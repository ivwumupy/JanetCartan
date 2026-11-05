module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.OrderedDerivatives

/-!
# Differentiating the finite image factors

A finite expression records only the actual coefficient multipliers, constant
matrix units and Bessel factors of `imageNormal_eq_finiteFactors`. Its Sobolev
actions and Leibniz rule are constructed from the proved actions of these
factors. This is the algebraic input to the image-normal commutator in
`app:ch_background:eq:bg-commutator`; it is not an assumed normal interface.
Coefficient slots retain their original index and the exact derivative word,
so quantitative estimates can recover the primitive coefficient jets.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace ContinuumRow

/-- Finite expressions in the literal image factors, retaining coefficient
indices and derivative words (`app:ch_background:eq:bg-commutator`). -/
inductive ImageFactorExpression (n : ℕ) (ι : Type*) where
  | zero
  | coefficient (a : ι) (js : List (Fin n))
  | matrixUnit (i k : Fin n)
  | bessel
  | derivativeBessel (i : Fin n)
  | add (e f : ImageFactorExpression n ι)
  | neg (e : ImageFactorExpression n ι)
  | comp (e f : ImageFactorExpression n ι)

namespace ImageFactorExpression

variable {n : ℕ} {ι : Type*}
variable (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))

/-- Interpretation using the published L² factors, including actual coefficient
jets (`app:ch_background:eq:bg-commutator`). -/
def onL2 : ImageFactorExpression n ι → (OutputL2 n →L[ℝ] OutputL2 n)
  | .zero => 0
  | .coefficient a js => cutoffMultiplier (orderedCoefficient (q a) (hq a) js)
  | .matrixUnit i k => (reducedMatrixUnit i k).compLpL 2 MeasureTheory.volume
  | .bessel => periodicBesselInverse
  | .derivativeBessel i => Differential.derivativeBessel i
  | .add e f => onL2 e + onL2 f
  | .neg e => -onL2 e
  | .comp e f => onL2 e ∘L onL2 f

/-- Constructed actions of the finite factors at every Sobolev order. No action
or regularity assertion is an input (`app:ch_background:prop:bg-inverse`). -/
def onSobolev (s : ℕ) : ImageFactorExpression n ι →
    (PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s)
  | .zero => 0
  | .coefficient a js => cutoffSobolev (orderedCoefficient (q a) (hq a) js)
      ((hq a).coordinateDerivList js) s
  | .matrixUnit i k => matrixUnitSobolev s i k
  | .bessel => besselSobolev s
  | .derivativeBessel i => derivativeBesselSobolev s i
  | .add e f => onSobolev s e + onSobolev s f
  | .neg e => -onSobolev s e
  | .comp e f => onSobolev s e ∘L onSobolev s f

/-- Every expression acts on the same underlying L² datum at all orders
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_onSobolev (e : ImageFactorExpression n ι) (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (e.onSobolev q hq s u) = e.onL2 q hq (toL2 s u) := by
  induction e generalizing u with
  | zero => simp [onSobolev, onL2]
  | coefficient a js => exact toL2_cutoffSobolev _ _ _ _
  | matrixUnit i k => exact toL2_matrixUnitSobolev _ _ _ _
  | bessel => exact toL2_besselSobolev _ _
  | derivativeBessel i => exact toL2_derivativeBesselSobolev _ _ _
  | add e f he hf => simp only [onSobolev, onL2, add_apply,
      map_add, he, hf]
  | neg e he => simp only [onSobolev, onL2, neg_apply, map_neg, he]
  | comp e f he hf => simp only [onSobolev, onL2, ContinuousLinearMap.comp_apply,
      he, hf]

/-- All finite actions commute with the original Sobolev inclusions
(`app:ch_background:eq:bg-commutator`). -/
theorem inclusion_onSobolev (e : ImageFactorExpression n ι) {s t : ℕ}
    (h : s ≤ t) (u : PeriodicSobolevSpace n (Euclidean n) t) :
    inclusion h (e.onSobolev q hq t u) = e.onSobolev q hq s (inclusion h u) := by
  apply toL2_injective s
  simp only [multiplier_toL2_inclusion, toL2_onSobolev]

/-- The coefficient part of differentiation. Constant Fourier and matrix
factors contribute zero; composition uses the full Leibniz rule
(`app:ch_background:eq:bg-commutator`). -/
def coefficientDerivative (i : Fin n) : ImageFactorExpression n ι → ImageFactorExpression n ι
  | .zero => .zero
  | .coefficient a js => .coefficient a (i :: js)
  | .matrixUnit _ _ => .zero
  | .bessel => .zero
  | .derivativeBessel _ => .zero
  | .add e f => .add (coefficientDerivative i e) (coefficientDerivative i f)
  | .neg e => .neg (coefficientDerivative i e)
  | .comp e f => .add (.comp (coefficientDerivative i e) f)
      (.comp e (coefficientDerivative i f))

/-- The exact coordinate Leibniz identity for each finite expression on all
Sobolev data, proved from its actual factors
(`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivative_onSobolev (e : ImageFactorExpression n ι) (s : ℕ)
    (i : Fin n) (u : PeriodicSobolevSpace n (Euclidean n) (s + 1)) :
    coordinateDerivative s i (e.onSobolev q hq (s + 1) u) =
      (e.coefficientDerivative i).onSobolev q hq s (inclusion (Nat.le_succ s) u) +
        e.onSobolev q hq s (coordinateDerivative s i u) := by
  induction e generalizing u with
  | zero => simp [onSobolev, coefficientDerivative]
  | coefficient a js =>
    exact coordinateDerivative_cutoffSobolev _ _ _ _ _
  | matrixUnit j k =>
    simpa only [coefficientDerivative, onSobolev, zero_apply,
      zero_add] using coordinateDerivative_matrixUnitSobolev s i j k u
  | bessel =>
    simpa only [coefficientDerivative, onSobolev, zero_apply,
      zero_add] using coordinateDerivative_besselSobolev s i u
  | derivativeBessel j =>
    simpa only [coefficientDerivative, onSobolev, zero_apply,
      zero_add] using coordinateDerivative_derivativeBesselSobolev s i j u
  | add e f he hf =>
    simp only [coefficientDerivative, onSobolev, add_apply,
      map_add, he, hf]
    abel
  | neg e he =>
    simp only [coefficientDerivative, onSobolev, neg_apply,
      map_neg, he, neg_add]
  | comp e f he hf =>
    simp only [coefficientDerivative, onSobolev, add_apply,
      ContinuousLinearMap.comp_apply, he, hf, inclusion_onSobolev, map_add]
    abel

/-- A finite sum of factors, without imposing algebraic relations on their
syntax (`app:ch_background:eq:bg-commutator`). -/
def finSum {m : ℕ} (f : Fin m → ImageFactorExpression n ι) : ImageFactorExpression n ι :=
  (List.ofFn f).foldr ImageFactorExpression.add ImageFactorExpression.zero

/-- Interpretation of a finite factor sum is the actual sum of L² operators
(`app:ch_background:eq:bg-commutator`). -/
theorem onL2_finSum {m : ℕ} (f : Fin m → ImageFactorExpression n ι) :
    (finSum f).onL2 q hq = ∑ i, (f i).onL2 q hq := by
  have h (l : List (ImageFactorExpression n ι)) :
      (l.foldr ImageFactorExpression.add ImageFactorExpression.zero).onL2 q hq = (l.map (onL2 q hq)).sum := by
    induction l with
    | nil => rfl
    | cons e l ih => simp only [List.foldr_cons, onL2, ih, List.map_cons, List.sum_cons]
  rw [finSum, h, List.map_ofFn, List.sum_ofFn]
  rfl

end ImageFactorExpression
end JanetCartan.ContinuumCommutator.ImageChannel.Differential
