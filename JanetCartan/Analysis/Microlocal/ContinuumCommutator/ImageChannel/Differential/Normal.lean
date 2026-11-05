module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Commutators
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Factorization

/-!
# Exact higher commutators of the actual image normal

The finite expression below is identified with the published
`imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint`.
The resulting constructed `H^s → L²` commutators supply exactly the weak
identity used by `HigherRegularity.mem_succ_of_commutators`. Both masks, both
normal factors, every connection coefficient and the actual adjoint signs
are retained (`app:ch_background:eq:bg-commutator`).

The quantitative single-high estimate for these same constructed maps is
proved from primitive coefficient jets in `TameEstimates.lean`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace ContinuumRow ImageFactorExpression

/-- Coefficient slots retain every reduced coefficient and the two fixed masks
(`app:ch_background:eq:bg-commutator`). The Boolean slots are measurement
(`false`) and source (`true`). -/
abbrev ImageCoefficientSlot (n : ℕ) := GeometricProfile.ReducedCoefficientIndex n ⊕ Bool

/-- The original coefficients and masks in the finite expression, with no
replacement of the published image channel (`app:ch_background:eq:bg-commutator`). -/
def imageFactorCoefficients {n : ℕ}
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) : ImageCoefficientSlot n → C(Torus n, ℝ)
  | .inl a => c a
  | .inr false => χmeas
  | .inr true => χsrc

/-- Smoothness of the same primitive coefficients and fixed masks suffices
for all finite Sobolev actions (`app:ch_background:prop:bg-inverse`). -/
theorem smooth_imageFactorCoefficients {n : ℕ}
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc : C(Torus n, ℝ))
    (hχmeas : IsSmoothPeriodic χmeas) (hχsrc : IsSmoothPeriodic χsrc) :
    ∀ a, IsSmoothPeriodic (imageFactorCoefficients c χmeas χsrc a)
  | .inl a => hc a
  | .inr false => hχmeas
  | .inr true => hχsrc

/-- The literal forward finite factors, including source and measurement masks
and both first- and zeroth-order coefficient terms
(`app:ch_background:eq:bg-commutator`). -/
def imageForwardExpression (n : ℕ) : ImageFactorExpression n (ImageCoefficientSlot n) :=
  .comp (.comp (.coefficient (.inr false) [])
    (.add
      (finSum fun a : Fin n ↦ finSum fun i : Fin n ↦ finSum fun k : Fin n ↦
        .comp (.comp (.matrixUnit i k) (.coefficient (.inl (.inl (a, i, k))) []))
          (.derivativeBessel a))
      (finSum fun i : Fin n ↦ finSum fun k : Fin n ↦
        .comp (.comp (.matrixUnit i k) (.coefficient (.inl (.inr (i, k))) []))
          .bessel)))
    (.coefficient (.inr true) [])

/-- The actual Hilbert-adjoint factors in their reversed order, including the
minus sign on `Dᵢ J` (`app:ch_background:eq:bg-commutator`). -/
def imageAdjointExpression (n : ℕ) : ImageFactorExpression n (ImageCoefficientSlot n) :=
  .comp (.comp (.coefficient (.inr true) [])
    (.add
      (finSum fun a : Fin n ↦ finSum fun i : Fin n ↦ finSum fun k : Fin n ↦
        .comp (.neg (.derivativeBessel a))
          (.comp (.matrixUnit k i) (.coefficient (.inl (.inl (a, i, k))) [])))
      (finSum fun i : Fin n ↦ finSum fun k : Fin n ↦
        .comp .bessel (.comp (.matrixUnit k i) (.coefficient (.inl (.inr (i, k))) [])))))
    (.coefficient (.inr false) [])

variable {n : ℕ}
variable (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
variable (hc : ∀ a, IsSmoothPeriodic (c a))
variable (χmeas χsrc : C(Torus n, ℝ))
variable (hχmeas : IsSmoothPeriodic χmeas) (hχsrc : IsSmoothPeriodic χsrc)

/-- Interpretation of the forward expression is exactly the already published
image channel (`app:ch_background:eq:bg-commutator`). -/
theorem onL2_imageForwardExpression :
    (imageForwardExpression n).onL2 (imageFactorCoefficients c χmeas χsrc)
      (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc) =
        imageChannel c χmeas χsrc := by
  rw [imageChannel_eq_finiteFactors]
  simp only [imageForwardExpression, onL2, onL2_finSum, imageFactorCoefficients,
    orderedCoefficient, periodicCoordinateDerivList, reducedCoefficientMultiplier]
  rfl

/-- Interpretation of the reversed expression is the literal adjoint of the
same image channel (`app:ch_background:eq:bg-commutator`). -/
theorem onL2_imageAdjointExpression :
    (imageAdjointExpression n).onL2 (imageFactorCoefficients c χmeas χsrc)
      (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc) =
        (imageChannel c χmeas χsrc).adjoint := by
  rw [imageChannel_adjoint_eq_finiteFactors]
  simp only [imageAdjointExpression, onL2, onL2_finSum, imageFactorCoefficients,
    orderedCoefficient, periodicCoordinateDerivList, reducedCoefficientMultiplier]
  rfl

/-- The constructed commutator for the actual image normal. Its source is
`H^s` although the word may have length `s+1`; every branch contains a
coefficient derivative (`app:ch_background:eq:bg-commutator`). -/
def imageNormalCommutator (s : ℕ) (is : List (Fin n)) (hlen : is.length ≤ s + 1) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ] OutputL2 n :=
  (ImageFactorExpression.comp (imageForwardExpression n) (imageAdjointExpression n)).commutator
    (imageFactorCoefficients c χmeas χsrc)
    (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc) s is hlen

/-- Exact `hK` for the literal `A.comp A.adjoint`, on every smooth periodic
field and every word of length at most `s+1`. This is the identity consumed by
`HigherRegularity.mem_succ_of_commutators` and
`HigherRegularity.gradeNorm_succ_le_of_commutators`
(`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`). -/
theorem hasWeakDerivativeList_imageNormalCommutator (s : ℕ) (is : List (Fin n))
    (hlen : is.length ≤ s + 1) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    HasPeriodicWeakDerivativeList is
      ((imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint)
        (toL2 s (ofSmooth s f hf)))
      ((imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint)
        (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) +
          imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen (ofSmooth s f hf)) := by
  have h := (ImageFactorExpression.comp (imageForwardExpression n)
    (imageAdjointExpression n)).hasWeakDerivativeList_commutator
      (imageFactorCoefficients c χmeas χsrc)
      (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc) s is hlen f hf
  simpa only [onL2, onL2_imageForwardExpression c hc χmeas χsrc hχmeas hχsrc,
    onL2_imageAdjointExpression c hc χmeas χsrc hχmeas hχsrc,
    imageNormalCommutator] using h

include hc hχmeas hχsrc in
/-- The exact existential `K/hK` input of the generic higher-regularity theorem,
constructed from primitive smooth coefficients and the two fixed masks.
This endpoint asserts the weak identity; `TameEstimates` adds the single-high bound
(`app:ch_background:prop:bg-inverse`). -/
theorem exists_imageNormal_commutators (s : ℕ) :
    ∃ K : (is : List (Fin n)) → is.length = s + 1 →
        PeriodicSobolevSpace n (Euclidean n) s →L[ℝ] OutputL2 n,
      ∀ (is : List (Fin n)) (hlen : is.length = s + 1)
        (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f),
        HasPeriodicWeakDerivativeList is
          ((imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint)
            (toL2 s (ofSmooth s f hf)))
          ((imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint)
            (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) +
              K is hlen (ofSmooth s f hf)) :=
  ⟨fun is hlen ↦ imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen.le,
    fun is hlen f hf ↦
      hasWeakDerivativeList_imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen.le f hf⟩

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
