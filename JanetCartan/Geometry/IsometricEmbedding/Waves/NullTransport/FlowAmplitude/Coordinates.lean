module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Reduction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Regularity
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Coordinates for the supplied-flow amplitude

The derivative bridge used by `FlowAmplitude.exists_positive_null_amplitude_of_flow`
in `app:ch_waves:thm:leading`. Carrier parameters are kept separate from the
Euclidean variables differentiated by the literal reduced operator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.FlowAmplitude

variable {n N : ℕ} {X Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Adapted space-time coordinates, leaving carrier parameters unchanged
(`app:ch_waves:thm:leading`). The time-coordinate identity is supplied separately. -/
def coordinates (e : Euclidean n ≃L[ℝ] (ℝ × X)) :
    (Euclidean n × Z) ≃L[ℝ] (ℝ × (X × Z)) :=
  (e.prodCongr (ContinuousLinearEquiv.refl ℝ Z)).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ℝ X Z)

/-- Explicit forward space-time and carrier identification
(`app:ch_waves:thm:leading`). -/
@[simp] theorem coordinates_apply (e : Euclidean n ≃L[ℝ] (ℝ × X))
    (w : Euclidean n × Z) : coordinates e w = ((e w.1).1, (e w.1).2, w.2) := rfl

/-- Explicit inverse space-time and carrier identification
(`app:ch_waves:thm:leading`). -/
@[simp] theorem coordinates_symm_apply (e : Euclidean n ≃L[ℝ] (ℝ × X))
    (q : ℝ × (X × Z)) : (coordinates e).symm q = (e.symm (q.1, q.2.1), q.2.2) := rfl

/-- The raw geometric data for `app:ch_waves:thm:leading`. These are functions
and fixed indices only; in particular this record contains no transport solution. -/
structure Geometry (n N : ℕ) (Z : Type*) where
  immersion : Z → Euclidean n → Euclidean N
  frame : Z → Euclidean n → Fin n → MetricTensor n
  covector : Z → Euclidean n → Euclidean n
  row : Fin n
  col : Fin n
  time : Fin n

namespace Geometry

variable (g : Geometry n N Z)

/-- The literal characteristic matrix, at fixed carrier (`app:ch_waves:eq:reduced-symbol`). -/
def symbol (w : Euclidean n × Z) : MetricTensor n :=
  reducedSymbol (g.frame w.2 w.1) (g.covector w.2 w.1)

/-- Fixed adjugate column, with the shared Euclidean norm (`app:ch_waves:thm:leading`). -/
def kernel (w : Euclidean n × Z) : Euclidean n :=
  WithLp.toLp 2 (rightNullvector (g.symbol w) g.col)

/-- Fixed adjugate row (`app:ch_waves:thm:leading`). -/
def dual (w : Euclidean n × Z) : Fin n → ℝ :=
  leftNullvector (g.symbol w) g.row

/-- The actual time coefficient before division (`app:ch_waves:thm:leading`). -/
def timeCoefficient (w : Euclidean n × Z) : ℝ :=
  transportField (g.frame w.2 w.1) (g.dual w) (fun j ↦ g.kernel w j) g.time

/-- The actual normalized principal direction (`app:ch_waves:thm:leading`). -/
def direction (w : Euclidean n × Z) : Euclidean n :=
  WithLp.toLp 2 (fun a ↦
    transportField (g.frame w.2 w.1) (g.dual w) (fun j ↦ g.kernel w j) a /
      g.timeCoefficient w)

/-- The actual normalized zero-order term, retaining the connection and holding
carrier parameters fixed during differentiation (`app:ch_waves:thm:leading`). -/
def coefficient (w : Euclidean n × Z) : ℝ :=
  (g.dual w ⬝ᵥ reducedOperator (g.immersion w.2) (g.frame w.2)
    (fun x ↦ g.kernel (x, w.2)) w.1) / g.timeCoefficient w

/-- Smooth matrix entries give joint smoothness of the fixed column, used for
`b = α k` in `app:ch_waves:thm:leading`. -/
theorem contDiffOn_kernel {Ω : Set (Euclidean n × Z)}
    (hQ : ∀ i j a, ContDiffOn ℝ ∞ (fun w ↦ g.frame w.2 w.1 i j a) Ω)
    (hξ : ∀ a, ContDiffOn ℝ ∞ (fun w ↦ g.covector w.2 w.1 a) Ω) :
    ContDiffOn ℝ ∞ g.kernel Ω := by
  apply (contDiffOn_piLp 2).2
  intro i
  apply contDiffOn_adjugate_entry (A := g.symbol) _ i g.col
  intro j a
  change ContDiffOn ℝ ∞ (fun w ↦ ∑ b, g.frame w.2 w.1 j a b *
    g.covector w.2 w.1 b) Ω
  exact ContDiffOn.sum (fun b _ ↦ (hQ j a b).mul (hξ b))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- A fixed minor and a simple time root justify the division in the actual
transport field (`app:ch_waves:thm:leading`). -/
theorem timeCoefficient_ne_zero {w : Euclidean n × Z}
    (hQ : ∀ i, (g.frame w.2 w.1 i).IsSymm)
    (hchar : (g.symbol w).det = 0)
    (hminor : (g.symbol w).adjugate g.row g.col ≠ 0)
    (hroot : partialDeriv (reducedDeterminant (g.frame w.2 w.1))
      (g.covector w.2 w.1) g.time ≠ 0) : g.timeCoefficient w ≠ 0 :=
  transportField_time_ne_zero _ hQ _ hchar hminor hroot

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The normalized direction has unit time component; this is what identifies
the geometric derivative with the supplied flow derivative (`app:ch_waves:thm:leading`). -/
theorem direction_time {w : Euclidean n × Z} (ht : g.timeCoefficient w ≠ 0) :
    g.direction w g.time = 1 := div_self ht

end Geometry

/-- The chain rule and the Euclidean basis expansion identify the scalar PDE
with the derivative along the adapted flow, while freezing the carrier.
Consumed by `exists_positive_null_amplitude_of_flow` (`app:ch_waves:thm:leading`). -/
theorem directional_derivative_coordinates
    (e : Euclidean n ≃L[ℝ] (ℝ × X)) {u : ℝ × (X × Z) → ℝ}
    {w : Euclidean n × Z} (hu : DifferentiableAt ℝ u (coordinates e w))
    (v : Euclidean n) :
    (∑ a, v a * partialDeriv (fun x ↦ u (coordinates e (x, w.2))) w.1 a) =
      fderiv ℝ u (coordinates e w) ((e v).1, (e v).2, 0) := by
  have hi : HasFDerivAt (fun x : Euclidean n ↦ (x, w.2))
      ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0) w.1 :=
    (hasFDerivAt_id w.1).prodMk (hasFDerivAt_const w.2 w.1)
  let L : Euclidean n →L[ℝ] (ℝ × (X × Z)) :=
    (coordinates (Z := Z) e).toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0)
  have hj : HasFDerivAt (fun x ↦ coordinates e (x, w.2)) L w.1 :=
    (coordinates (Z := Z) e).hasFDerivAt.comp w.1 hi
  have hd : HasFDerivAt (fun x ↦ u (coordinates e (x, w.2)))
      ((fderiv ℝ u (coordinates e w)).comp L) w.1 := hu.hasFDerivAt.comp w.1 hj
  have hs : (∑ a, v a * partialDeriv
      (fun x ↦ u (coordinates e (x, w.2))) w.1 a) =
      fderiv ℝ (fun x ↦ u (coordinates e (x, w.2))) w.1 v := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
      congrArg (fderiv ℝ (fun x ↦ u (coordinates e (x, w.2))) w.1)
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  rw [hs, hd.fderiv]
  rfl

end JanetCartan.NullTransport.FlowAmplitude
