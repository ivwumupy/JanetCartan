module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactPDO
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.GraphConvergence

/-!
# The exact compact-frequency principal normal

For the principal PDO in `app:ch_regular_base:eq:actual-pdo-remainder`, the
averaged-gradient chart of `x·η` is the identity on all frequencies. Its normal
is the product of the SAME principal symbol at two independent output positions.
The frequency cutoff is the existing expanding cutoff; no physical source
cutoff is introduced. The consumer is the finite spatial-jet normal estimate
and its cutoff removal in `app:ch_regular_base:eq:actual-right-inverse`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.WeightedPrincipalLocalization

open NormalComparison LowBounds LowBounds.FrequencyCutoff

variable {n r : ℕ}
local notation "E" => Euclidean n

private theorem fderiv_principal_linearPhase (u z : E) :
    fderiv ℝ (fun x : E ↦ inner ℝ x u) z = innerSL ℝ u := by
  simpa only [coe_innerSL_apply, real_inner_comm] using
    (innerSL ℝ u).hasFDerivAt.fderiv (x := z)

/-- The principal phase has the identity averaged-gradient map, including
the zero covector. Consumer: the exact normal in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
@[simp] theorem averagedGradient_principal_linearPhase (x y u : E) :
    averagedGradient (fun x u : E ↦ inner ℝ x u) x y u = u := by
  unfold averagedGradient averagedPhaseDifferential
  simp_rw [fderiv_principal_linearPhase]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply u

/-- The actual global chart for the principal PDO has unit determinant and
identity inverse. Consumer: the compact normal estimate in actual-calculus
Step 1, `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem principal_linearPhase_chart (K : Set E) :
    AveragedGradientChart (fun x u : E ↦ inner ℝ x u) K univ
      (fun _ _ ξ ↦ ξ) (fun _ _ _ ↦ ContinuousLinearMap.id ℝ E) 1 := by
  refine ⟨MeasurableSet.univ, zero_lt_one, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ y _ u _ t _
    simpa only [coe_innerSL_apply, real_inner_comm] using
      (innerSL ℝ u).differentiableAt (x := y + t • (x - y))
  · intro x _ y _ u _
    simp_rw [fderiv_principal_linearPhase]
    exact intervalIntegrable_const
  · intro x _ y _ u _
    have he : averagedGradient (fun x u : E ↦ inner ℝ x u) x y = id :=
      funext (averagedGradient_principal_linearPhase x y)
    rw [he]
    exact (hasFDerivAt_id (𝕜 := ℝ) u).hasFDerivWithinAt
  · intro x _ y _ u _ v _ huv
    simpa only [averagedGradient_principal_linearPhase] using huv
  · intro x _ y _ u _
    exact averagedGradient_principal_linearPhase x y u
  · intro x _ y _ u _
    change (1 : ℝ) ≤ |LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)|
    simp

/-- The literal principal compact normal, in the paired positions required
by `GraphNormalAmplitudeBounds`. Its frequency cutoff affects neither physical
position. Consumer: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
def principalCutoffNormalSymbol (a : FullAmplitude n r) (j : ℕ)
    (ξ : E) (z : Euclidean (2 * n)) : Matrix (Fin r) (Fin r) ℂ :=
  cutAmplitude (principalPhysicalAmplitude a) j (splitPhysicalPositions z).1
      ((2 * Real.pi) • ξ) *
    (cutAmplitude (principalPhysicalAmplitude a) j (splitPhysicalPositions z).2
      ((2 * Real.pi) • ξ)).conjTranspose

/-- The principal compact normal is the squared real frequency cutoff times
the two independent cycle symbols. This formula permits spatial differentiation
without any normalized-shell frequency hypothesis. Consumer: the finite-jet
bound in `app:ch_regular_base:eq:actual-pdo-remainder`. -/
theorem principalCutoffNormalSymbol_eq_cycle (a : FullAmplitude n r) (j : ℕ)
    (ξ : E) (z : Euclidean (2 * n)) :
    principalCutoffNormalSymbol a j ξ z =
      (cycleCutoff j ξ)^2 •
        (principalCycleSymbol a (splitPhysicalPositions z).1 ξ *
          (principalCycleSymbol a (splitPhysicalPositions z).2 ξ).conjTranspose) := by
  simp only [principalCutoffNormalSymbol, cutAmplitude, principalPhysicalAmplitude_cycle]
  change (cycleCutoff j ξ • principalCycleSymbol a (splitPhysicalPositions z).1 ξ) *
    (cycleCutoff j ξ • principalCycleSymbol a (splitPhysicalPositions z).2 ξ).conjTranspose = _
  simp only [Matrix.conjTranspose_smul, cycleCutoff_star, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, pow_two]

/-- The compact graph's existing cycle normal is exactly the displayed
principal normal. This closes the chart and normalization inputs of the
normal estimate in `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cycleCrossNormalSymbol_principal_cutoff (a : FullAmplitude n r) (j : ℕ) :
    cycleCrossNormalSymbol univ (fun x u : E ↦ inner ℝ x u)
      (cutAmplitude (principalPhysicalAmplitude a) j)
      (cutAmplitude (principalPhysicalAmplitude a) j)
      (fun _ _ ξ ↦ ξ) (fun _ _ _ ↦ ContinuousLinearMap.id ℝ E) =
      principalCutoffNormalSymbol a j := by
  funext ξ z
  have hdet : (ContinuousLinearMap.id ℝ E).det = 1 := LinearMap.det_id
  simp [cycleCrossNormalSymbol, cycleCrossNormalAmplitude, extendedCrossNormalAmplitude,
    crossNormalAmplitude, crossNormalNumerator, principalCutoffNormalSymbol, hdet]

end JanetCartan.FourierIntegral.WeightedPrincipalLocalization
