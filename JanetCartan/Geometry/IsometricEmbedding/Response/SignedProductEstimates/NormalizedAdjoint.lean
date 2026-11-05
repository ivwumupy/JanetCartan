module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedMask

/-!
# The literal adjoint of the corrected source discrepancy

Adjunction reverses the existing position masks. On the original supported
source their own plateaux leave the SAME complementary Fourier operator,
with the original input mask on its left. Consumer: the backward angular
source contribution in `resolved-angular-tail` and the signed residual chains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open FourierIntegral.LowBounds
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure E)

/-- Absorption uses only the original mask's plateau on the datum
(`app:ch_regular:eq:resolved-angular-tail`). -/
private theorem supported_source_cut_eq
    (χ : E → ℝ) (hc : Continuous χ) (hb : ∀ y, ‖χ y‖ ≤ 1)
    (u : H) (hu : ∀ᵐ y ∂volume, u y ≠ 0 → χ y = 1) :
    sourceCutMultiplier χ hc hb u = u := by
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn χ hc hb u, hu] with y hy hu
  by_cases hz : u y = 0
  · simp [hy, hz]
  · simp [hy, hu hz]

/-- The actual corrected adjoint discrepancy keeps its reversed original
physical masks and unchanged complementary Fourier symbol. No order-zero
source defect is assigned a smoothing gain (`measured-adjoint`,
`app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedSource_adjoint_sub_identity_eq_complement
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    {L₀ : ℝ} (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (u : H) (hu : ∀ᵐ y ∂volume, u y ≠ 0 → y ∈ closedBall center f.physicalRadius)
    (hop : ∀ᵐ y ∂volume, u y ≠ 0 → output y = 1) :
    ((pairedSource f hK L₀ output ho hob).adjoint - 1) u =
      -sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous
        (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)
        (complementFourierOperator f hK L₀ u) := by
  let Mo := sourceCutMultiplier (r := d+1) f.outputMask f.outputMask_smooth.continuous
    (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)
  let Mi := sourceCutMultiplier (r := d+1) f.inputMask f.inputMask_smooth.continuous
    (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)
  let Mc := sourceCutMultiplier (r := d+1) output ho hob
  have hi : Mi u = u := supported_source_cut_eq _ _ _ u (by
    filter_upwards [hu] with y hy hz
    exact interior_subset (s := {z | f.inputMask z = 1})
      (f.inputMask_plateau ((closedBall_subset_closedBall
        (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 2*f.physicalRadius)) (hy hz))))
  have hmo : Mo u = u := supported_source_cut_eq _ _ _ u (by
    filter_upwards [hu] with y hy hz
    exact interior_subset (s := {z | f.outputMask z = 1}) (f.outputMask_plateau (hy hz)))
  have hmc : Mc u = u := supported_source_cut_eq _ _ _ u hop
  rw [pairedSource_adjoint_eq_fourier_composition f hK hL₀ output ho hob]
  change Mi (sourceFourierOperator f hK L₀ (Mo (Mc u))) - u =
    -Mi (complementFourierOperator f hK L₀ u)
  rw [hmc, hmo]
  calc
    _ = Mi (sourceFourierOperator f hK L₀ u - u) := by rw [map_sub, hi]
    _ = _ := by
      have he := congrArg (fun T : H →L[ℂ] H ↦ T u) (sourceFourierOperator_sub_identity f hK L₀)
      change sourceFourierOperator f hK L₀ u - u = -complementFourierOperator f hK L₀ u at he
      rw [he, map_neg]

end JanetCartan.SignedProductEstimates
