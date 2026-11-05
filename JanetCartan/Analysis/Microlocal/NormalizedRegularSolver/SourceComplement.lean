module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.SourceIdentity

/-!
# The exact complementary normalized Fourier operator

The source discrepancy has symbol `D gammaTotal - 1`. On data supported in
the original measurement core, the physical input mask is absorbed by its
actual plateau, and the two output masks remain outside the complementary
Fourier operator. Consumer: `resolved-angular-tail`, signed source localization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory FourierTransform
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks.ActualFamily Characteristic.EvolutionIntegral FourierIntegral.LowBounds
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The genuine complementary Fourier operator with scalar mask
`1-D gammaTotal`, including the unchanged low shoulder (`resolved-angular-tail`). -/
def complementFourierOperator (L : ℝ) : H →L[ℂ] H :=
  scalarPhysicalFrequencyOperator (normalizedComplementMask f hK L)
    (normalizedComplementMask_properties f hK L).1.continuous
    (fun ξ ↦ (Real.norm_of_nonneg ((normalizedComplementMask_properties f hK L).2.1 ξ).1).trans_le
      ((normalizedComplementMask_properties f hK L).2.1 ξ).2)

/-- Literal Fourier representative of the complete complementary source
mask, with the same physical frequency convention (`resolved-angular-tail`). -/
theorem complementFourierOperator_fourier_ae (L : ℝ) (u : H) :
    (𝓕 (complementFourierOperator f hK L u) : H) =ᵐ[volume]
      fun ξ ↦ (normalizedComplementMask f hK L ((2*Real.pi) • ξ) : ℂ) • (𝓕 u : H) ξ := by
  simp only [complementFourierOperator, scalarPhysicalFrequencyOperator,
    ContinuousLinearMap.comp_apply, fourierInvCLM_apply, fourierCLM_apply, fourier_fourierInv_eq]
  exact sourceCutMultiplier_coeFn _ _ _ _

/-- The exact full source subtracts ONE identity and leaves precisely its
complement, without any source-support or high-frequency premise
(`resolved-angular-tail`, `prop:complete-residual`). -/
theorem sourceFourierOperator_sub_identity (L : ℝ) :
    sourceFourierOperator f hK L - 1 = -complementFourierOperator f hK L := by
  ext1 u
  apply (Lp.fourierTransformₗᵢ E V).injective
  simp only [sub_apply, neg_apply, one_apply_eq_self, map_sub, map_neg]
  change (𝓕 (sourceFourierOperator f hK L u) - 𝓕 u : H) =
    -𝓕 (complementFourierOperator f hK L u)
  apply Lp.ext
  filter_upwards [sourceFourierOperator_fourier_ae f hK L u,
    complementFourierOperator_fourier_ae f hK L u,
    Lp.coeFn_sub (𝓕 (sourceFourierOperator f hK L u)) (𝓕 u),
    Lp.coeFn_neg (𝓕 (complementFourierOperator f hK L u))] with ξ hs hc hd hn
  rw [hd, Pi.sub_apply, hs, hn, Pi.neg_apply, hc]
  simp only [normalizedComplementMask, Complex.ofReal_sub, Complex.ofReal_one,
    sub_smul, one_smul, neg_sub]

/-- Absorb a physical source mask only using its actual support plateau
(`app:ch_pairs:prop:pairs-lag-sum`). -/
private theorem sourceCutMultiplier_fixes_supported
    (χ : E → ℝ) (hc : Continuous χ) (hb : ∀ y, ‖χ y‖ ≤ 1)
    (u : H) (hu : ∀ᵐ y ∂volume, u y ≠ 0 → χ y = 1) :
    sourceCutMultiplier χ hc hb u = u := by
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn χ hc hb u, hu] with y hy hu
  by_cases hz : u y = 0
  · simp [hy, hz]
  · simp [hy, hu hz]

/-- On the original supported source, the normalized physical discrepancy
is the negative complementary Fourier operator with both actual output
masks. The original input mask is removed only by its own proved plateau.
Consumer: the signed source tail (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem pairedSource_sub_identity_eq_complement {L : ℝ} (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (u : H) (hu : ∀ᵐ y ∂volume, u y ≠ 0 → y ∈ Metric.closedBall x f.physicalRadius)
    (hop : ∀ᵐ y ∂volume, u y ≠ 0 → output y = 1) :
    (pairedSource f hK L output ho hob - 1) u =
      -sourceCutMultiplier output ho hob
        (sourceCutMultiplier f.outputMask f.outputMask_smooth.continuous
          (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)
          (complementFourierOperator f hK L u)) := by
  let Mo := sourceCutMultiplier (r := d+1) f.outputMask f.outputMask_smooth.continuous
    (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)
  let Mi := sourceCutMultiplier (r := d+1) f.inputMask f.inputMask_smooth.continuous
    (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)
  let Mc := sourceCutMultiplier (r := d+1) output ho hob
  have hi : Mi u = u := sourceCutMultiplier_fixes_supported _ _ _ u (by
    filter_upwards [hu] with y hy hz
    exact interior_subset (s := {z | f.inputMask z = 1})
      (f.inputMask_plateau ((Metric.closedBall_subset_closedBall
        (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 2*f.physicalRadius)) (hy hz))))
  have hmo : Mo u = u := sourceCutMultiplier_fixes_supported _ _ _ u (by
    filter_upwards [hu] with y hy hz
    exact interior_subset (s := {z | f.outputMask z = 1}) (f.outputMask_plateau (hy hz)))
  have hmc : Mc u = u := sourceCutMultiplier_fixes_supported _ _ _ u hop
  rw [pairedSource_eq_fourier_composition f hK hL output ho hob]
  change Mc (Mo (sourceFourierOperator f hK L (Mi u))) - u =
    -Mc (Mo (complementFourierOperator f hK L u))
  rw [hi]
  calc
    _ = Mc (Mo (sourceFourierOperator f hK L u - u)) := by rw [map_sub, map_sub, hmo, hmc]
    _ = _ := by
      have he := congrArg (fun T : H →L[ℂ] H ↦ T u) (sourceFourierOperator_sub_identity f hK L)
      change sourceFourierOperator f hK L u - u = -complementFourierOperator f hK L u at he
      rw [he, map_neg, map_neg]

end JanetCartan.RegularSector.NormalizedSolver
