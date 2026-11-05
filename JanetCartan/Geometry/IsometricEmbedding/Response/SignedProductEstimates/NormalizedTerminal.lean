module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompleteSourcePlateau
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.SourceComplement
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencyLocalization

/-!
# The actual normalized source on the protected terminal localizer

Apply the corrected source's own plateau to the original right quantization.
The source's `2*L₀` collar remains fixed. Exact Fourier cancellation above
`4*L₀/lo` leaves all three original physical tails, including their literal
adjoint order. The angular input is terminal coverage by the same selector
compact, not a desired plateau or decay hypothesis. Consumer:
`finiteChain_observation_rapidDecayAt.hBnear` (`resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ C : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure E)

/-- The corrected same-family Fourier source fixes the original right
localizer above the unchanged low collar. Terminal coverage is supplied by
`exists_primitive_signed_complete_source_terminal_cover`; the normalized
plateau is derived internally (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedSourceFourier_comp_rightLocalizer_eq
    (f : ActualMaskFamily Ω center RQ A₀ K C) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) {L₀ lo ρ : ℝ}
    (hL₀ : 0 < L₀) (hlo : 0 < lo) (hρ : 4*L₀/lo < ρ)
    (mi : LocalizerSymbol (d+1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K) :
    (sourceFourierOperator f hK L₀).comp M.adjoint = M.adjoint := by
  obtain ⟨V, _, hKV, _, hplateau⟩ :=
    exists_normalizedSourceMask_partition_near f hK (Subset.rfl : K ⊆ K) hsym
  apply scalarPhysicalFrequencyOperator_comp_rightLocalizer_eq ρ mi M hM
    (normalizedSourceMask f hK L₀) (normalizedSourceMask_properties f hK L₀).1.continuous
    (fun ξ ↦ (Real.norm_of_nonneg ((normalizedSourceMask_properties f hK L₀).2 ξ).1).trans_le
      ((normalizedSourceMask_properties f hK L₀).2 ξ).2)
    (hasTemperateGrowth_complex_dilatedConicMask (contDiff_gammaTotal f hK) (2*L₀))
  intro x ξ hmi
  have hp : (x, ρ⁻¹ • ξ) ∈ tsupport mi := subset_tsupport mi hmi
  have hρpos : 0 < ρ := (div_pos (by positivity) hlo).trans hρ
  have hhigh : 4*L₀ ≤ ‖ξ‖ := by
    have hmul := mul_le_mul_of_nonneg_left (hann _ hp) hρpos.le
    have he : ρ * ‖ρ⁻¹ • ξ‖ = ‖ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρpos.le),
        ← mul_assoc, mul_inv_cancel₀ hρpos.ne', one_mul]
    rw [he] at hmul
    exact (((div_lt_iff₀ hlo).mp hρ).trans_le hmul).le
  have hdir : NormedSpace.normalize ξ ∈ V := by
    apply hKV
    simpa only [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hρpos)] using hterminal _ hp
  exact (hplateau L₀ hL₀ ξ hdir).2 hhigh

/-- Exact three-tail expansion of the corrected source minus ONE identity,
forward and for its literal adjoint. The input mask stays before the Fourier
factor; the extra output mask and original output mask both remain. This is
the actual terminal input to `app:ch_regular:eq:chain-tail`. -/
theorem normalizedSource_comp_rightLocalizer_eq_physical_tails
    (f : ActualMaskFamily Ω center RQ A₀ K C) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) {L₀ lo ρ : ℝ}
    (hL₀ : f.radialThreshold ≤ L₀) (hlo : 0 < lo) (hρ : 4*L₀/lo < ρ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (mi : LocalizerSymbol (d+1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K) :
    let Mc := sourceCutMultiplier (r := d+1) output ho hob
    let Mo := sourceCutMultiplier (r := d+1) f.outputMask f.outputMask_smooth.continuous
      (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)
    let Mi := sourceCutMultiplier (r := d+1) f.inputMask f.inputMask_smooth.continuous
      (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)
    let F := sourceFourierOperator f hK L₀
    let P := pairedSource f hK L₀ output ho hob
    ∀ u : H,
      ((P-1).comp M.adjoint) u =
        Mc (Mo (F ((Mi-1) (M.adjoint u)))) + Mc ((Mo-1) (M.adjoint u)) + (Mc-1) (M.adjoint u) ∧
      ((P.adjoint-1).comp M.adjoint) u =
        Mi (F (Mo ((Mc-1) (M.adjoint u)))) + Mi (F ((Mo-1) (M.adjoint u))) + (Mi-1) (M.adjoint u) := by
  intro Mc Mo Mi F P u
  have hfreq : F (M.adjoint u) = M.adjoint u :=
    DFunLike.congr_fun (normalizedSourceFourier_comp_rightLocalizer_eq f hK hsym
      (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans hL₀)) hlo hρ mi M hM hann hterminal) u
  have hf : P = Mc.comp (Mo.comp (F.comp Mi)) :=
    pairedSource_eq_fourier_composition f hK hL₀ output ho hob
  have ha : P.adjoint = Mi.comp (F.comp (Mo.comp Mc)) :=
    pairedSource_adjoint_eq_fourier_composition f hK hL₀ output ho hob
  constructor
  · rw [hf]
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub, hfreq]
    abel
  · rw [ha]
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub, hfreq]
    abel

end JanetCartan.SignedProductEstimates
