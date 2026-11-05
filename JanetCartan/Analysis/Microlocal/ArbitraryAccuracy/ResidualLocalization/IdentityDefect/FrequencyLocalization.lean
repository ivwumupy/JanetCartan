module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.ActualTerminal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness

/-!
# Exact frequency cancellation on the right physical localizer

The right quantization has its symbol's exact Fourier support, even though it
has physical tails. The original angular multiplier therefore fixes it once
the annulus lies above the fixed low-frequency modification. This does not
discard either original physical mask. Consumer: the terminal estimate
`app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform Filter Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral LowBounds LowBounds.FrequencyCutoff FiniteChain.Graph KernelLimits
open RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open EvolutionIntegratedLocalization

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The physical Fourier transform of the original scalar multiplier is
literal multiplication by its physical symbol, with the `2π` factors
cancelling exactly (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem channelFourierTransform_physicalMultiplier
    (b : E → ℝ) (ht : (fun ξ ↦ (b ξ : ℂ)).HasTemperateGrowth)
    (g : SchwartzMap E (Fin r → ℂ)) (ξ : E) :
    channelFourierTransform (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) g) ξ =
      (b ξ : ℂ) • channelFourierTransform g ξ := by
  have hbc : (fun ξ : E ↦ (b ((2 * Real.pi) • ξ) : ℂ)).HasTemperateGrowth :=
    ht.comp (by fun_prop)
  change ((2 * Real.pi) ^ (d + 1) : ℝ)⁻¹ •
    (𝓕 (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) g)) ((2 * Real.pi)⁻¹ • ξ) = _
  simp only [physicalMultiplier, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply hbc]
  rw [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  exact smul_comm _ _ _

private theorem leftLocalizer_toEuclideanSchwartz
    (ρ : ℝ) (mi : LocalizerSymbol (d + 1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (g : SchwartzMap E (Fin r → ℂ)) :
    M ((toEuclideanSchwartz g).toLp 2) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi g x) := by
  have hg := (toEuclideanSchwartz g).coeFn_toLp 2
  have hint : ∀ i, Integrable (fun y ↦ (toEuclideanSchwartz g).toLp 2 volume y i) := by
    intro i
    apply (g.integrable.eval i).congr
    filter_upwards [hg] with y hy
    exact (congrArg (fun z : V ↦ z i) hy).symm
  refine (hM _ hint).trans (Eventually.of_forall (fun x ↦ ?_))
  apply congrArg (WithLp.toLp 2)
  unfold leftLocalizer graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [hg] with y hy
  rw [hy]
  rfl

/-- A scalar multiplier equal to one on the actual frequency support fixes
the right physical localizer. Both localizers are the SAME bounded adjoint
pair produced by `exists_bounded_physicalLocalizers`. The plateau premise is
geometric; for the actual angular symbol it is discharged below from the
fixed annulus and finite partition. No claim of physical support or global
annihilation is made (`app:ch_regular:eq:chain-tail`). -/
theorem scalarPhysicalFrequencyOperator_comp_rightLocalizer_eq
    (ρ : ℝ) (mi : LocalizerSymbol (d + 1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (b : E → ℝ) (hb : Continuous b) (hbound : ∀ ξ, ‖b ξ‖ ≤ 1)
    (ht : (fun ξ ↦ (b ξ : ℂ)).HasTemperateGrowth)
    (hplateau : ∀ x ξ, mi (x, ρ⁻¹ • ξ) ≠ 0 → b ξ = 1) :
    (scalarPhysicalFrequencyOperator b hb hbound).comp M.adjoint = M.adjoint := by
  have hleft : M.comp (scalarPhysicalFrequencyOperator b hb hbound) = M := by
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer
      (M.comp (scalarPhysicalFrequencyOperator b hb hbound)).continuous M.continuous
    funext u
    simp only [Function.comp_apply]
    rw [← schwartzVectorToLp_graphTestToSchwartz u,
      schwartzVectorToLp_eq_toEuclideanSchwartz_toLp]
    simp only [ContinuousLinearMap.comp_apply]
    rw [scalarPhysicalFrequencyOperator_toEuclideanSchwartz b hb hbound ht]
    apply Lp.ext
    filter_upwards [leftLocalizer_toEuclideanSchwartz ρ mi M hM
      (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) (graphTestToSchwartz u)),
      leftLocalizer_toEuclideanSchwartz ρ mi M hM (graphTestToSchwartz u)] with x hl hr
    rw [hl, hr]
    apply congrArg (WithLp.toLp 2)
    simp only [leftLocalizer_eq_channelFourierIntegral,
      channelFourierTransform_physicalMultiplier b ht]
    apply integral_congr_ae
    filter_upwards [] with ξ
    by_cases hm : mi (x, ρ⁻¹ • ξ) = 0
    · simp only [hm, Complex.ofReal_zero, mul_zero, zero_smul]
    · rw [hplateau x ξ hm, Complex.ofReal_one, one_smul]
  have h := congrArg ContinuousLinearMap.adjoint hleft
  simpa only [ContinuousLinearMap.adjoint_comp,
    scalarPhysicalFrequencyOperator_adjoint] using h

open RegularSector.FiniteMasks

/-- The actual finite angular symbol fixes the right localizer above a
single fixed radial threshold. `ProtectedMasks` supplies the compact annulus
and strict angular plateau; `ActualMaskFamily` supplies the original finite
partition and low bump. All operators and the threshold are independent of
accuracy. Physical source/output multipliers are deliberately still outside
this cancellation (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem actualAngularFrequency_comp_rightLocalizer_eq
    {Ω : Set E} {center : E} {RQ Mbound : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K Mbound)
    {lo ρ : ℝ} (hlo : 0 < lo) (hρ : 2 * f.radialThreshold / lo < ρ)
    (mi : LocalizerSymbol (d + 1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hang : ∀ p ∈ tsupport mi,
      NormedSpace.normalize p.2 ∈ interior {η | ∑ i, f.angularMask i η = 1}) :
    let b := fun ξ ↦ ∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ
    let hb : Continuous b := continuous_finsetSum _ (fun p _ ↦
      (contDiff_dilatedConicMask (f.angularMask_smooth p) f.radialThreshold).continuous)
    let hbound : ∀ ξ, ‖b ξ‖ ≤ 1 := fun ξ ↦
      (Real.norm_of_nonneg (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).1).trans_le
        (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).2
    (scalarPhysicalFrequencyOperator b hb hbound).comp M.adjoint = M.adjoint := by
  intro b hb hbound
  apply scalarPhysicalFrequencyOperator_comp_rightLocalizer_eq ρ mi M hM b hb hbound
    (actualFamily_angularSymbol_hasTemperateGrowth f)
  intro x ξ hm
  have hp : (x, ρ⁻¹ • ξ) ∈ tsupport mi := subset_tsupport mi hm
  have hR : 0 < f.radialThreshold := zero_lt_one.trans_le f.radialThreshold_ge_one
  have hρpos : 0 < ρ :=
    (div_pos (mul_pos (by norm_num) hR) hlo).trans hρ
  have hn : 2 * f.radialThreshold < ‖ξ‖ := by
    have hmul := mul_le_mul_of_nonneg_left (hann _ hp) hρpos.le
    have he : ρ * ‖ρ⁻¹ • ξ‖ = ‖ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρpos.le),
        ← mul_assoc, mul_inv_cancel₀ hρpos.ne', one_mul]
    rw [he] at hmul
    exact ((div_lt_iff₀ hlo).mp hρ).trans_le hmul
  apply sum_dilatedConicMask_eq_one_of_high_plateau f.angularMask hR hn.le
  have ha := interior_subset (s := {η | ∑ i, f.angularMask i η = 1}) (hang _ hp)
  simpa only [mem_ofPred_eq, NormedSpace.normalize_smul_of_pos (inv_pos.mpr hρpos)] using ha

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
