module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.IntegralRepresentative
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Integrating continuous representatives with noncompact output

The regularized identity term has noncompact output. Compact exhaustion,
using bounded physical multiplication, identifies its elapsed integral
without imposing compact output support or a pointwise time majorant.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral LowBounds LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Continuous representatives of integrable L² orbits represent their actual
elapsed integral, even for the noncompact output of the regularized identity.
Consumer: finite elapsed shell identification in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_L2_eq_continuous_representative
    (g : ℝ → H) (F : ℝ → E → V) (Δ : ℝ)
    (hg : IntegrableOn g (Icc 0 Δ)) (hc : Continuous (Function.uncurry F))
    (he : ∀ᵐ r ∂volume.restrict (Icc 0 Δ), g r =ᵐ[volume] F r) :
    (∫ r in Icc 0 Δ, g r) =ᵐ[volume] fun x ↦ ∫ r in Icc 0 Δ, F r x := by
  have hb (j : ℕ) (x : E) : ‖physicalCutoff j x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (physicalCutoff_nonneg j x)]
    exact physicalCutoff_le_one j x
  let M (j : ℕ) : H →L[ℂ] H :=
    sourceCutMultiplier (physicalCutoff j) (physicalCutoff_contDiff j).continuous (hb j)
  have hcut (j : ℕ) : ∀ᵐ x ∂volume,
      (physicalCutoff j x : ℂ) • (∫ r in Icc 0 Δ, g r) x =
        (physicalCutoff j x : ℂ) • ∫ r in Icc 0 Δ, F r x := by
    have hr := integral_L2_eq_compact_representative
      (fun r ↦ M j (g r)) (fun r x ↦ (physicalCutoff j x : ℂ) • F r x) Δ
      (((Complex.continuous_ofReal.comp (physicalCutoff_contDiff j).continuous).comp
        continuous_snd).smul hc)
      (physicalCutoff_hasCompactSupport j)
      (fun r x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) (by
        filter_upwards [he] with r hr
        exact (sourceCutMultiplier_coeFn _ _ _ (g r)).trans
          (hr.mono (fun x hx ↦ by dsimp; rw [hx])))
    rw [(M j).integral_comp_comm hg] at hr
    filter_upwards [hr, sourceCutMultiplier_coeFn _ _ _ (∫ r in Icc 0 Δ, g r)]
      with x hx hm
    rw [hm, integral_smul] at hx
    exact hx
  filter_upwards [ae_all_iff.mpr hcut] with x hx
  obtain ⟨j, hj⟩ := (physicalCutoff_eventually_eq_one x).exists
  simpa only [hj, Complex.ofReal_one, one_smul] using hx j

/-- An almost everywhere physical limit and a strong L² limit of the same
sequence agree. Consumer: identifying the summed elapsed shell action with
the actual operator in `app:ch_regular:eq:chain-tail`. -/
theorem ae_eq_of_strongLimit_of_representatives
    (v : ℕ → H) (w : H) (f : ℕ → E → V) (g : E → V)
    (he : ∀ᶠ j in atTop, v j =ᵐ[volume] f j)
    (hv : Tendsto v atTop (𝓝 w))
    (hf : ∀ᵐ x ∂volume, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x))) :
    w =ᵐ[volume] g := by
  have hae (j : ℕ) : ∀ᵐ x ∂volume, (v j =ᵐ[volume] f j) → v j x = f j x := by
    by_cases h : v j =ᵐ[volume] f j
    · exact h.mono (fun _ hx _ ↦ hx)
    · exact Eventually.of_forall (fun _ hx ↦ (h hx).elim)
  obtain ⟨φ, hφ, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [hlim, hf, ae_all_iff.mpr hae] with x hx hg hxe
  exact tendsto_nhds_unique hx ((hg.comp hφ.tendsto_atTop).congr'
    ((hφ.tendsto_atTop.eventually he).mono (fun j hj ↦ (hxe (φ j) hj).symm)))

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
