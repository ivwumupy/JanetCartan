module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.CompactSectionJets.Smooth

/-!
# L² bounds for the carrier derivatives of compact transverse sections

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, differentiation of the actual
transverse L² section commutes with taking scalar carrier derivatives.
The operator norm of each section derivative is bounded by the transverse
L² norm of the scalar jet's operator norm. Fubini then gives constant one.
The consumer is `exists_parameterInitialFourier_test_bound`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The concrete compact-test section has finite L² jet energy, bounded by
the corresponding scalar carrier jet with constant one. This is the
parameter differentiation input for `app:ch_background:eq:bg-density-adjoint`.
No transverse derivative is taken. -/
theorem carrierTestSlice_jet_memLp_and_bound (f : carrierInitialTestSpace n) (k : ℕ) :
    MemLp (iteratedFDeriv ℝ k (Fubini.slice f.val)) 2 (volume.prod volume) ∧
      lpNorm (iteratedFDeriv ℝ k (Fubini.slice f.val)) 2 (volume.prod volume) ≤
        lpNorm (weightedCarrierJet k 0 f.val) 2 (carrierMeasure n) := by
  let g : CarrierVariable n → ℂ := fun x ↦ (‖weightedCarrierJet k 0 f.val x‖ : ℂ)
  have hgc : Continuous g := Complex.continuous_ofReal.comp
    (continuous_weightedCarrierJet k 0 f.property.1).norm
  have hgs : HasCompactSupport g :=
    (hasCompactSupport_weightedCarrierJet k 0 f.property.1 f.property.2).norm.comp_left
      (by simp : ((0 : ℝ) : ℂ) = 0)
  have hgm : MemLp g 2 (carrierMeasure n) :=
    (memLp_weightedCarrierJet_of_compactSupport k 0 f.property.1 f.property.2).norm.continuousLinearMap_comp
      Complex.ofRealCLM
  have hslice z : MemLp (fun η ↦ g (z, η)) 2 volume :=
    carrier_memLp_slice_of_continuous_hasCompactSupport hgc hgs z
  have hpt (z : CarrierParameter) :
      ‖iteratedFDeriv ℝ k (Fubini.slice f.val) z‖ ≤ ‖Fubini.slice g z‖ := by
    apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
    intro v
    rw [mul_comm]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [iteratedFDeriv_carrierTestSlice_coeFn f k z v,
      Fubini.slice_coeFn (hslice z)] with η hη hgη
    rw [hη, hgη]
    simpa only [g, Complex.norm_real, norm_norm, weightedCarrierJet, etaBesselWeight,
      pow_zero, one_smul, mul_comm] using
      (iteratedFDeriv ℝ k (fun a ↦ f.val (a, η)) z).le_opNorm v
  have hs := Fubini.memLp_slice hgc.stronglyMeasurable hgm
  have hd := (contDiff_carrierTestSlice f).continuous_iteratedFDeriv
    (by simp : (k : ℕ∞ω) ≤ ∞)
  refine ⟨hs.mono hd.aestronglyMeasurable (Filter.Eventually.of_forall hpt), ?_⟩
  have he : carrierFubiniEquiv n (hgm.toLp g) =ᵐ[volume.prod volume] Fubini.slice g := by
    filter_upwards [carrierFubiniEquiv_toLp_coeFn hgm] with z hz
    exact Lp.ext (hz.trans (Fubini.slice_coeFn (hslice z)).symm)
  calc
    _ ≤ lpNorm (fun z ↦ ‖Fubini.slice g z‖) 2 (volume.prod volume) :=
      lpNorm_mono_real hs.norm hpt
    _ = lpNorm (Fubini.slice g) 2 (volume.prod volume) :=
      lpNorm_norm hs.aestronglyMeasurable 2
    _ = lpNorm g 2 (carrierMeasure n) := by
      change (eLpNorm _ 2 _).toReal = (eLpNorm _ 2 _).toReal
      rw [← eLpNorm_congr_ae he, ← Lp.norm_def, (carrierFubiniEquiv n).norm_map]
      exact Lp.norm_toLp _ hgm
    _ = _ := by
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_norm_ae hgm.aestronglyMeasurable
        (memLp_weightedCarrierJet_of_compactSupport k 0 f.property.1 f.property.2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun x ↦ by simp [g])

/-- Uniform bounds for all carrier jets of the actual transverse L² section.
This discharges the section hypothesis consumed by
`exists_parameterInitialFourier_test_bound`, for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_carrierTestSlice_jet_bound (s : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : carrierInitialTestSpace n,
      ContDiff ℝ ∞ (Fubini.slice f.val) ∧ ∀ k ≤ s,
        MemLp (iteratedFDeriv ℝ k (Fubini.slice f.val)) 2 (volume.prod volume) ∧
          lpNorm (iteratedFDeriv ℝ k (Fubini.slice f.val)) 2 (volume.prod volume) ≤
            D * lpNorm (weightedCarrierJet k 0 f.val) 2 (carrierMeasure n) := by
  refine ⟨1, zero_le_one, fun f ↦ ⟨contDiff_carrierTestSlice f, fun k _ ↦ ?_⟩⟩
  simpa only [one_mul] using carrierTestSlice_jet_memLp_and_bound f k

end JanetCartan.ContinuumAdjoint.DensityMultiplier
