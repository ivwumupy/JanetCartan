module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.WeightSplit
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.FullCompatibility

/-!
# Carrier parameter weights through partial Fourier synthesis

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, a weight in the three carrier
parameters passes through the carrier Fubini identification and the exact
transverse normalization dilation without changing its L² norm. The eventual
compact-test parameter estimate uses this to transfer its Hilbert-valued
parameter Plancherel bound to the literal product measure.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- A measurable carrier-parameter weight commutes with the inverse Fubini
identification, with equality of its numerical L² norms. The parameter
Plancherel estimate for `app:ch_background:eq:bg-density-adjoint` consumes
this statement; no boundedness of the weight is required. -/
theorem parameterWeight_carrierFubiniEquiv_symm
    (w : CarrierParameter → ℝ) (hw : Measurable w) (g : IteratedCarrierL2 n)
    (hg : MemLp (fun z => w z • g z) 2 (volume.prod volume)) :
    MemLp (fun x : CarrierVariable n => w x.1 • (carrierFubiniEquiv n).symm g x)
        2 (carrierMeasure n) ∧
      lpNorm (fun x : CarrierVariable n => w x.1 • (carrierFubiniEquiv n).symm g x)
        2 (carrierMeasure n) =
      lpNorm (fun z => w z • g z) 2 (volume.prod volume) := by
  let q : IteratedCarrierL2 n := hg.toLp _
  have he : (carrierFubiniEquiv n).symm q =ᵐ[carrierMeasure n]
      fun x : CarrierVariable n => w x.1 • (carrierFubiniEquiv n).symm g x := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (Lp.stronglyMeasurable _).measurable
      ((hw.comp measurable_fst).smul (Lp.stronglyMeasurable _).measurable))).mpr
    filter_upwards [carrierFubiniEquiv_symm_coeFn n q,
      carrierFubiniEquiv_symm_coeFn n g, hg.coeFn_toLp] with z hq hz hzg
    change q z = w z • g z at hzg
    rw [hzg] at hq
    filter_upwards [hq, hz, Lp.coeFn_smul (w z) (g z)] with η hqη hgη hsη
    exact hqη.trans (hsη.trans (congrArg (fun a : ℂ => w z • a) hgη.symm))
  refine ⟨(Lp.memLp ((carrierFubiniEquiv n).symm q)).ae_eq he, ?_⟩
  change (eLpNorm _ 2 (carrierMeasure n)).toReal =
    (eLpNorm _ 2 (volume.prod volume)).toReal
  rw [← eLpNorm_congr_ae he, ← Lp.norm_def,
    (carrierFubiniEquiv n).symm.norm_map]
  exact Lp.norm_toLp _ hg

/-- An arbitrary measurable parameter weight keeps its L² norm under the
inverse transverse dilation. This retains the shared radian normalization
in the parameter estimate for `app:ch_background:prop:bg-adjoint`. -/
theorem parameterWeight_iteratedTransverseDilation_symm
    (w : CarrierParameter → ℝ) (hw : Measurable w) (g : IteratedCarrierL2 n)
    (hg : MemLp (fun z => w z • g z) 2 (volume.prod volume)) :
    MemLp (fun z => w z • (iteratedTransverseDilation n).symm g z)
        2 (volume.prod volume) ∧
      lpNorm (fun z => w z • (iteratedTransverseDilation n).symm g z)
        2 (volume.prod volume) =
      lpNorm (fun z => w z • g z) 2 (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun z => w z • (iteratedTransverseDilation n).symm g z) (volume.prod volume) :=
    hw.aestronglyMeasurable.smul (Lp.memLp _).aestronglyMeasurable
  have he : (fun z => ‖w z • (iteratedTransverseDilation n).symm g z‖)
      =ᵐ[volume.prod volume] fun z => ‖w z • g z‖ := by
    filter_upwards [iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ) g]
      with z hz
    change (iteratedTransverseDilation n).symm g z =
      (transverseDilation n ℂ).symm (g z) at hz
    rw [hz, norm_smul, norm_smul, (transverseDilation n ℂ).symm.norm_map]
  refine ⟨hg.congr_norm hm he.symm, ?_⟩
  exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae hm hg.aestronglyMeasurable he)

set_option maxHeartbeats 800000 in
/-- Parameter-weighted full Fourier energy after actual partial synthesis
equals the parameter Fourier energy on the transverse Hilbert fiber.
This discharges the Fubini and normalization steps of the compact-test
parameter estimate in `app:ch_background:eq:bg-density-adjoint`. The
remaining weighted membership is to be proved by parameter differentiation
and Plancherel for the actual test section. -/
theorem parameterWeight_initialFourier_partialUnitaryInverse
    (w : CarrierParameter → ℝ) (hw : Measurable w) (f : CarrierL2 n)
    (hf : MemLp (fun z => w z •
      iteratedParameterFourier n (carrierFubiniEquiv n f) z) 2 (volume.prod volume)) :
    MemLp (fun ξ : CarrierVariable n =>
      w ξ.1 • initialFourier n (partialUnitaryInverse n f) ξ) 2 (carrierMeasure n) ∧
      lpNorm (fun ξ : CarrierVariable n =>
        w ξ.1 • initialFourier n (partialUnitaryInverse n f) ξ) 2 (carrierMeasure n) =
      lpNorm (fun z => w z • iteratedParameterFourier n (carrierFubiniEquiv n f) z)
        2 (volume.prod volume) := by
  obtain ⟨hd, hed⟩ := parameterWeight_iteratedTransverseDilation_symm (n := n) w hw _ hf
  obtain ⟨hF, heF⟩ := parameterWeight_carrierFubiniEquiv_symm (n := n) w hw _ hd
  rw [initialFourier_partialUnitaryInverse]
  exact ⟨hF, heF.trans hed⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
