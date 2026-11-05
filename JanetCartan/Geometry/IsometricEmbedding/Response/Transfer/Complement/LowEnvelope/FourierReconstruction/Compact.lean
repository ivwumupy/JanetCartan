module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.Graph
/-!
# Absolute convergence of compact-frequency reconstruction

Compact full amplitudes and the Fourier L¹ bound justify joint frequency/source
integration in `app:ch_response:thm:response-literal-transfer`. All measures are
Lebesgue; no physical L¹ assumption is used for the low-support L² datum.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.LowEnvelope
open JanetCartan.Localization FourierIntegral
variable {n r : ℕ}
local instance : ContinuousENorm (Matrix (Fin r) (Fin r) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin r) (Fin r) ℂ) inferInstance).toContinuousENorm
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin r → Fin r → ℂ))

/-- Joint absolute integrability of the reconstructed source kernel against an
L¹ Fourier datum. This is the compact-frequency Fubini prerequisite for the low
envelope in `app:ch_response:thm:response-literal-transfer`; it uses no decay bound.
Continuity suffices, so in particular smooth compact full amplitudes qualify. -/
theorem integrable_sourceKernel_mulVec (A : FullAmplitude n r) (x : Euclidean n)
    (ha : Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (hc : HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (ψ : Euclidean n → Euclidean n → Euclidean n → ℝ)
    (hψ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦ ψ p.1.1 p.2 p.1.2))
    {H : Euclidean n → EuclideanSpace ℂ (Fin r)} (hH : Integrable H) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      (sourceKernel (ψ p.1 p.2) A x p.1).mulVec (H p.2)) (volume.prod volume) := by
  let T : Matrix (Fin r) (Fin r) ℂ →L[ℂ]
      ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) :=
    (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.toContinuousLinearMap
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  have ha' : Integrable (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1)
      (volume.prod volume) := ha.integrable_of_hasCompactSupport hc
  have hi := (T.integrable_comp ha').op_fst_snd
    (op := fun (T : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) v ↦ T v)
    (by fun_prop) ⟨1, fun T v ↦ by simpa using T.le_opNorm v⟩
    (e.toContinuousLinearMap.integrable_comp hH)
  have hp : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      phaseOscillation (ψ p.1.1 p.2) p.1.2) := by
    unfold phaseOscillation
    exact ((Complex.continuous_ofReal.comp hψ).mul continuous_const).cexp
  have hj := hi.bdd_smul 1 hp.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p ↦ (norm_phaseOscillation _ _).le))
  change Integrable (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      phaseOscillation (ψ p.1.1 p.2) p.1.2 •
        (A x p.1.2 p.1.1).mulVec (H p.2)) ((volume.prod volume).prod volume) at hj
  have hk : Integrable (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      phaseOscillation (ψ p.1 p.2.2) p.2.1 •
        (A x p.2.1 p.1).mulVec (H p.2.2)) (volume.prod (volume.prod volume)) :=
    (measurePreserving_prodAssoc volume volume volume).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding |>.mp hj
  have hl : Integrable (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      phaseOscillation (ψ p.1 p.2.1) p.2.2 •
        (A x p.2.2 p.1).mulVec (H p.2.1)) (volume.prod (volume.prod volume)) :=
    ((MeasurePreserving.id volume).prod Measure.measurePreserving_swap).integrable_comp_emb
      ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodComm : (Euclidean n × Euclidean n) ≃ᵐ _)).measurableEmbedding
      |>.mpr hk
  have hm : Integrable (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      phaseOscillation (ψ p.1.1 p.1.2) p.2 •
        (A x p.2 p.1.1).mulVec (H p.1.2)) ((volume.prod volume).prod volume) :=
    (measurePreserving_prodAssoc volume volume volume).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding |>.mpr hl
  apply hm.integral_prod_left.congr
  filter_upwards [] with p
  let L : Matrix (Fin r) (Fin r) ℂ →L[ℂ] (Fin r → ℂ) :=
    (ContinuousLinearMap.apply ℂ (Fin r → ℂ) (⇑(H p.2))).comp T
  have has : HasCompactSupport (fun y ↦ A x y p.1) :=
    HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd) (by
      intro y hy
      exact ⟨(p.1, y), subset_tsupport _ hy, rfl⟩)
  have hai : Integrable (fun y ↦ A x y p.1) :=
    (ha.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport has
  have hpi : Continuous (fun y ↦ phaseOscillation (ψ p.1 p.2) y) :=
    hp.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hb := hai.bdd_smul 1 hpi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y ↦ (norm_phaseOscillation _ _).le))
  have he := L.integral_comp_comm hb
  change (∫ y, (phaseOscillation (ψ p.1 p.2) y • A x y p.1).mulVec (H p.2)) =
    (sourceKernel (ψ p.1 p.2) A x p.1).mulVec (H p.2) at he
  simpa only [Matrix.smul_mulVec] using he
end JanetCartan.ResponseTransfer.LowEnvelope
