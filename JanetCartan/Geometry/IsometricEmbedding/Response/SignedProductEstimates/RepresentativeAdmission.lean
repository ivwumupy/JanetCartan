module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Amplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Strain
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SignedSourceAdmission

/-!
# Admission of signed sources through amplitude representatives

The normalized solver estimates a smooth amplitude representative on its
profile domain. The physical sampled amplitude need agree with that
representative only on the original source support. Admission follows from
the actual phases and amplitudes, without representing the latter as the
derivative of a different field. Consumers are the normalized fixed-solver
size estimate and its original-frame periodic-source application.
Sources: `app:ch_pairs:lem:pairs-ledger`, `app:ch_pairs:eq:pairs-lag-sum-size`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open PrimarySourceAdmission ResponseSourceExtension UniformStep
variable {n N : ℕ} {ι : Type*}

/-- Smooth phase and full amplitude representatives admit both complete
cutoff signed sources. Equal indices are allowed for the plus source
(`app:ch_pairs:lem:pairs-ledger`, `app:ch_pairs:eq:pairs-weighted-U`). -/
theorem cutoff_signed_sources_mem_of_smooth_phases
    (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hθ : ∀ i, ContDiffOn ℝ ∞ (θ i) U)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) (i j : ι) :
    (fun x ↦ χ x • ProductSum.plusSource θ A i j x) ∈ compactSmoothSources (tsupport χ) ∧
      (fun x ↦ χ x • ProductSum.minusSource θ A i j x) ∈ compactSmoothSources (tsupport χ) := by
  obtain ⟨hp, hm⟩ := contDiffOn_signed_tensor_amplitudes (hA i) (hA j)
  have hw {φ : Euclidean n → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) :
      ContDiffOn ℝ ∞ (fun x ↦ wavePhase (φ x)) U := by
    unfold wavePhase
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn hφ).mul contDiffOn_const).cexp
  exact ⟨cutoff_mem_compactSmoothSources hχ hc hU
      (contDiffOn_tensorFieldRealPart ((hw ((hθ i).add (hθ j))).smul hp)) hs,
    cutoff_mem_compactSmoothSources hχ hc hU
      (contDiffOn_tensorFieldRealPart ((hw ((hθ i).sub (hθ j))).smul hm)) hs⟩

/-- The original full tensor depends on the phase and amplitude representative
only on the whole source support. The original sampled derivative is retained;
no agreement on a larger analytic profile ball is needed
(`app:ch_pairs:eq:pairs-lag-sum-size`, Step 2). -/
theorem cutoff_sampled_signed_source_eq_of_representatives
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ φ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (χ : Euclidean n → ℝ)
    (hθ : ∀ i, EqOn (θ i) (φ i) (tsupport χ))
    (hA : ∀ i, EqOn (sampledDerivativeAmplitude Z θ i) (A i) (tsupport χ))
    (minus : Bool) (i j : ι) :
    (fun x ↦ χ x • (if minus then ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x
      else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x)) =
    (fun x ↦ χ x • (if minus then ProductSum.minusSource φ A i j x
      else ProductSum.plusSource φ A i j x)) := by
  funext x
  by_cases hx : χ x = 0
  · simp only [hx, zero_smul]
  · have hxS := subset_tsupport χ hx
    simp only [ProductSum.minusSource, ProductSum.plusSource,
      hθ i hxS, hθ j hxS, hA i hxS, hA j hxS]

end JanetCartan.SignedProductEstimates
