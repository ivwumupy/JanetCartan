module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledMetric
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported

/-!
# Admission of the actual sampled signed-product sources

`app:ch_pairs:prop:pairs-lag-sum` applies the fixed response to the full
source-cutoff tensor. For the literal derivative amplitude of the sampled
fields, both signed products are smooth on the original physical chart:
their carrier phases cancel back to products of the actual derivatives.
The existing source-domain constructor then gives compact smooth sources and
Lebesgue L² membership, with the supplied source cutoff unchanged.

This closes source admission, not the response's quantitative estimates. The
same fixed inverse and response must still supply those estimates.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep

open PrimarySourceAdmission

variable {n N : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The complete signed products of the SAME sampled derivative are smooth
where the original atoms are smooth (`app:ch_pairs:lem:pairs-ledger`). No
smoothness of a separately chosen global phase or amplitude extension is used.
Consumed by `sampled_signed_sources_mem`. -/
theorem contDiffOn_sampled_signed_sources
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U) (i j : ι) :
    ContDiffOn ℝ ∞ (ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j) U ∧
      ContDiffOn ℝ ∞ (ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j) U := by
  have hd (i : ι) (a : Fin N) (l : Fin n) :
      ContDiffOn ℝ ∞ (fun x ↦ sampledDerivative Z i x a l) U :=
    (contDiffOn_piLp 2).mp
      (((hZ i).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const) a
  have hp : ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j =
      fun x ↦ (symmetricBilinearTensor (sampledDerivative Z i x)
        (sampledDerivative Z j x)).map Complex.re := by
    funext x
    rw [ProductSum.plusSource, signedPairPlus_eq,
      ← sampledDerivative_eq_phase_smul_amplitude, ← sampledDerivative_eq_phase_smul_amplitude]
  have hm : ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j =
      fun x ↦ (symmetricBilinearTensor (sampledDerivative Z i x)
        ((sampledDerivative Z j x).map conj)).map Complex.re := by
    funext x
    rw [ProductSum.minusSource, signedPairMinus_eq,
      ← sampledDerivative_eq_phase_smul_amplitude, ← sampledDerivative_eq_phase_smul_amplitude]
  let L : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    { LinearMap.id with cont := continuous_id }
  rw [hp, hm]
  constructor
  · apply L.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro a
    apply contDiffOn_pi.mpr
    intro l
    simp only [symmetricBilinearTensor_apply]
    apply Complex.reCLM.contDiff.comp_contDiffOn
    exact ContDiffOn.sum (s := Finset.univ) (fun c _ ↦
      (((hd i c a).mul (hd j c l)).add ((hd j c a).mul (hd i c l))).const_smul
        ((2 : ℂ)⁻¹))
  · apply L.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro a
    apply contDiffOn_pi.mpr
    intro l
    simp only [Matrix.map_apply, symmetricBilinearTensor_apply]
    apply Complex.reCLM.contDiff.comp_contDiffOn
    have hconj (a : Fin n) (c : Fin N) :=
      Complex.conjCLE.contDiff.comp_contDiffOn (hd j c a)
    exact ContDiffOn.sum (s := Finset.univ) (fun c _ ↦
      (((hd i c a).mul (hconj l c)).add ((hconj a c).mul (hd i c l))).const_smul
        ((2 : ℂ)⁻¹))

omit [Fintype ι] in
/-- Every actual full signed product, after the ORIGINAL source cutoff, lies
in the existing response source domain (`app:ch_pairs:eq:pairs-weighted-U`).
The supplied support buffer is preserved. This is the source-membership input
for `ResponseSourceExtension.contDiff_ambientExtension`; neither a smooth
response nor a source-domain membership is assumed. -/
theorem sampled_signed_sources_mem
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) (i j : ι) :
    (fun x ↦ χ x • ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x) ∈
        compactSmoothSources (tsupport χ) ∧
      (fun x ↦ χ x • ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x) ∈
        compactSmoothSources (tsupport χ) := by
  obtain ⟨hp, hm⟩ := contDiffOn_sampled_signed_sources Z θ hU hZ i j
  exact ⟨cutoff_mem_compactSmoothSources hχ hc hU hp hs,
    cutoff_mem_compactSmoothSources hχ hc hU hm hs⟩

/-- The complete off-self tensor on the SAME history and final family is an
actual compact smooth response source, with its original Lebesgue L² class
(`app:ch_pairs:eq:pairs-weighted-U`). The source cutoff is applied once to
the full tensor, and all doubled carriers are retained. -/
theorem sampled_offSelf_source_mem [DecidableEq ι]
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) :
    let q := fun x ↦ χ x •
      ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x
    q ∈ compactSmoothSources (tsupport χ) ∧ MemLp q 2 volume := by
  dsimp only
  let cut : MetricField n →ₗ[ℝ] MetricField n :=
    { toFun := fun q x ↦ χ x • q x
      map_add' := by intros; funext x; exact smul_add _ _ _
      map_smul' := by
        intro a q
        funext x
        change χ x • (a • q x) = a • (χ x • q x)
        exact smul_comm _ _ _ }
  have he : (fun x ↦ χ x •
      ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x) =
        ProductSum.weightedSignedSum b μ
          (fun i j x ↦ χ x • ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x)
          (fun i j x ↦ χ x • ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x) := by
    change cut _ = _
    rw [ProductSum.offSelfSource_eq_weightedSignedSum b μ hμ θ _ _
      (sampledDerivative_eq_phase_smul_amplitude Z θ), ProductSum.map_weightedSignedSum]
    rfl
  have hmem : (fun x ↦ χ x •
      ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x) ∈
        compactSmoothSources (tsupport χ) := by
    rw [he]
    exact ResponseSourceExtension.weightedSignedSum_mem b μ _ _
      (fun i j ↦ (sampled_signed_sources_mem Z θ hU hZ hχ hc hs i j).1)
      (fun i j _ ↦ (sampled_signed_sources_mem Z θ hU hZ hχ hc hs i j).2)
  exact ⟨hmem, memLp_of_mem_compactSmoothSources hmem⟩

/-- Apply the SAME ambient response to the literal full source-cutoff tensor
(`app:ch_pairs:eq:pairs-weighted-U`). Source admission and source smoothness
are proved above, so only the original reduced solver's regularity remains
an input from `both-fixed-inverse`. The result supplies the physical product
field's smoothness in `identities_sampled_history_fields_of_contDiffOn` and
identifies it with the original ambient formula and output cutoff. It does
not assert the response's error or Sobolev estimates. -/
theorem sampled_offSelf_ambientCorrection_smooth [DecidableEq ι] {κ : Type*}
    (F : Euclidean n → Euclidean N) (Q : Euclidean n → κ → MetricTensor n)
    (η : Euclidean n → ℝ)
    (T : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → κ → ℝ))
    (S : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    {core chart : Set (Euclidean n)} (Ξ : ResponseSourceExtension.OutputCutoff core chart)
    {χ : Euclidean n → ℝ}
    (hS : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (S (AmbientResponse.correctedStressSource Q η T h)) x)
    (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
    (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
    (hreg : ∀ h : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (S (AmbientResponse.correctedStressSource Q η T h)) chart)
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    let q := fun x ↦ χ x •
      ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x
    let B := ResponseSourceExtension.ambientExtension F Q η T S
      (compactSmoothSources (tsupport χ)) Ξ hS
    ContDiff ℝ ∞ (-B q) ∧
      -B q = fun x ↦ -(Ξ.toFun x • AmbientResponse.ambientResponse F Q η T S q x) := by
  dsimp only
  let q := fun x ↦ χ x •
    ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x
  have hq : q ∈ compactSmoothSources (tsupport χ) :=
    (sampled_offSelf_source_mem b μ hμ Z θ hU hZ hχ hc hs).1
  refine ⟨(ResponseSourceExtension.contDiff_ambientExtension F Q η T S
    (compactSmoothSources (tsupport χ)) Ξ hS ⟨q, hq⟩ ho hF hq.1.contDiffOn
    hi hrank (hreg ⟨q, hq⟩)).neg, ?_⟩
  exact congrArg Neg.neg (ResponseSourceExtension.ambientExtension_eq_cutoff F Q η T S
    (compactSmoothSources (tsupport χ)) Ξ hS ⟨q, hq⟩)

end JanetCartan.UniformStep
