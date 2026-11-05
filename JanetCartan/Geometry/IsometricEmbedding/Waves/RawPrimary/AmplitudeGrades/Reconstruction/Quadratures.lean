module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Definitions
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Both quadratures of the correction reconstruction

Regularity and norm comparison for `app:ch_waves:eq:exact-W-amplitude`.
The consumer is the primitive geometric estimate in `Reconstruction.Bounds`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 5

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave AmbientResponse ResponseTransfer

/-- The imaginary quadrature of the correction in
`app:ch_waves:eq:primary-algebraic-correction`, as a real contraction. -/
def correctionImaginaryPart (n : ℕ) : EuclideanSpace ℂ (Fin n) →L[ℝ] Euclidean n :=
  euclideanRealPart.comp ((-Complex.I) • ContinuousLinearMap.id ℝ _)

/-- The contraction retains the imaginary coordinate of the actual correction
(`app:ch_waves:eq:primary-algebraic-correction`). -/
@[simp] theorem correctionImaginaryPart_apply {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    correctionImaginaryPart n v i = (v i).im := by
  simp [correctionImaginaryPart, Complex.mul_re]

/-- Imaginary-part extraction has norm at most one in the joint reconstruction
estimate (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem correctionImaginaryPart_norm_le (n : ℕ) : ‖correctionImaginaryPart n‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1 * 1 := mul_le_mul euclideanRealPart_norm_le
      (by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro v
        simp [norm_smul]) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

private theorem cNorm_contraction {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} (hK : IsCompact K) (j : ℕ) (A : F →L[ℝ] G) (hA : ‖A‖ ≤ 1)
    {f : E → F} (hf : ∀ x ∈ K, ContDiffAt ℝ j f x) :
    cNorm K j (A ∘ f) ≤ cNorm K j f :=
  (FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on hK j A hf).trans
    (by simpa using mul_le_mul_of_nonneg_right hA (cNorm_nonneg K j f))

/-- Taking either actual quadrature loses no derivatives or norm factors
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem cNorm_correction_quadratures_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {K : Set E} (hK : IsCompact K) (j : ℕ)
    {b : E → EuclideanSpace ℂ (Fin n)} (hb : ∀ x ∈ K, ContDiffAt ℝ j b x) :
    cNorm K j (euclideanRealPart ∘ b) ≤ cNorm K j b ∧
      cNorm K j (correctionImaginaryPart n ∘ b) ≤ cNorm K j b :=
  ⟨cNorm_contraction hK j (euclideanRealPart (ι := Fin n)) euclideanRealPart_norm_le hb,
    cNorm_contraction hK j (correctionImaginaryPart n) (correctionImaginaryPart_norm_le n) hb⟩

/-- Recombining the quadratures costs only their sum, including all ambient
derivatives (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem cNorm_complex_quadrature_sum_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    {K : Set E} (hK : IsCompact K) (j : ℕ) {f g : E → Euclidean N}
    (hf : ∀ x ∈ K, ContDiffAt ℝ j f x) (hg : ∀ x ∈ K, ContDiffAt ℝ j g x) :
    cNorm K j (fun x ↦ euclideanComplexInclusion (f x) +
      Complex.I • euclideanComplexInclusion (g x)) ≤ cNorm K j f + cNorm K j g := by
  let A : Euclidean N →L[ℝ] EuclideanSpace ℂ (Fin N) :=
    Complex.I • euclideanComplexInclusion
  have hA : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound zero_le_one
    intro v
    simp [A, norm_smul, euclideanComplexInclusion_norm]
  exact (cNorm_add_le_of_contDiffAt hK
    (fun x hx ↦ euclideanComplexInclusion.contDiff.contDiffAt.comp x (hf x hx))
    (fun x hx ↦ A.contDiff.contDiffAt.comp x (hg x hx))).trans
      (add_le_add (cNorm_contraction hK j (euclideanComplexInclusion (ι := Fin N)) euclideanComplexInclusion_norm_le hf)
        (cNorm_contraction hK j A hA hg))

/-- The literal principal normal is smooth on the primitive geometric chart.
This supplies the regularity required by the correction's norm estimate
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem contDiffOn_joint_principalNormal_canonical {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b ξ : Euclidean n × Z → Euclidean n}
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V))
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞
      (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p))
      (U ×ˢ V) := by
  have hj := JointReconstruction.contDiffOn_jointJet hU hV hF hb hξ
  intro p hp
  have hFp : ContDiffAt ℝ 2 F p.1 := (hF.contDiffAt (hU.mem_nhds hp.1)).of_le (by simp)
  have hr : Set.range (GeometricProfile.secondJetNormalMap (GeometricProfile.secondJet F p.1)) =
      ((LinearMap.range (fderiv ℝ F p.1).toLinearMap)ᗮ : Set (Euclidean N)) := by
    rw [JointReconstruction.secondJetNormalMap_eq_of_contDiffAt hFp (hi _ hp.1)]
    exact hrank _ hp.1
  exact (((JointReconstruction.contDiffAt_principalNormalValue
    (q := JointReconstruction.jointJet F b ξ p) (hi _ hp.1) hr).comp p
      (hj.contDiffAt ((hU.prod hV).mem_nhds hp))).congr_of_eventuallyEq
        (JointReconstruction.jointJet_fields_eventuallyEq ξ hU hV hF hb hi hrank hp).1.symm).contDiffWithinAt

/-- Exact quadrature identity for the correction principal normal
(`app:ch_waves:eq:exact-W-amplitude`). -/
theorem canonicalPrincipalNormalComplex_eq_quadratures {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x ξ : Euclidean n)
    (b : EuclideanSpace ℂ (Fin n)) :
    canonicalPrincipalNormalComplex F x ξ b =
      euclideanComplexInclusion (principalNormal (canonicalNormalCompletion F x) ξ
        (euclideanRealPart b)) + Complex.I • euclideanComplexInclusion
          (principalNormal (canonicalNormalCompletion F x) ξ (correctionImaginaryPart n b)) := by
  have he : correctionImaginaryPart n b = WithLp.toLp 2 (fun i ↦ (b i).im) := by ext; simp
  ext k
  apply Complex.ext <;>
    simp [canonicalPrincipalNormalComplex_re, canonicalPrincipalNormalComplex_im, he,
      euclideanRealPart]

/-- Exact quadrature identity for the full zero-source reconstruction,
including its tangential and Christoffel terms (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem completedVariationComplex_eq_quadratures {n N : ℕ}
    (F : Euclidean n → Euclidean N) {b : Euclidean n → EuclideanSpace ℂ (Fin n)}
    {x : Euclidean n} (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F b 0 x =
      euclideanComplexInclusion (reconstruction F (canonicalNormalCompletion F)
        (euclideanRealPart ∘ b) x) + Complex.I • euclideanComplexInclusion
          (reconstruction F (canonicalNormalCompletion F) (correctionImaginaryPart n ∘ b) x) := by
  have he : correctionImaginaryPart n ∘ b = fun y ↦ WithLp.toLp 2 (fun i ↦ (b y i).im) := by
    funext y; ext; simp
  ext k
  apply Complex.ext <;>
    simp [completedVariationComplex_zero_re F hb, completedVariationComplex_zero_im F hb,
      he, euclideanRealPart, Function.comp_def]

end JanetCartan.RawPrimary.AmplitudeGrades
