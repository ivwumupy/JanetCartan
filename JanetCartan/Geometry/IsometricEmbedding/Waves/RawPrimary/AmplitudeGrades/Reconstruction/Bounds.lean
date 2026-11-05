module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Reconstruction.Quadratures

/-!
# Primitive bounds for the complex correction reconstruction

The consumer is the actual correction profile in `Reconstruction`. The bounds
for `app:ch_waves:eq:exact-W-amplitude` retain both quadratures of the SAME
covector. No estimate of an ambient coefficient is a hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave AmbientResponse ResponseTransfer

/-- Smoothness of the complex principal normal on the original product chart,
from primitive geometry and covector smoothness (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem contDiffOn_joint_canonicalPrincipalNormalComplex {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)}
    {ξ : Euclidean n × Z → Euclidean n}
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V))
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p))
      (U ×ˢ V) := by
  have hR := contDiffOn_joint_principalNormal_canonical hU hV hF
    (euclideanRealPart.contDiff.comp_contDiffOn hb) hξ hi hrank
  have hI := contDiffOn_joint_principalNormal_canonical hU hV hF
    ((correctionImaginaryPart n).contDiff.comp_contDiffOn hb) hξ hi hrank
  apply ((euclideanComplexInclusion.contDiff.comp_contDiffOn hR).add
    ((euclideanComplexInclusion.contDiff.comp_contDiffOn hI).const_smul Complex.I)).congr
  intro p _
  exact canonicalPrincipalNormalComplex_eq_quadratures F p.1 (ξ p) (b p)

/-- The complex principal normal is smooth on an arbitrary open flow domain;
local product neighborhoods suffice (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem contDiffOn_joint_canonicalPrincipalNormalComplex_of_isOpen {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)}
    {ξ : Euclidean n × Z → Euclidean n}
    {U : Set (Euclidean n)} {Ω : Set (Euclidean n × Z)}
    (hΩ : IsOpen Ω) (hspace : ∀ p ∈ Ω, p.1 ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b Ω)
    (hξ : ContDiffOn ℝ ∞ ξ Ω)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p)) Ω := by
  intro p hp
  obtain ⟨X, V, hX, hV, hx, hv, hsub⟩ := isOpen_prod_iff.mp hΩ p.1 p.2 hp
  have hXU : X ⊆ U := fun x hx ↦ hspace (x, p.2) (hsub ⟨hx, hv⟩)
  exact ((contDiffOn_joint_canonicalPrincipalNormalComplex hX hV (hF.mono hXU)
    (hb.mono hsub) (hξ.mono hsub) (fun x hx ↦ hi x (hXU hx))
      (fun x hx ↦ hrank x (hXU hx))).contDiffAt
        ((hX.prod hV).mem_nhds ⟨hx, hv⟩)).contDiffWithinAt

/-- Joint one-high bounds for both actual complex reconstruction coefficients.
The constant precedes all varying fields and domains. The derivative losses
are two in the immersion, one in the correction and zero in the phase gradient
(`app:ch_waves:eq:exact-W-amplitude`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_complex_reconstruction_le_of_primitive_bounds
    {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {M γ κ : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hκ : 0 < κ) (B : ℝ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (U : Set (Euclidean n)) (V : Set Z), IsOpen U → IsOpen V →
      closedBall a.1 ρ ⊆ U → closedBall a.2 ρ ⊆ V →
      ∀ (F : Euclidean n → Euclidean N)
        (b : Euclidean n × Z → EuclideanSpace ℂ (Fin n))
        (ξ : Euclidean n × Z → Euclidean n),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞ b (U ×ˢ V) → ContDiffOn ℝ ∞ ξ (U ×ˢ V) →
      cNorm (closedBall a.1 ρ) 4 F ≤ M →
      (∀ x ∈ closedBall a.1 ρ, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall a.1 ρ, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall a ρ) 1 b ≤ B → cNorm (closedBall a ρ) 1 ξ ≤ B →
      ∀ j,
      cNorm (closedBall a ρ) j (fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p)) +
        cNorm (closedBall a ρ) j
          (fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1) ≤
        C j * (1 + cNorm (closedBall a.1 ρ) (j + 2) F +
          cNorm (closedBall a ρ) (j + 1) b + cNorm (closedBall a ρ) j ξ) := by
  obtain ⟨C, hC, hbound⟩ :=
    JointReconstruction.exists_cNorm_joint_reconstruction_le_of_primitive_bounds
      (N := N) a hρ hM hγ hκ B
  refine ⟨fun j ↦ 2 * C j, fun j ↦ mul_pos (by norm_num) (hC j), ?_⟩
  intro U V hU hV hKU hKV F b ξ hF hi hrank hb hξ hFM hmetric hnormal hbB hξB j
  have hKUV : closedBall a ρ ⊆ U ×ˢ V := by
    rw [← closedBall_prod_same a.1 a.2 ρ]
    exact Set.prod_mono hKU hKV
  have hbat (k : ℕ) (p) (hp : p ∈ closedBall a ρ) : ContDiffAt ℝ k b p :=
    (hb.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp)
  let bR := euclideanRealPart ∘ b
  let bI := correctionImaginaryPart n ∘ b
  have hbR : ContDiffOn ℝ ∞ bR (U ×ˢ V) := euclideanRealPart.contDiff.comp_contDiffOn hb
  have hbI : ContDiffOn ℝ ∞ bI (U ×ˢ V) :=
    (correctionImaginaryPart n).contDiff.comp_contDiffOn hb
  have hquad (k : ℕ) := cNorm_correction_quadratures_le (isCompact_closedBall a ρ) k (hbat k)
  have hR := hbound U V hU hV hKU hKV F bR ξ hF hi hrank hbR hξ hFM hmetric hnormal
    ((hquad 1).1.trans hbB) hξB j
  have hI := hbound U V hU hV hKU hKV F bI ξ hF hi hrank hbI hξ hFM hmetric hnormal
    ((hquad 1).2.trans hbB) hξB j
  let nR := fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (bR p)
  let nI := fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (bI p)
  let vR := fun p : Euclidean n × Z ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ bR (x, p.2)) p.1
  let vI := fun p : Euclidean n × Z ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ bI (x, p.2)) p.1
  have hnR := contDiffOn_joint_principalNormal_canonical hU hV hF hbR hξ hi hrank
  have hnI := contDiffOn_joint_principalNormal_canonical hU hV hF hbI hξ hi hrank
  have hvR := JointReconstruction.contDiffOn_joint_reconstruction_canonical hU hV hF hbR hi hrank
  have hvI := JointReconstruction.contDiffOn_joint_reconstruction_canonical hU hV hF hbI hi hrank
  have hn := cNorm_complex_quadrature_sum_le (isCompact_closedBall a ρ) j
    (fun p hp ↦ (hnR.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
    (fun p hp ↦ (hnI.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
  have hv := cNorm_complex_quadrature_sum_le (isCompact_closedBall a ρ) j
    (fun p hp ↦ (hvR.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
    (fun p hp ↦ (hvI.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
  have hen : (fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p)) =
      (fun p ↦ euclideanComplexInclusion (nR p) + Complex.I • euclideanComplexInclusion (nI p)) := by
    funext p
    exact canonicalPrincipalNormalComplex_eq_quadratures F p.1 (ξ p) (b p)
  have hev : cNorm (closedBall a ρ) j
      (fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1) =
      cNorm (closedBall a ρ) j
        (fun p ↦ euclideanComplexInclusion (vR p) + Complex.I • euclideanComplexInclusion (vI p)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ j
    intro p hp
    filter_upwards [(hU.prod hV).mem_nhds (hKUV hp)] with q hq
    exact completedVariationComplex_eq_quadratures F
      (((hb.contDiffAt ((hU.prod hV).mem_nhds hq)).differentiableAt (by simp)).comp q.1
        (differentiableAt_id.prodMk (differentiableAt_const _)))
  rw [hen, hev]
  apply (add_le_add hn hv).trans
  have hbRhigh := (hquad (j + 1)).1
  have hbIhigh := (hquad (j + 1)).2
  have hRm := cNorm_nonneg (closedBall a ρ) j (fun p ↦ principalMatrix (nR p) (ξ p))
  have hIm := cNorm_nonneg (closedBall a ρ) j (fun p ↦ principalMatrix (nI p) (ξ p))
  have hmR := mul_le_mul_of_nonneg_left hbRhigh (hC j).le
  have hmI := mul_le_mul_of_nonneg_left hbIhigh (hC j).le
  dsimp only [nR, nI, vR, vI, bR, bI] at *
  nlinarith

end JanetCartan.RawPrimary.AmplitudeGrades
