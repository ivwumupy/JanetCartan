module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CanonicalAtom
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.LocalIdentity

/-!
# Smoothness of the actual reconstructed atoms

For `app:ch_waves:thm:individual`, derive joint regularity of the literal
canonical atom from smooth covectors and primitive immersion/normal rank.
Both quadratures use the same canonical real reconstruction. These results
discharge the atomic regularity inputs of `CanonicalSuperposition`; they do
not assert coefficient grades or a prepared initial scalar.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave ResponseTransfer

variable {n N : ℕ}

/-- Joint regularity of the zero-source complex reconstruction, obtained
from its two actual real quadratures (`app:ch_waves:eq:reconstruction`). -/
theorem contDiffOn_joint_completedVariationComplex_zero {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N}
    {b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞
      (fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1) (U ×ˢ V) := by
  let bR : Euclidean n × Z → Euclidean n :=
    fun p ↦ WithLp.toLp 2 (fun i ↦ (b p i).re)
  let bI : Euclidean n × Z → Euclidean n :=
    fun p ↦ WithLp.toLp 2 (fun i ↦ (b p i).im)
  have hbR : ContDiffOn ℝ ∞ bR (U ×ˢ V) :=
    (contDiffOn_piLp 2).mpr fun i ↦
      Complex.reCLM.contDiff.comp_contDiffOn ((contDiffOn_piLp 2).mp hb i)
  have hbI : ContDiffOn ℝ ∞ bI (U ×ˢ V) :=
    (contDiffOn_piLp 2).mpr fun i ↦
      Complex.imCLM.contDiff.comp_contDiffOn ((contDiffOn_piLp 2).mp hb i)
  have hR := JointReconstruction.contDiffOn_joint_reconstruction_canonical hU hV hF hbR hi hrank
  have hI := JointReconstruction.contDiffOn_joint_reconstruction_canonical hU hV hF hbI hi hrank
  apply ((euclideanComplexInclusion.contDiff.comp_contDiffOn hR).add
    ((euclideanComplexInclusion.contDiff.comp_contDiffOn hI).const_smul Complex.I)).congr
  intro p hp
  have hbp : DifferentiableAt ℝ (fun x ↦ b (x, p.2)) p.1 :=
    (((hb.contDiffAt ((hU.prod hV).mem_nhds hp)).comp p.1
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  ext k
  apply Complex.ext
  · simp [completedVariationComplex_zero_re F hbp, bR]
  · simp [completedVariationComplex_zero_im F hbp, bI]

/-- The same joint reconstruction on an arbitrary open flow domain; no
product-domain extension is imposed (`app:ch_waves:eq:WKB-W`). -/
theorem contDiffOn_joint_completedVariationComplex_zero_of_isOpen {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N}
    {b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} {Ω : Set (Euclidean n × Z)}
    (hΩ : IsOpen Ω) (hspace : ∀ p ∈ Ω, p.1 ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b Ω)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞
      (fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1) Ω := by
  intro p hp
  obtain ⟨X, V, hX, hV, hx, hv, hsub⟩ := isOpen_prod_iff.mp hΩ p.1 p.2 hp
  have hXU : X ⊆ U := fun x hx ↦ hspace (x, p.2) (hsub ⟨hx, hv⟩)
  exact ((contDiffOn_joint_completedVariationComplex_zero hX hV (hF.mono hXU)
    (hb.mono hsub) (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx))).contDiffAt
      ((hX.prod hV).mem_nhds ⟨hx, hv⟩)).contDiffWithinAt

/-- Smooth phase and covectors give a smooth literal two-term wave with
all spectator parameters (`app:ch_waves:eq:WKB-u`). -/
theorem contDiffOn_joint_twoTermWave {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (lam : ℝ) {S : Euclidean n × Z → ℝ}
    {b₀ b₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin n)}
    {Ω : Set (Euclidean n × Z)}
    (hS : ContDiffOn ℝ ∞ S Ω) (hb₀ : ContDiffOn ℝ ∞ b₀ Ω)
    (hb₁ : ContDiffOn ℝ ∞ b₁ Ω) :
    ContDiffOn ℝ ∞ (fun p ↦ twoTermWave lam (fun x ↦ S (x, p.2))
      (fun x ↦ b₀ (x, p.2)) (fun x ↦ b₁ (x, p.2)) p.1) Ω := by
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hS)).cexp).smul
    ((hb₀.add (hb₁.const_smul ((lam : ℂ)⁻¹))).const_smul (((lam : ℂ)⁻¹)^2))

/-- Joint smoothness of the actual canonical WKB atom, without assuming
smoothness of its ambient reconstruction (`app:ch_waves:eq:WKB-W`). -/
theorem contDiffOn_canonicalAtom {F : Euclidean n → Euclidean N} (τ : ℝ)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hb₀ : ContDiffOn ℝ ∞ b₀ (U ×ˢ V)) (hb₁ : ContDiffOn ℝ ∞ b₁ (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (canonicalAtom F τ S b₀ b₁) (U ×ˢ V) := by
  exact contDiffOn_joint_completedVariationComplex_zero (F := F)
    (b := fun p ↦ twoTermWave τ⁻¹ (fun x ↦ S (x, p.2))
      (fun x ↦ b₀ (x, p.2)) (fun x ↦ b₁ (x, p.2)) p.1)
    hU hV hF (contDiffOn_joint_twoTermWave τ⁻¹ hS hb₀ hb₁) hi hrank

/-- The displacement polynomial is jointly smooth on the SAME chart.
The proof demodulates the already reconstructed atom; it does not assume
regularity of the differentiated coefficient formula
(`app:ch_waves:eq:exact-W-amplitude`). -/
theorem contDiffOn_canonicalDisplacementAmplitude {F : Euclidean n → Euclidean N}
    {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hb₀ : ContDiffOn ℝ ∞ b₀ (U ×ˢ V)) (hb₁ : ContDiffOn ℝ ∞ b₁ (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (canonicalDisplacementAmplitude F τ S b₀ b₁) (U ×ˢ V) := by
  have hc : ContDiffOn ℝ ∞ (fun p ↦ Complex.exp (-Complex.I * (S p / τ : ℝ)))
      (U ×ˢ V) :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (hS.div_const τ))).cexp
  apply (hc.smul (contDiffOn_canonicalAtom τ hU hV hF hi hrank hS hb₀ hb₁)).congr
  intro p hp
  have hd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × Euclidean (n - 1) → E} (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
      DifferentiableAt ℝ (fun y ↦ f (y, p.2)) p.1 :=
    (((hf.contDiffAt ((hU.prod hV).mem_nhds hp)).comp p.1
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  change canonicalDisplacementAmplitude F τ S b₀ b₁ p =
    Complex.exp (-Complex.I * (S p / τ : ℝ)) • canonicalAtom F τ S b₀ b₁ (p.1, p.2)
  rw [canonicalAtom_eq F hτ (hd hS) (hd hb₀) (hd hb₁), smul_smul, ← Complex.exp_add]
  simp

end JanetCartan.RawPrimary
