module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Kernel.LinearAlgebra
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.TensorFrame
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.MeanBounds
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import JanetCartan.Analysis.ContDiff.Norm.Basic
import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# The compact reduced source of the positive background

The source `-θ q_G(R₀)/2` in `app:ch_background:eq:bg-current-raising`.
Reduction uses the existing Frobenius tensor contraction. For a normalized
seed, smoothness of the original carrier integral and the dilation estimate
give a smooth compact source of size `O_s(ρ)`. The same cutoff and scale
interval work for all orders; the density and inverse are not assumed here.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PositiveBackground

variable {n : ℕ}

/-- The paper's actual reduced source, with the factor `-1/2` and original
physical source cutoff (`app:ch_background:eq:bg-current-raising`). -/
def cutReducedSource (θ : Euclidean n → ℝ)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n) :
    Euclidean n → Euclidean n :=
  fun x ↦ (- (1 / 2 : ℝ) * θ x) • WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x))

/-- The compact source has no support outside the preselected source cutoff
(`app:ch_background:eq:bg-current-raising`). -/
theorem cutReducedSource_tsupport (θ : Euclidean n → ℝ)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n) :
    tsupport (cutReducedSource θ Q R) ⊆ tsupport θ := by
  apply closure_mono
  intro x hx hθ
  exact hx (by simp [cutReducedSource, hθ])

/-- The smooth source is zero-extended by the SAME cutoff, without any
smoothness requirement outside its support (`app:ch_background:eq:bg-current-raising`). -/
theorem contDiff_cutReducedSource {θ : Euclidean n → ℝ}
    {Q : Euclidean n → Fin n → MetricTensor n} {R : MetricField n}
    {U : Set (Euclidean n)} (hU : IsOpen U) (hθ : ContDiff ℝ ∞ θ)
    (hsupp : tsupport θ ⊆ U) (hQ : ContDiffOn ℝ ∞ Q U)
    (hR : ContDiffOn ℝ ∞ R U) : ContDiff ℝ ∞ (cutReducedSource θ Q R) := by
  have hred : ContDiffOn ℝ ∞
      (fun x ↦ WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x))) U := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    exact hR.inner ℝ ((contDiffOn_pi.mp hQ) i)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport θ
  · exact (contDiffAt_const.mul hθ.contDiffAt).smul
      (hred.contDiffAt (hU.mem_nhds (hsupp hx)))
  · apply (contDiffAt_const (c := (0 : Euclidean n))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [cutReducedSource, hy]

/-- The actual compact physical source has a smooth representative on the
unit torus, with every physical jet unchanged inside its cell
(`app:ch_background:eq:bg-current-raising`). -/
theorem cutReducedSource_periodic {θ : Euclidean n → ℝ}
    {Q : Euclidean n → Fin n → MetricTensor n} {R : MetricField n}
    {U : Set (Euclidean n)} {r : ℝ} (hr : r < 1 / 2)
    (hU : IsOpen U) (hθ : ContDiff ℝ ∞ θ)
    (hsupp : tsupport θ ⊆ U) (hbox : tsupport θ ⊆ {x | ∀ i, |x i| ≤ r})
    (hQ : ContDiffOn ℝ ∞ Q U) (hR : ContDiffOn ℝ ∞ R U) :
    IsSmoothPeriodic (UniformStep.Periodization.vectorPeriodization
      (cutReducedSource θ Q R)) ∧
      ∀ x ∈ fundamentalCell n,
        periodicLift (UniformStep.Periodization.vectorPeriodization
          (cutReducedSource θ Q R)) =ᶠ[nhds x] cutReducedSource θ Q R := by
  have hs := (cutReducedSource_tsupport θ Q R).trans hbox
  exact ⟨UniformStep.Periodization.isSmoothPeriodic_vectorPeriodization hr hs
    (contDiff_cutReducedSource hU hθ hsupp hQ hR),
    fun _ hx ↦ UniformStep.Periodization.vectorPeriodization_eventuallyEq hr hs hx⟩

private theorem exists_cutReducedSource_dilation_bounds
    {U : Set (Euclidean n)} (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    {Q : Euclidean n → Fin n → MetricTensor n} {H : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q U) (hH : ContDiffOn ℝ ∞ H U)
    {r : ℝ} (hr : 0 < r) {θ : Euclidean n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hsupp : tsupport θ ⊆ closedBall 0 r) :
    ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
      (∀ ρ ∈ Icc (0 : ℝ) ρ₀, MapsTo (fun x ↦ ρ • x) (closedBall 0 r) U ∧
        ContDiff ℝ ∞ (cutReducedSource θ (fun x ↦ Q (ρ • x))
          (fun x ↦ H (ρ • x) - H 0))) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Icc (0 : ℝ) ρ₀,
        cNorm (closedBall 0 r) s (cutReducedSource θ (fun x ↦ Q (ρ • x))
          (fun x ↦ H (ρ • x) - H 0)) ≤ C * ρ := by
  let f : Euclidean n → Euclidean n := fun x ↦
    WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (H x - H 0))
  have hf : ContDiffOn ℝ ∞ f U := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    exact (hH.sub contDiffOn_const).inner ℝ ((contDiffOn_pi.mp hQ) i)
  have hf0 : f 0 = 0 := by simp [f]
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  have hclosed : closedBall (0 : Euclidean n) (d / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hdU
  obtain ⟨g, hg, _, _, hext⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall 0
      (half_pos hd) hU hclosed hf
  have hg0 : g 0 = 0 :=
    ((hext 0 (mem_closedBall_self (half_pos hd).le)).self_of_nhds).trans hf0
  let ρ₀ := min 1 ((d / 2) / (r + 1))
  have hρ₀ : 0 < ρ₀ := lt_min zero_lt_one (by positivity)
  have hball (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) ρ₀)
      {x : Euclidean n} (hx : x ∈ closedBall 0 r) :
      ρ • x ∈ closedBall (0 : Euclidean n) (d / 2) := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
    have hscale := (le_div_iff₀ (by positivity : 0 < r + 1)).mp
      (hρ.2.trans (min_le_right _ _))
    have hxnorm := mem_closedBall_zero_iff.mp hx
    nlinarith [mul_le_mul_of_nonneg_left hxnorm hρ.1]
  let a : Euclidean n → ℝ := fun x ↦ - (1 / 2 : ℝ) * θ x
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul hθ
  have hgsmooth (ρ : ℝ) : ContDiff ℝ ∞ (fun x : Euclidean n ↦ g (ρ • x) - g 0) :=
    (hg.comp (contDiff_id.const_smul ρ)).sub contDiff_const
  have heq (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) ρ₀) :
      cutReducedSource θ (fun x ↦ Q (ρ • x)) (fun x ↦ H (ρ • x) - H 0) =
        fun x ↦ a x • (g (ρ • x) - g 0) := by
    funext x
    by_cases hx : θ x = 0
    · simp [cutReducedSource, a, hx]
    · have he := (hext (ρ • x) (hball ρ hρ (hsupp (subset_tsupport θ hx)))).self_of_nhds
      rw [hg0, sub_zero, he]
      rfl
  refine ⟨ρ₀, hρ₀, min_le_left _ _, ?_, ?_⟩
  · intro ρ hρ
    refine ⟨fun x hx ↦ hclosed (hball ρ hρ hx), ?_⟩
    rw [heq ρ hρ]
    exact ha.smul (hgsmooth ρ)
  · intro s
    obtain ⟨C, hC, hbound⟩ := exists_cNorm_dilation_sub_const_bound (isCompact_closedBall 0 r) hg s
    let M := (2 : ℝ) ^ s * cNorm (closedBall 0 r) s a
    have hM : 0 ≤ M := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
    refine ⟨M * C + 1, by positivity, ?_⟩
    intro ρ hρ
    rw [heq ρ hρ]
    have hprod := cNorm_smul_le (r := s) (isCompact_closedBall 0 r)
      (ha.of_le (by simp)) ((hgsmooth ρ).of_le (by simp))
    calc
      _ ≤ M * cNorm (closedBall 0 r) s (fun x ↦ g (ρ • x) - g 0) := hprod
      _ ≤ M * (C * ρ) := mul_le_mul_of_nonneg_left
        (hbound ρ ⟨hρ.1, hρ.2.trans (min_le_left _ _)⟩) hM
      _ ≤ (M * C + 1) * ρ := by nlinarith [hρ.1]

/-- The normalized compact reduced source is smooth and `O_s(ρ)` for the
literal carrier mean and unchanged measure
(`app:ch_background:eq:bg-current-raising`, `app:ch_background:eq:bg-positive-profile`).
Smoothness of the integral and the source bound are proved from the seed
fields. The actual projected stress is substituted using its source-dilation
identity; no density, inverse, or successful positive background is assumed. -/
theorem exists_normalized_cutReducedSource_bounds
    {A Z F : Type} [Fintype A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (μ : A → Measure Z) (K V : A → Set Z) {U : Set (Euclidean n)}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → Euclidean n × Z → F)
    (ξ : A → Euclidean n × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    (hwSupport : ∀ a z, z ∉ K a → w a z = 0)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q U)
    {r : ℝ} (hr : 0 < r) {θ : Euclidean n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hsupp : tsupport θ ⊆ closedBall 0 r) :
    ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
      (∀ ρ ∈ Icc (0 : ℝ) ρ₀, MapsTo (fun x ↦ ρ • x) (closedBall 0 r) U ∧
        ContDiff ℝ ∞ (cutReducedSource θ (fun x ↦ Q (ρ • x))
          (fun x ↦ NormalizedBackground.normalizedCarrierMean μ w ν ξ ρ x -
            NormalizedBackground.normalizedCarrierMean μ w ν ξ 0 x))) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Icc (0 : ℝ) ρ₀,
        cNorm (closedBall 0 r) s (cutReducedSource θ (fun x ↦ Q (ρ • x))
          (fun x ↦ NormalizedBackground.normalizedCarrierMean μ w ν ξ ρ x -
            NormalizedBackground.normalizedCarrierMean μ w ν ξ 0 x)) ≤ C * ρ := by
  have hmean := NormalizedBackground.SourceGeometry.contDiffOn_carrierMean_of_weight_support
    μ K V hU hV hK hKV w ν ξ hw hν hξ hwSupport
  simpa only [NormalizedBackground.normalizedCarrierMean_eq_dilation,
    NormalizedBackground.normalizedCarrierMean_zero, zero_smul] using
    exists_cutReducedSource_dilation_bounds hU h0 hQ hmean hr hθ hsupp

end JanetCartan.PositiveBackground
