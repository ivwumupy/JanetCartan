module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Mean
import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Local all-order bounds for the actual carrier mean

The estimate `app:ch_background:eq:bg-Hsigma` of
`app:ch_background:prop:bg-normalized`. The smoothness of the mean is derived
by integration from the seed fields on their original open spatial/carrier
domains. A single cutoff extension, physical buffer, and scale interval work
for every derivative order. Equality on neighborhoods transfers all ambient
derivatives, including those at boundary points of the compact working set.

The measures and weights in the conclusion are exactly the input measures and
weights; in particular the measures may be literal Lebesgue carrier measures.
The consuming source-geometry construction must still supply its actual smooth
phase and normal fields. No global smoothness of those fields or their mean is
assumed here.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius Topology

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {A E Z F : Type} {n : ℕ} [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `app:ch_background:eq:bg-Hsigma`: the actual mean of compactly supported
smooth carrier data satisfies the local `O(ρ)` estimate at every spatial order.
The open physical buffer containing the prescribed compact set and the positive
scale interval are chosen before the order. The proof first integrates the seed
fields, then chooses one smooth extension near zero, and transfers the dilation
estimate by neighborhood equality. Nonnegativity of the weights is not needed
for this estimate (it is used separately for positivity of the limiting mean). -/
theorem exists_local_cNorm_normalizedCarrierMean_sub_zero_bounds
    (μ : A → Measure Z) (K V : A → Set Z) {U D : Set E}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hD : IsCompact D)
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a))
    (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    (hsupp : ∀ a z, z ∉ K a → w a z = 0) :
    ∃ W : Set E, IsOpen W ∧ D ⊆ W ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧
      (∀ ρ ∈ Icc (0 : ℝ) ρ₀, MapsTo (fun x ↦ ρ • x) W U) ∧
      ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ρ ∈ Icc (0 : ℝ) ρ₀,
        cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x -
          normalizedCarrierMean μ w ν ξ 0 x) ≤ C * ρ := by
  have hmean := contDiffOn_carrierMean_of_weight_support
    μ K V hU hV hK hKV w ν ξ hw hν hξ hsupp
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  have ha : 0 < d / 2 := by positivity
  have hclosed : Metric.closedBall (0 : E) (d / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hdU
  obtain ⟨H, hH, _, _, hext⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall 0 ha hU hclosed hmean
  have hH0 : H 0 = carrierMean μ w ν ξ 0 :=
    (hext 0 (Metric.mem_closedBall_self ha.le)).self_of_nhds
  obtain ⟨R, hR, hDR⟩ := hD.isBounded.exists_pos_norm_le
  let W : Set E := Metric.ball 0 (R + 1)
  have hW : IsOpen W := Metric.isOpen_ball
  have hDW : D ⊆ W := by
    intro x hx
    change dist x 0 < R + 1
    rw [dist_zero_right]
    linarith [hDR x hx]
  let ρ₀ : ℝ := min 1 ((d / 2) / (2 * (R + 1)))
  have hρ₀ : 0 < ρ₀ := lt_min zero_lt_one (by positivity)
  have hball (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) ρ₀) {x : E} (hx : x ∈ W) :
      ρ • x ∈ Metric.ball (0 : E) (d / 2) := by
    have hxnorm : ‖x‖ ≤ R + 1 := by
      have : dist x 0 < R + 1 := hx
      simpa only [dist_zero_right] using this.le
    have hscale : ρ * (2 * (R + 1)) ≤ d / 2 :=
      (le_div_iff₀ (by positivity)).mp (hρ.2.trans (min_le_right _ _))
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hρ.1]
    have := mul_le_mul_of_nonneg_left hxnorm hρ.1
    nlinarith
  refine ⟨W, hW, hDW, ρ₀, hρ₀, min_le_left _ _, ?_, ?_⟩
  · intro ρ hρ x hx
    exact hclosed (Metric.ball_subset_closedBall (hball ρ hρ hx))
  · intro s
    obtain ⟨C, hC, hbound⟩ := exists_cNorm_dilation_sub_const_bound hD hH s
    refine ⟨C, hC, ?_⟩
    intro ρ hρ
    have hnorm : cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x -
          normalizedCarrierMean μ w ν ξ 0 x) =
        cNorm D s (fun x ↦ H (ρ • x) - H 0) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hW.mem_nhds (hDW hx)] with y hy
      have hextρ := (hext (ρ • y)
        (Metric.ball_subset_closedBall (hball ρ hρ hy))).self_of_nhds
      rw [normalizedCarrierMean_zero, normalizedCarrierMean_eq_dilation, hextρ, hH0]
    rw [hnorm]
    exact hbound ρ ⟨hρ.1, hρ.2.trans (min_le_left _ _)⟩

end JanetCartan.NormalizedBackground.SourceGeometry
