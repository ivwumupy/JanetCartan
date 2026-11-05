module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Convergence of actual induced metrics

Section 9 (`main:sec:convergence`, after `main:eq:final-Cr`) passes to the limit
in the finite Gram matrix of the differential. These results use the existing
Frobenius topology on metric tensors. Existence of the map and derivative limits
is an explicit input; no correction sequence is constructed here.
-/

public noncomputable section

open Filter Set
open scoped ContDiff Topology Uniformity Matrix.Norms.Frobenius

namespace JanetCartan

private theorem comp_tendstoLocallyUniformlyOn_of_continuous
    {α β γ ι : Type*} [TopologicalSpace α] [UniformSpace β] [UniformSpace γ]
    {u : ι → α → β} {f : α → β} {g : β → γ} {l : Filter ι} {s : Set α}
    (hu : TendstoLocallyUniformlyOn u f l s) (hf : ContinuousOn f s)
    (hg : Continuous g) : TendstoLocallyUniformlyOn (fun j x ↦ g (u j x))
      (fun x ↦ g (f x)) l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hu ⊢
  intro x hx
  have h₁ : Tendsto (fun y : ι × α ↦ f y.2) (l ×ˢ 𝓝[s] x) (𝓝 (f x)) :=
    Tendsto.comp (hf x hx) tendsto_snd
  have h₂ := h₁.congr_uniformity (hu x hx)
  exact (tendsto_right_nhds_uniformity.comp (hg.continuousAt.tendsto.comp h₁)).uniformity_trans
    (tendsto_left_nhds_uniformity.comp (hg.continuousAt.tendsto.comp h₂))

/-- Section 9, `main:sec:convergence`: the finite Gram matrix depends continuously
on a differential in operator norm, with the Frobenius topology on its output. -/
theorem continuous_gramMatrix_differential {n N : ℕ} :
    Continuous (fun L : Euclidean n →L[ℝ] Euclidean N ↦
      (fun i j ↦ inner ℝ (L (EuclideanSpace.single i 1))
        (L (EuclideanSpace.single j 1)) : MetricTensor n)) := by
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_eval_const _).inner (continuous_eval_const _)

/-- Section 9 after `main:eq:final-Cr`: convergence of actual differentials
implies convergence of the induced metric at a point. -/
theorem tendsto_inducedMetric_of_tendsto_fderiv {n N : ℕ} {ι : Type*} {l : Filter ι}
    {M : ι → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {x : Euclidean n}
    (h : Tendsto (fun j ↦ fderiv ℝ (M j) x) l (𝓝 (fderiv ℝ F x))) :
    Tendsto (fun j ↦ inducedMetric (M j) x) l (𝓝 (inducedMetric F x)) :=
  (continuous_gramMatrix_differential (n := n) (N := N)).continuousAt.tendsto.comp h

/-- Section 9 after `main:eq:final-Cr`: locally uniform derivative convergence
passes through the induced metric, when the limiting differential is continuous. -/
theorem tendstoLocallyUniformlyOn_inducedMetric_of_fderiv
    {n N : ℕ} {ι : Type*} {l : Filter ι}
    {M : ι → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hF : ContinuousOn (fderiv ℝ F) s)
    (h : TendstoLocallyUniformlyOn (fun j ↦ fderiv ℝ (M j)) (fderiv ℝ F) l s) :
    TendstoLocallyUniformlyOn (fun j ↦ inducedMetric (M j)) (inducedMetric F) l s := by
  have hg := continuous_gramMatrix_differential (n := n) (N := N)
  have hc := comp_tendstoLocallyUniformlyOn_of_continuous h hF hg
  exact hc

/-- Section 9, `main:sec:convergence`: a local C¹ limit has locally uniformly
convergent induced metrics. The convergence of maps themselves is unnecessary
for this implication once convergence to the differential of `F` is known. -/
theorem tendstoLocallyUniformlyOn_inducedMetric_of_contDiffOn
    {n N : ℕ} {ι : Type*} {l : Filter ι}
    {M : ι → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hs : IsOpen s) (hF : ContDiffOn ℝ 1 F s)
    (h : TendstoLocallyUniformlyOn (fun j ↦ fderiv ℝ (M j)) (fderiv ℝ F) l s) :
    TendstoLocallyUniformlyOn (fun j ↦ inducedMetric (M j)) (inducedMetric F) l s :=
  tendstoLocallyUniformlyOn_inducedMetric_of_fderiv
    (hF.continuousOn_fderiv_of_isOpen hs le_rfl) h

/-- Section 9 after `main:eq:final-Cr`: local C¹ convergence gives uniform
Frobenius convergence of the metrics on every compact subset of the domain. -/
theorem tendstoUniformlyOn_inducedMetric_of_isCompact
    {n N : ℕ} {ι : Type*} {l : Filter ι}
    {M : ι → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {s K : Set (Euclidean n)} (hs : IsOpen s) (hF : ContDiffOn ℝ 1 F s)
    (h : TendstoLocallyUniformlyOn (fun j ↦ fderiv ℝ (M j)) (fderiv ℝ F) l s)
    (hK : IsCompact K) (hKs : K ⊆ s) :
    TendstoUniformlyOn (fun j ↦ inducedMetric (M j)) (inducedMetric F) l K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    ((tendstoLocallyUniformlyOn_inducedMetric_of_contDiffOn hs hF h).mono hKs)

end JanetCartan
