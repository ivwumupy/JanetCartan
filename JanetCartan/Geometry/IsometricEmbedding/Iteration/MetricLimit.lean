module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricLimit.Convergence
public import JanetCartan.Geometry.IsometricEmbedding.Local
public import JanetCartan.Analysis.Iteration.SmoothLimit

/-!
# The metric equation and local embedding at the limit

The final paragraph of Section 9 (`main:sec:convergence`) of `paper.tex`:
derivative convergence and a vanishing metric defect give an isometric map;
positive definiteness gives immersion; `Local` supplies one smaller neighborhood
on which the map is an embedding.

The limit map, its regularity, derivative convergence, and defect decay are explicit
inputs. The series corollary instead takes summable eventual derivative bounds and
uses the existing smooth-series theorem. None of these statements constructs the
correction sequence or establishes its analytic estimates in `main:eq:final-Cr`.
-/

public noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan

/-- Section 9, `main:sec:convergence`: a vanishing defect and convergence to the
actual differential of the limit imply the metric equation. -/
theorem isIsometricOn_of_tendsto_fderiv_of_tendsto_metricDefect
    {n N : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {M : ι → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)}
    (hderiv : ∀ x ∈ s,
      Tendsto (fun j ↦ fderiv ℝ (M j) x) l (𝓝 (fderiv ℝ F x)))
    (hdefect : ∀ x ∈ s,
      Tendsto (fun j ↦ g x - inducedMetric (M j) x) l (𝓝 0)) :
    IsIsometricOn g F s := by
  intro x hx
  have h := (tendsto_const_nhds (x := g x)).sub
    (tendsto_inducedMetric_of_tendsto_fderiv (hderiv x hx))
  exact (sub_eq_zero.mp (tendsto_nhds_unique h (hdefect x hx))).symm

/-- Section 9, `main:eq:metric-induction`: an eventual scalar error bound tending
to zero suffices for the metric equation, with the manuscript's defect sign. -/
theorem isIsometricOn_of_tendsto_fderiv_of_metric_error
    {n N : ℕ} {M : ℕ → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)} {ε : ℕ → ℝ}
    (hderiv : ∀ x ∈ s,
      Tendsto (fun j ↦ fderiv ℝ (M j) x) atTop (𝓝 (fderiv ℝ F x)))
    (hε : Tendsto ε atTop (𝓝 0))
    (herror : ∀ᶠ j in atTop, ∀ x ∈ s, ‖g x - inducedMetric (M j) x‖ ≤ ε j) :
    IsIsometricOn g F s := by
  apply isIsometricOn_of_tendsto_fderiv_of_tendsto_metricDefect hderiv
  intro x hx
  apply tendsto_zero_iff_norm_tendsto_zero.2
  exact squeeze_zero' (Eventually.of_forall (fun j ↦ norm_nonneg _))
    (herror.mono (fun j hj ↦ hj x hx)) hε

/-- Section 9, `main:sec:convergence`: positive definiteness converts the limiting
metric equation into injectivity of the actual differential throughout the domain. -/
theorem isIsometricOn_and_isImmersionOn_of_metric_limit
    {n N : ℕ} {M : ℕ → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)} {ε : ℕ → ℝ}
    (hg : ∀ x ∈ s, (g x).PosDef)
    (hderiv : ∀ x ∈ s,
      Tendsto (fun j ↦ fderiv ℝ (M j) x) atTop (𝓝 (fderiv ℝ F x)))
    (hε : Tendsto ε atTop (𝓝 0))
    (herror : ∀ᶠ j in atTop, ∀ x ∈ s, ‖g x - inducedMetric (M j) x‖ ≤ ε j) :
    IsIsometricOn g F s ∧ IsImmersionOn F s := by
  have hmetric := isIsometricOn_of_tendsto_fderiv_of_metric_error hderiv hε herror
  exact ⟨hmetric, isImmersionOn_of_isIsometricOn hg hmetric⟩

/-- Section 9, final paragraph (`main:thm:main`): a smooth limit with converging
derivatives and vanishing metric defect is a smooth isometric embedding after
one restriction. The neighborhood is independent of derivative order. -/
theorem exists_local_embedding_of_metric_limit
    {n N : ℕ} {M : ℕ → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)} {p : Euclidean n} {ε : ℕ → ℝ}
    (hs : IsOpen s) (hp : p ∈ s) (hF : ContDiffOn ℝ ∞ F s)
    (hg : ∀ x ∈ s, (g x).PosDef)
    (hderiv : ∀ x ∈ s,
      Tendsto (fun j ↦ fderiv ℝ (M j) x) atTop (𝓝 (fderiv ℝ F x)))
    (hε : Tendsto ε atTop (𝓝 0))
    (herror : ∀ᶠ j in atTop, ∀ x ∈ s, ‖g x - inducedMetric (M j) x‖ ≤ ε j) :
    IsIsometricOn g F s ∧ IsImmersionOn F s ∧
      ∃ U : Opens (Euclidean n), p ∈ U ∧ (U : Set (Euclidean n)) ⊆ s ∧
        ContDiffOn ℝ ∞ F U ∧ Topology.IsEmbedding (fun x : U ↦ F x.val) ∧
        IsIsometricOn g F U := by
  obtain ⟨hmetric, himm⟩ := isIsometricOn_and_isImmersionOn_of_metric_limit hg hderiv hε herror
  exact ⟨hmetric, himm, exists_local_embedding_of_isIsometricOn hs hp hF hg hmetric⟩

/-- Section 9 after `main:eq:final-Cr`: summable eventual bounds for every
derivative of the increments and a vanishing stage defect yield one smooth
isometric limit and a local embedding. All summability and defect inputs remain
explicit; the smooth-series construction is supplied by `SmoothLimit`. -/
theorem exists_local_embedding_series_of_metric_error
    {n N : ℕ} {G : Euclidean n → Euclidean N}
    {f : ℕ → Euclidean n → Euclidean N} {v : ℕ → ℕ → ℝ}
    {g : MetricField n} {s : Set (Euclidean n)} {p : Euclidean n} {ε : ℕ → ℝ}
    (hs : IsOpen s) (hp : p ∈ s) (hg : ∀ x ∈ s, (g x).PosDef)
    (hG : ContDiff ℝ ∞ G) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j)
    (hε : Tendsto ε atTop (𝓝 0))
    (herror : ∀ J, ∀ x ∈ s,
      ‖inducedMetric (fun y ↦ G y + ∑ j ∈ Finset.range J, f j y) x - g x‖ ≤ ε J) :
    let F := fun x ↦ G x + ∑' j, f j x
    ContDiff ℝ ∞ F ∧ IsIsometricOn g F s ∧ IsImmersionOn F s ∧
      ∃ U : Opens (Euclidean n), p ∈ U ∧ (U : Set (Euclidean n)) ⊆ s ∧
        ContDiffOn ℝ ∞ F U ∧ Topology.IsEmbedding (fun x : U ↦ F x.val) ∧
        IsIsometricOn g F U := by
  dsimp only
  have hF := (smooth_limit_of_eventual_bounds hG hf hv hb).1
  have hmetric := isIsometricOn_series_of_metric_error hG hf hv hb hε herror
  exact ⟨hF, hmetric, isImmersionOn_of_isIsometricOn hg hmetric,
    exists_local_embedding_of_isIsometricOn hs hp hF.contDiffOn hg hmetric⟩

end JanetCartan
