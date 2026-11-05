module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Fields
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame

/-!
# Closing the flat seed's geometric inputs

The seed in `app:ch_background:prop:bg-normalized` is the actual `FlatReference`
constructed by `Reference.Construction`. Its center stress basis is a conclusion
of its exact cube stress identity, rather than an additional assumption on the
normalized family. The normalized second form and normal completion below are
the literal fields of this same reference. No rank assertion is made at scale zero.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.NormalRankStability

namespace JanetCartan.NormalizedBackground
open ProjectedStressFrame SourceGeometry AmbientResponse

/-- Discharge the center-basis input of
`SourceGeometry.exists_sourcePrincipalMean_and_phase_bounds` for the actual
flat seed (`app:ch_background:prop:bg-normalized`). -/
theorem flatReference_projectedStress_basis {n : ℕ} (hn : 5 ≤ n)
    (G : FlatReference n) :
    ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap G.map 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress G.map 0 i := by
  obtain ⟨ε, hε, _, _, hb⟩ := exists_projectedStress_basis_neighborhood hn
  have h0 : (0 : Euclidean n) ∈ G.domain.chart n :=
    mem_ball_self (G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius)
  have hi : IsImmersionOn G.map (G.domain.chart n) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ G.inducedMetric_eq_one x)
  exact (hb G.map 0 (G.contDiff.contDiffAt.of_le (by simp)) (hi 0 h0)
    (G.fullNormalRank 0 h0) (by simpa only [projectedStress_flatReference_zero,
      sub_self, norm_zero, Finset.sum_const_zero] using hε)).1

/-- The actual seed supplies smooth extension of both normalized geometric
inverse factors in `app:ch_background:eq:bg-Nsigma`. Their agreement with the
positive-scale geometry is derived from source dilation. -/
theorem flatReference_normalized_geometric_extensions {n : ℕ} (G : FlatReference n) :
    (∀ i j : Fin n,
      ContDiffOn ℝ ∞ (fun q : ℝ × Euclidean n ↦
        secondFundamentalForm G.map (q.1 • q.2) i j)
        {q | q.1 • q.2 ∈ G.domain.chart n} ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x : Euclidean n,
        ρ⁻¹ • secondFundamentalForm (sourceDilation G.map ρ) x i j =
          secondFundamentalForm G.map (ρ • x) i j) ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × Euclidean n ↦
      (canonicalNormalCompletion G.map (q.1 • q.2)).toContinuousLinearMap)
      {q | q.1 • q.2 ∈ G.domain.chart n} ∧
    ∀ ρ : ℝ, 0 < ρ → ∀ x : Euclidean n, ρ • x ∈ G.domain.chart n →
      ρ • (canonicalNormalCompletion (sourceDilation G.map ρ) x).toContinuousLinearMap =
        (canonicalNormalCompletion G.map (ρ • x)).toContinuousLinearMap := by
  have hi : IsImmersionOn G.map (G.domain.chart n) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ G.inducedMetric_eq_one x)
  exact ⟨fun i j ↦ normalized_secondFundamentalForm_extension isOpen_ball G.contDiff hi i j,
    normalized_canonicalNormalCompletion_extension isOpen_ball G.contDiff hi G.fullNormalRank⟩

/-- Common scale and physical buffer for every mixed derivative of the actual
seed's normalized second form and canonical completion. This supplies the
geometric-factor bounds in `app:ch_background:prop:bg-normalized` before any
carrier weights, target metric, accuracy or history is chosen. -/
theorem exists_flatReference_normalized_factor_bounds {n : ℕ} (G : FlatReference n)
    {D : Set (Euclidean n)} (hD : IsCompact D) :
    let J := fun q : ℝ × Euclidean n ↦
      (secondFundamentalForm G.map (q.1 • q.2),
        (canonicalNormalCompletion G.map (q.1 • q.2)).toContinuousLinearMap)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      (∀ σ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, σ • x ∈ G.domain.chart n) ∧
      ContDiffOn ℝ ∞ J (Ioo (-2 * r) (2 * r) ×ˢ B) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ σ ∈ Icc (0 : ℝ) r, ∀ x ∈ D,
        ‖iteratedFDeriv ℝ s J (σ, x)‖ ≤ C := by
  let J := fun q : ℝ × Euclidean n ↦
    (secondFundamentalForm G.map (q.1 • q.2),
      (canonicalNormalCompletion G.map (q.1 • q.2)).toContinuousLinearMap)
  have h0 : (0 : Euclidean n) ∈ G.domain.chart n :=
    mem_ball_self (G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius)
  obtain ⟨B, hB, hDB, r₀, hr₀, hseg⟩ := exists_source_phase_buffer isOpen_ball h0 hD
  let r := min r₀ 1
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hmaps (σ : ℝ) (hσ : σ ∈ Ioo (-2 * r) (2 * r)) (x) (hx : x ∈ B) :
      σ • x ∈ G.domain.chart n := by
    simpa only [one_mul, LocalDomain.chart] using hseg σ ⟨by linarith [hσ.1, min_le_left r₀ 1],
      by linarith [hσ.2, min_le_left r₀ 1]⟩ x hx 1 ⟨by norm_num, by norm_num⟩
  have hg := flatReference_normalized_geometric_extensions G
  have hJ : ContDiffOn ℝ ∞ J (Ioo (-2 * r) (2 * r) ×ˢ B) :=
    ((contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦ (hg.1 i j).1).prodMk hg.2.1).mono
      (fun q hq ↦ hmaps q.1 hq.1 q.2 hq.2)
  refine ⟨B, hB, hDB, r, hr, min_le_right _ _, hmaps, hJ, ?_⟩
  intro s
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hD).exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hJ (isOpen_Ioo.prod hB) (by simp)).mono
      (show Icc (0 : ℝ) r ×ˢ D ⊆ Ioo (-2 * r) (2 * r) ×ˢ B from by
        intro q hq
        exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hDB hq.2⟩))
  exact ⟨|C| + 1, by positivity, fun σ hσ x hx ↦
    (hC (σ, x) ⟨hσ, hx⟩).trans ((le_abs_self C).trans (by linarith))⟩

end JanetCartan.NormalizedBackground
