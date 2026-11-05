module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# An interval of compatible reference source scales

For `main:prop:seed` and `main:prop:current-scale`, the quotient construction
needs its low frame neighborhood at every sufficiently small source scale.
This permits the initializer to impose additional finite coefficient margins
without replacing the reference used by the current-map construction.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FixedReferenceProfiles

open ProjectedStressFrame

/-- The low frame margin of `app:ch_seed:setup:seed-current` holds on an entire
positive source-scale interval. Its consumer is
`exists_source_scale_cap_for_fixed_reference_history_profiles`: the cap is
chosen before the history orders and the initializer may choose any smaller
positive scale to meet its additional full-array margins. -/
theorem exists_source_scale_interval_projectedStress_lt {n : ℕ}
    (G₀ : FlatReference n) {K : Set (Euclidean n)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ cap → ∀ i,
        cNorm K 6 (fun x ↦ projectedStress (sourceDilation G₀.map σ) x i -
          cubeStress n i) < ε := by
  obtain ⟨_, _, _, σ₀, hσ₀, hσ₁, _, _, hb⟩ :=
    exists_projectedStress_dilation_bounds G₀ hK
  obtain ⟨C, hC, hbound⟩ := hb 6
  refine ⟨min σ₀ (ε / (2 * C)), lt_min hσ₀ (by positivity),
    (min_le_left _ _).trans hσ₁, ?_⟩
  intro σ hσ hcap i
  have hsmall : C * σ < ε := by
    have := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (hcap.trans (min_le_right _ _))
    nlinarith
  exact (hbound σ ⟨hσ, hcap.trans (min_le_left _ _)⟩ i).trans_lt hsmall

/-- Map equality transfers the outer carrier geometry in `main:prop:seed`.
The initialized record may have a much smaller working chart. Only the
original analytic source's chart must contain the carrier ball; there is no
comparison with `G.domain.chartRadius`. This is the domain transfer used when
applying the history profiles to the initialized reference. -/
theorem fixed_reference_outer_geometry {n : ℕ} (G₀ G : FlatReference n)
    {σ R : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (hmap : G.map = sourceDilation G₀.map σ) (hR : R < G₀.domain.chartRadius) :
    IsImmersionOn G.map (ball 0 R) ∧ HasFullNormalRankOn G.map (ball 0 R) ∧
      ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 R) := by
  let H := sourceDilationReference G₀ hσ hσ₁
  have hmaps : G.map = H.map := hmap
  have hi : IsImmersionOn H.map (ball 0 R) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map (ball 0 R) := by
    intro x hx
    apply H.fullNormalRank x
    exact (ball_subset_ball hR.le) hx
  rw [hmaps]
  exact ⟨hi, hrank,
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball H.contDiff.contDiffOn hi hrank)⟩

end JanetCartan.FixedReferenceProfiles
