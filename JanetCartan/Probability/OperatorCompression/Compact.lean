module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Norm convergence of compact compressions

The compactness step in `app:ch_waves:thm:sampling` of `paper.tex`.
The projections may be replaced by any strongly convergent self-adjoint contractions.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology InnerProduct

namespace JanetCartan.OperatorCompression

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- Two-sided compression, as used in `app:ch_waves:thm:sampling`. -/
def compress (P T : H →L[𝕜] H) : H →L[𝕜] H := P ∘L T ∘L P

/-- Strongly convergent contractions converge uniformly on a compact set
(`app:ch_waves:thm:sampling`, compactness step). -/
theorem eventually_uniform_on_compact
    (P : ℕ → H →L[𝕜] H) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖P n x - x‖ < ε := by
  obtain ⟨s, _, hs, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 4 by positivity)
  have hcenters : ∀ᶠ n in atTop, ∀ y ∈ s, ‖P n y - y‖ < ε / 2 := by
    apply hs.eventually_all.mpr
    intro y _
    simpa only [dist_eq_norm] using
      ((hstrong y).eventually (Metric.ball_mem_nhds y (show 0 < ε / 2 by positivity)))
  filter_upwards [hcenters] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x - y‖ < ε / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have hbound : ‖P n (x - y)‖ ≤ ‖x - y‖ :=
    ((P n).le_opNorm (x - y)).trans
      (by simpa using mul_le_mul_of_nonneg_right (hP n) (norm_nonneg (x - y)))
  calc
    ‖P n x - x‖ = ‖P n (x - y) + (P n y - y) + (y - x)‖ := by
      congr 1
      simp only [map_sub]
      abel
    _ ≤ ‖P n (x - y)‖ + ‖P n y - y‖ + ‖y - x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε := by rw [norm_sub_rev y x]; linarith [hn y hy]

/-- Strong convergence becomes operator-norm convergence after a compact operator
(`app:ch_waves:thm:sampling`). -/
theorem tendsto_compact_left
    (P : ℕ → H →L[𝕜] H) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (T : H →L[𝕜] H) (hT : IsCompactOperator T) :
    Tendsto (fun n ↦ P n ∘L T) atTop (𝓝 T) := by
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact 1
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hu := eventually_uniform_on_compact P hP hstrong hK
    (show 0 < ε / 2 by positivity)
  apply eventually_atTop.mp
  filter_upwards [hu] with n hn
  rw [dist_eq_norm]
  have hnorm : ‖P n ∘L T - T‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    exact (hn (T x) (hTK ⟨x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx.le,
      rfl⟩)).le
  linarith

variable [CompleteSpace H]

/-- Compact self-adjoint operators converge in norm under two-sided strongly
convergent self-adjoint contractions (`app:ch_waves:thm:sampling`). -/
theorem tendsto_compress
    (P : ℕ → H →L[𝕜] H) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hsa : ∀ n, IsSelfAdjoint (P n))
    (hstrong : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (T : H →L[𝕜] H) (hT : IsCompactOperator T) (hTsa : IsSelfAdjoint T) :
    Tendsto (fun n ↦ compress (P n) T) atTop (𝓝 T) := by
  have hleft := tendsto_compact_left P hP hstrong T hT
  have hright : Tendsto (fun n ↦ T ∘L P n) atTop (𝓝 T) := by
    have h := ContinuousLinearMap.adjoint.continuous.tendsto T |>.comp hleft
    simpa only [Function.comp_def, ContinuousLinearMap.adjoint_comp,
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp hTsa),
      fun n ↦ ContinuousLinearMap.isSelfAdjoint_iff'.mp (hsa n)] using h
  have hsum : Tendsto (fun n ↦ ‖T ∘L P n - T‖ + ‖P n ∘L T - T‖) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hright).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hleft)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  have hid : compress (P n) T - T =
      P n ∘L (T ∘L P n - T) + (P n ∘L T - T) := by
    simp only [compress, ContinuousLinearMap.comp_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hP n))) le_rfl)

end JanetCartan.OperatorCompression
