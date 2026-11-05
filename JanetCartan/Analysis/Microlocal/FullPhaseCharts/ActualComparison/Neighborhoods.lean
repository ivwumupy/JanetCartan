module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes

/-!
# Closed cores inside the actual chart neighborhoods

The inverse-family consumer of `app:ch_seed:prop:seed-phase-charts` needs
compact convex cores contained in open parameter/data neighborhoods. These
are the literal centered boxes for `exists_actual_chart_comparison`; no
analytic estimates enter their construction.
-/

@[expose] public noncomputable section
open Set Metric

namespace JanetCartan.FullPhaseCharts.ActualComparison

/-- The closed full parameter box, including both epsilon endpoints
(`app:ch_seed:prop:seed-phase-charts`). -/
def fullParameterBox {n : ℕ} (z₀ : Euclidean 3) (r e : ℝ) :
    Set (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
      WithLp 2 (ℝ × Euclidean (n - 1))) :=
  Icc (-e) e ×ˢ closedBall (spectatorCenter z₀) r ×ˢ closedBall 0 r ×ˢ closedBall 0 r

/-- The closed transverse parameter box. A quarter-radius in time and each
transverse endpoint keeps both spacetime endpoints in the physical core
(`app:ch_seed:prop:seed-phase-charts`). -/
def transverseParameterBox {n : ℕ} (z₀ : Euclidean 3) (r e : ℝ) :
    Set (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) :=
  Icc (-e) e ×ˢ closedBall (spectatorCenter z₀) r ×ˢ closedBall 0 (r / 4) ×ˢ
    closedBall (z₀ 0) r ×ˢ closedBall 0 (r / 4) ×ˢ closedBall 0 (r / 4)

/-- The closed normalized-data box centered at the prescribed direction
(`app:ch_seed:prop:seed-phase-charts`). -/
def dataBox {n : ℕ} (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r : ℝ) :
    Set (ℝ × Euclidean (n - 1)) := closedBall (z₀ 0) r ×ˢ closedBall ηb r

/-- The full core is compact, convex, contains the base parameters, and has
an open enlargement past epsilon zero and endpoints
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullParameterBox_geometry {n : ℕ} (z₀ : Euclidean 3) {r e : ℝ}
    (hr : 0 < r) (he : 0 < e) :
    IsCompact (fullParameterBox (n := n) z₀ r e) ∧
    Convex ℝ (fullParameterBox (n := n) z₀ r e) ∧
    (0, spectatorCenter z₀, 0, 0) ∈ fullParameterBox (n := n) z₀ r e ∧
    fullParameterBox (n := n) z₀ r e ⊆ fullParameterSet z₀ (2 * r) (2 * e) := by
  refine ⟨isCompact_Icc.prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))),
    (convex_Icc _ _).prod ((convex_closedBall _ _).prod
      ((convex_closedBall _ _).prod (convex_closedBall _ _))), ?_, ?_⟩
  · exact ⟨⟨by linarith, he.le⟩, mem_closedBall_self hr.le,
      mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
  · intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      closedBall_subset_ball (by linarith) hq.2.1,
      closedBall_subset_ball (by linarith) hq.2.2.1,
      closedBall_subset_ball (by linarith) hq.2.2.2⟩

private theorem fixedTime_mem_double_ball {n : ℕ} {r t : ℝ}
    (hr : 0 < r) {y : Euclidean (n - 1)}
    (ht : t ∈ closedBall 0 (r / 4)) (hy : y ∈ closedBall 0 (r / 4)) :
    WithLp.toLp 2 (t,y) ∈ ball 0 (2 * r) := by
  have ht' : ‖t‖ ≤ r / 4 := by simpa using ht
  have hy' : ‖y‖ ≤ r / 4 := by simpa using hy
  have hn : ‖WithLp.toLp 2 (t,y)‖ ≤ ‖t‖ + ‖y‖ := by
    have hh := norm_add_le (WithLp.toLp 2 (t, (0 : Euclidean (n - 1))))
      (WithLp.toLp 2 ((0 : ℝ), y))
    have hid : WithLp.toLp 2 (t, (0 : Euclidean (n - 1))) +
        WithLp.toLp 2 ((0 : ℝ), y) = WithLp.toLp 2 (t,y) := by
      apply WithLp.ofLp_injective
      simp
    rw [hid] at hh
    simpa using hh
  rw [mem_ball, dist_zero_right]
  linarith

/-- The transverse core is compact, convex, contains the base parameters,
and lies inside the open neighborhood on which both spacetime endpoints
are admissible (`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseParameterBox_geometry {n : ℕ} (z₀ : Euclidean 3) {r e : ℝ}
    (hr : 0 < r) (he : 0 < e) :
    IsCompact (transverseParameterBox (n := n) z₀ r e) ∧
    Convex ℝ (transverseParameterBox (n := n) z₀ r e) ∧
    (0, spectatorCenter z₀, 0, z₀ 0, 0, 0) ∈ transverseParameterBox (n := n) z₀ r e ∧
    transverseParameterBox (n := n) z₀ r e ⊆ transverseParameterSet z₀ (2 * r) (2 * e) := by
  refine ⟨isCompact_Icc.prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))),
    (convex_Icc _ _).prod ((convex_closedBall _ _).prod
      ((convex_closedBall _ _).prod ((convex_closedBall _ _).prod
        ((convex_closedBall _ _).prod (convex_closedBall _ _))))), ?_, ?_⟩
  · exact ⟨⟨by linarith, he.le⟩, mem_closedBall_self hr.le,
      mem_closedBall_self (by positivity), mem_closedBall_self hr.le,
      mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  · intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      closedBall_subset_ball (by linarith) hq.2.1,
      closedBall_subset_ball (by linarith) hq.2.2.2.1,
      fixedTime_mem_double_ball hr hq.2.2.1 hq.2.2.2.2.1,
      fixedTime_mem_double_ball hr hq.2.2.1 hq.2.2.2.2.2⟩

/-- The normalized-data core is compact and convex, contains `(z₁,η_b)`,
and is strictly inside its open enlargement
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem dataBox_geometry {n : ℕ} (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    {r : ℝ} (hr : 0 < r) :
    IsCompact (dataBox z₀ ηb r) ∧ Convex ℝ (dataBox z₀ ηb r) ∧
    (z₀ 0, ηb) ∈ dataBox z₀ ηb r ∧ dataBox z₀ ηb r ⊆ dataSet z₀ ηb (2 * r) := by
  exact ⟨(isCompact_closedBall _ _).prod (isCompact_closedBall _ _),
    (convex_closedBall _ _).prod (convex_closedBall _ _),
    ⟨mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩,
    fun _ h ↦ ⟨closedBall_subset_ball (by linarith) h.1,
      closedBall_subset_ball (by linarith) h.2⟩⟩

end JanetCartan.FullPhaseCharts.ActualComparison
