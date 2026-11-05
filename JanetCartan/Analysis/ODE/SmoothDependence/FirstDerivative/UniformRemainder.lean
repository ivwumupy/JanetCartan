module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform first-order remainders along compact trajectories

The flow differentiation argument for
`app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase` needs a Taylor remainder uniform along a
compact trajectory. Compactness is required only of the trajectory, not of
balls in the ambient Banach space.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the first-order Taylor
remainder of a `C¹` map is uniformly small at base points in a compact subset
of its open domain. The second point need not lie in the compact set. -/
theorem exists_uniform_fderiv_remainder {f : E → F} {U C : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hC : IsCompact C) (hCU : C ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ C, ∀ y, dist y z < δ →
      ‖f y - f z - fderiv ℝ f z (y - z)‖ ≤ ε * ‖y - z‖ := by
  have hD := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  apply hC.induction_on
    (p := fun S ↦ ∃ δ > 0, ∀ z ∈ S, ∀ y, dist y z < δ →
      ‖f y - f z - fderiv ℝ f z (y - z)‖ ≤ ε * ‖y - z‖)
  · exact ⟨1, zero_lt_one, by simp⟩
  · intro S T hST ⟨δ, hδ, hb⟩
    exact ⟨δ, hδ, fun z hz ↦ hb z (hST hz)⟩
  · intro S T ⟨δ, hδ, hb⟩ ⟨η, hη, hc⟩
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro z hz y hy
    rcases hz with hz | hz
    · exact hb z hz y (hy.trans_le (min_le_left _ _))
    · exact hc z hz y (hy.trans_le (min_le_right _ _))
  · intro z hz
    have hzU := hCU hz
    have hc : ContinuousAt (fderiv ℝ f) z := (hD z hzU).continuousAt (hU.mem_nhds hzU)
    obtain ⟨η, hη, hb⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (hU.mem_nhds hzU) (hc (ball_mem_nhds _ (half_pos hε))))
    refine ⟨ball z (η / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (half_pos hη)),
      η / 2, half_pos hη, ?_⟩
    intro w hw y hy
    have hwη : w ∈ ball z η := hw.trans (half_lt_self hη)
    have hyη : y ∈ ball z η := by
      calc
        dist y z ≤ dist y w + dist w z := dist_triangle _ _ _
        _ < η / 2 + η / 2 := add_lt_add hy hw
        _ = η := add_halves η
    apply (convex_ball z η).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun v hv ↦ ((hf.contDiffAt
        (hU.mem_nhds (hb hv).1)).differentiableAt_one).hasFDerivAt.hasFDerivWithinAt)
      (φ := fderiv ℝ f w) _ hwη hyη
    intro v hv
    calc
      ‖fderiv ℝ f v - fderiv ℝ f w‖
          ≤ ‖fderiv ℝ f v - fderiv ℝ f z‖ +
            ‖fderiv ℝ f w - fderiv ℝ f z‖ := by
              simpa only [norm_sub_rev (fderiv ℝ f z) (fderiv ℝ f w)] using
                norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ f v) (fderiv ℝ f z) (fderiv ℝ f w)
      _ ≤ ε / 2 + ε / 2 := add_le_add
        (le_of_lt (by simpa [dist_eq_norm] using (hb hv).2))
        (le_of_lt (by simpa [dist_eq_norm] using (hb hwη).2))
      _ = ε := add_halves ε

variable {T : Type*} [TopologicalSpace T]

/-- `app:lem:common-hamilton-phase`: Lipschitz dependence of a family of curves
turns the uniform Taylor estimate into a remainder small relative to the
initial displacement, uniformly over any compact time set. No initial-data
derivative of the family is assumed. -/
theorem eventually_uniform_flow_remainder {f : E → F} {U s : Set E}
    {Φ : E × T → E} {C : Set T} {x : E} {K : ℝ≥0}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hs : s ∈ 𝓝 x)
    (hC : IsCompact C) (hΦ : ContinuousOn (fun t ↦ Φ (x, t)) C)
    (hrange : ∀ t ∈ C, Φ (x, t) ∈ U)
    (hlip : ∀ t ∈ C, LipschitzOnWith K (fun y ↦ Φ (y, t)) s)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ C,
      ‖f (Φ (y, t)) - f (Φ (x, t)) -
        fderiv ℝ f (Φ (x, t)) (Φ (y, t) - Φ (x, t))‖ ≤ ε * ‖y - x‖ := by
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_fderiv_remainder hU hf
    (hC.image_of_continuousOn hΦ) (by rintro _ ⟨t, ht, rfl⟩; exact hrange t ht)
    (div_pos hε hK)
  filter_upwards [hs, ball_mem_nhds x (div_pos hδ hK)] with y hy hxy
  intro t ht
  have hd : ‖Φ (y, t) - Φ (x, t)‖ ≤ (K : ℝ) * ‖y - x‖ := by
    simpa only [dist_eq_norm] using (hlip t ht).dist_le_mul y hy x (mem_of_mem_nhds hs)
  have hsmall : dist (Φ (y, t)) (Φ (x, t)) < δ := by
    rw [dist_eq_norm]
    calc
      ‖Φ (y, t) - Φ (x, t)‖ ≤ (K : ℝ) * ‖y - x‖ := hd
      _ ≤ ((K : ℝ) + 1) * ‖y - x‖ := by gcongr; linarith
      _ < δ := by
        have := (lt_div_iff₀ hK).mp (show ‖y - x‖ < δ / ((K : ℝ) + 1) from
          by simpa only [mem_ball, dist_eq_norm] using hxy)
        simpa only [mul_comm] using this
  calc
    _ ≤ (ε / ((K : ℝ) + 1)) * ‖Φ (y, t) - Φ (x, t)‖ :=
      hb _ (mem_image_of_mem _ ht) _ hsmall
    _ ≤ (ε / ((K : ℝ) + 1)) * (((K : ℝ) + 1) * ‖y - x‖) := by
      gcongr
      exact hd.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    _ = ε * ‖y - x‖ := by field_simp

end JanetCartan.ODE
