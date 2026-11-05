module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LebesgueData

/-!
# Concrete buffers for the raw Fourier ceiling

The original rounded density is supported below `4 K`. The window
`τ K ≤ ρ/32` keeps its full shift segments inside one fixed covector ball.
These containments discharge the product and segment premises of the physical
bound in `exists_finite_actual_graded_raw_family`, locally around its SAME
selected center (`app:ch_waves:eq:raw-physical-bound`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology
namespace JanetCartan.RawPrimary
/-- The entire rounded Fourier ceiling and every shift segment remain in
one original covector buffer (`app:ch_waves:thm:individual`). -/
theorem rawFamily_shifted_segment_mem_ball {n : ℕ} {ρ τ K : ℝ} (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (hwindow : τ * K ≤ ρ / 32) (ζ : Euclidean (n - 1))
    {η : Euclidean (n - 1)} (hη : η ∈ closedBall 0 (4 * K))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ζ + (t * τ) • η ∈ ball ζ (ρ / 4) := by
  have hn : ‖η‖ ≤ 4 * K := by simpa using hη
  have hmul : t * τ ≤ τ := by nlinarith [ht.1, ht.2]
  have hb : t * τ * ‖η‖ ≤ τ * (4 * K) :=
    (mul_le_mul_of_nonneg_right hmul (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hn hτ)
  rw [mem_ball, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1 hτ)]
  nlinarith
/-- A concrete open product sits inside the same graded working ball.
The carrier label and covector center are retained together
(`app:ch_waves:eq:individual-grading`). -/
theorem rawFamily_product_subset_workingBall {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (z₀ z : Euclidean 3) (ζ₀ ζ : Euclidean (n - 1))
    (hz : (z, ζ) ∈ ball (z₀, ζ₀) (ρ / 4))
    {x : Euclidean n} (hx : x ∈ ball 0 (ρ / 2))
    {ξ : Euclidean (n - 1)} (hξ : ξ ∈ ball ζ (ρ / 4)) :
    (x, (z, ξ)) ∈ closedBall ((0 : Euclidean n), (z₀, ζ₀)) ρ := by
  have hz' := (mem_ball.mp hz)
  rw [Prod.dist_eq, max_lt_iff] at hz'
  rw [mem_closedBall, Prod.dist_eq, Prod.dist_eq, max_le_iff, max_le_iff]
  refine ⟨(mem_ball.mp hx).le.trans (by linarith), hz'.1.le.trans (by linarith), ?_⟩
  exact (dist_triangle ξ ζ ζ₀).trans (by linarith [mem_ball.mp hξ, hz'.2])
end JanetCartan.RawPrimary
