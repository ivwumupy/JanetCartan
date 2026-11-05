module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Neighborhood
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! The local embedding assertion of Proposition `app:ch_seed:prop:seed-analytic`.
A strict first-order approximation by the center inclusion gives a lower distance
bound on a ball, hence an embedding on that ball.
-/

@[expose] public noncomputable section

open scoped Topology NNReal

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: a quantitative lower distance bound
for the explicit cube bending on a sufficiently small ball. -/
theorem cubeBending_lower_distance_bound {n : ℕ} (hn : 0 < n) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball (0 : Euclidean n) r,
      ∀ y ∈ Metric.ball (0 : Euclidean n) r,
        dist x y ≤ 2 * dist (cubeBending n x) (cubeBending n y) := by
  have hd := ((cubeBending_analyticOnNhd n).contDiff (n := (1 : WithTop ℕ∞))).hasStrictFDerivAt
    (x := 0) one_ne_zero
  obtain ⟨s, hs, happ⟩ := hd.approximates_deriv_on_nhds
    (c := (1 / 2 : ℝ≥0)) (Or.inr (by norm_num))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  have h := happ x (hball hx) y (hball hy)
  have hiso : ‖fderiv ℝ (cubeBending n) 0 (x - y)‖ = ‖x - y‖ := by
    unfold cubeBending
    rw [iteratedBending_fderiv_zero _ (by exact_mod_cast (Nat.ne_of_gt hn)),
      initialInclusion_norm]
  have ht := norm_sub_le (cubeBending n x - cubeBending n y)
    (cubeBending n x - cubeBending n y - fderiv ℝ (cubeBending n) 0 (x - y))
  rw [sub_sub_cancel, hiso] at ht
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
  simp only [dist_eq_norm]
  linarith

/-- Proposition `app:ch_seed:prop:seed-analytic`: the analytic cube bending is a
local topological embedding, in addition to having isometric differential. -/
theorem cubeBending_isEmbedding_ball {n : ℕ} (hn : 0 < n) :
    ∃ r : ℝ, 0 < r ∧ Topology.IsEmbedding
      (fun x : Metric.ball (0 : Euclidean n) r ↦ cubeBending n x) := by
  obtain ⟨r, hr, hbound⟩ := cubeBending_lower_distance_bound hn
  refine ⟨r, hr, ?_⟩
  have ha : AntilipschitzWith 2 (fun x : Metric.ball (0 : Euclidean n) r ↦ cubeBending n x) :=
    AntilipschitzWith.of_le_mul_dist (fun x y ↦ hbound x x.property y y.property)
  exact ha.isEmbedding (((cubeBending_analyticOnNhd n).contDiff (n := 0)).continuous.comp continuous_subtype_val)

end JanetCartan.ReferenceConstruction
