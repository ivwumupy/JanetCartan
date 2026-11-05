module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import Mathlib.Analysis.Convex.Basic

/-!
# Geometry of the parameter cubes

Closed, convex parameter cubes and their doubled open neighborhoods in Step 3
of `app:ch_seed:prop:seed-frozen-menu`. These lemmas make shrinking a genuine
cube compatible with the neighborhood statements supplied by calculus.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

open Filter Set
open scoped Topology

/-- The closed parameter cube in `app:ch_seed:prop:seed-frozen-menu` is closed. -/
theorem isClosed_parameterCube (ρ : ℝ) : IsClosed (parameterCube ρ) := by
  have heq : parameterCube ρ = ⋂ i : Fin 3, {z : Euclidean 3 | |z i| ≤ ρ} := by
    ext z
    simp [parameterCube]
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_le (PiLp.continuous_apply 2 _ i).abs
    continuous_const

/-- The smoothness domain in `app:ch_seed:prop:seed-frozen-menu` is open. -/
theorem isOpen_parameterInterior (ρ : ℝ) : IsOpen (parameterInterior ρ) := by
  have heq : parameterInterior ρ = ⋂ i : Fin 3, {z : Euclidean 3 | |z i| < ρ} := by
    ext z
    simp [parameterInterior]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (PiLp.continuous_apply 2 _ i).abs
    continuous_const

/-- The origin lies in every positive open parameter cube
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem zero_mem_parameterInterior {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : Euclidean 3) ∈ parameterInterior ρ := by
  simpa [parameterInterior] using hρ

/-- Every nonnegative closed parameter cube contains the origin
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem zero_mem_parameterCube {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : Euclidean 3) ∈ parameterCube ρ := by
  simpa [parameterCube] using hρ

/-- Positive open parameter cubes are neighborhoods of the base point
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem parameterInterior_mem_nhds {ρ : ℝ} (hρ : 0 < ρ) :
    parameterInterior ρ ∈ 𝓝 (0 : Euclidean 3) :=
  (isOpen_parameterInterior ρ).mem_nhds (zero_mem_parameterInterior hρ)

/-- The closed cube sits inside its doubled smoothness domain
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem parameterCube_subset_doubledInterior {ρ : ℝ} (hρ : 0 < ρ) :
    parameterCube ρ ⊆ parameterInterior (2 * ρ) := by
  intro z hz i
  exact (hz i).trans_lt (by linarith)

/-- Convexity keeps the whole segment in the domain of the chord estimate
`app:ch_seed:eq:seed-frozen-chord`. -/
theorem convex_parameterCube (ρ : ℝ) : Convex ℝ (parameterCube ρ) := by
  intro x hx y hy a b ha hb hab i
  change |a * x i + b * y i| ≤ ρ
  calc
    _ ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha,
        abs_of_nonneg hb]
    _ ≤ a * ρ + b * ρ := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = ρ := by rw [← add_mul, hab, one_mul]

/-- A convenient norm bound for the actual three-dimensional cube in
`app:ch_seed:prop:seed-frozen-menu`. -/
theorem norm_le_three_mul_of_mem_parameterCube {ρ : ℝ} (hρ : 0 ≤ ρ)
    {z : Euclidean 3} (hz : z ∈ parameterCube ρ) : ‖z‖ ≤ 3 * ρ := by
  have hsq : ‖z‖ ^ 2 ≤ 3 * ρ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, ρ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hz i) 2
      _ = 3 * ρ ^ 2 := by simp
  nlinarith [norm_nonneg z, sq_nonneg ρ]

/-- Closed parameter cubes are compact, as used in the frozen menu
construction (`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4). -/
theorem isCompact_parameterCube (ρ : ℝ) : IsCompact (parameterCube ρ) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_parameterCube ρ,
    (Metric.isBounded_closedBall (x := (0 : Euclidean 3)) (r := 3 * ρ)).subset ?_⟩
  intro z hz
  have hρ : 0 ≤ ρ := (abs_nonneg (z 0)).trans (hz 0)
  exact Metric.mem_closedBall.mpr (by simpa using norm_le_three_mul_of_mem_parameterCube hρ hz)

/-- Any neighborhood of the base point contains a doubled parameter cube.
This discharges the domain-shrinking step in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem exists_parameterCube_subset_nhds {U : Set (Euclidean 3)}
    (hU : U ∈ 𝓝 (0 : Euclidean 3)) :
    ∃ ρ > 0, parameterCube (2 * ρ) ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε / 12, by positivity, ?_⟩
  intro z hz
  apply hsub
  rw [Metric.mem_ball, dist_zero_right]
  have h := norm_le_three_mul_of_mem_parameterCube (by positivity : 0 ≤ 2 * (ε / 12)) hz
  linarith

end JanetCartan.FrozenMenu
