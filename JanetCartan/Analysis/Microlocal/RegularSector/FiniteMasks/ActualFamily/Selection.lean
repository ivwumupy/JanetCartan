module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Neighborhoods
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Pencil
public import Mathlib.Algebra.Order.Field.Pi

/-!
# Actual finite characteristic charts and common radii

Construct a local uniform chart at every protected frozen zero. The actual
source plateau gives its open angular neighborhood. Compactness in
`exists_finite_pencil_masks` selects the finite family and masks. Finally
shrink the coefficient and physical neighborhoods simultaneously. Every
choice precedes the current fields, derivative orders and accuracy.

Consumer: the finite physical solver of `app:ch_regular_base:thm:sector`;
the complementary determinant gap is retained for `prop:complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open ActualCarriers
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- Select the actual finite chart family and angular masks directly from
regularity on the protected compact. No characteristic cover, matching masks
or successful finite family is an input. The retained chart contains the SAME
root, masks, phase and amplitude construction for `UniformEvolution`.
The determinant gap holds on the complete complementary angular support.
Source: `app:ch_regular_base:thm:sector` and `prop:complete-residual`. -/
theorem exists_finite_actual_chart_masks
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ (s : Finset {ξ : E | ξ ∈ K ∧ determinant A₀ ξ = 0})
      (chart : ∀ p : s, LocalChart Ω x RQ A₀ p.val.val M)
      (χ : s → E → ℝ),
      ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ R > (0 : ℝ),
      (∀ p, ε ≤ (chart p).coefficientRadius) ∧
      closedBall x (4 * R) ⊆ Ω ∧
      closedBall x (4 * R) ⊆ closedBall x RQ ∧
      (∀ p, closedBall x (4 * R) ⊆ (chart p).physicalNeighborhood) ∧
      (∀ p, ContDiff ℝ ∞ (χ p)) ∧
      (∀ p ξ, χ p ξ ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, HasCompactSupport (χ p)) ∧
      (∀ p, tsupport (χ p) ⊆ (chart p).angularNeighborhood) ∧
      (∀ ξ, ∑ p, χ p ξ ≤ 1) ∧
      (∀ (Q : E → Fin (d + 1) → Mat) (X : Set E),
        (∀ y ∈ X, ‖Q y - A₀‖ ≤ ε) →
        (∀ y ∈ X, ∀ ξ ∈ K ∩ tsupport (fun η ↦ 1 - ∑ p, χ p η),
          δ ≤ |determinant (Q y) ξ|) ∧
        (∀ y ∈ X, ∀ ξ ∈ K, determinant (Q y) ξ = 0 →
          ξ ∈ interior {η | ∑ p, χ p η = 1})) := by
  classical
  let Z := {ξ : E | ξ ∈ K ∧ determinant A₀ ξ = 0}
  have hc (p : Z) : Nonempty (LocalChart Ω x RQ A₀ p.val M) :=
    exists_localChart hΩ x hRQ hKΩ A₀ p.val
      (fun hz ↦ hKzero (hz ▸ p.property.1)) p.property.2
      (hregular p.val p.property.1 p.property.2) hM
  let charts : ∀ p : Z, LocalChart Ω x RQ A₀ p.val M := fun p ↦ Classical.choice (hc p)
  obtain ⟨s, χ, ε₀, hε₀, δ, hδ, hχ, hrange, hcompact, hsupp, hsum, hstable⟩ :=
    exists_finite_pencil_masks A₀ hK (fun p : Z ↦ (charts p).angularNeighborhood)
      (fun p ↦ (charts p).isOpen_angularNeighborhood) (by
        intro ξ hξ hp
        exact ⟨⟨ξ, hξ, hp⟩, (charts ⟨ξ, hξ, hp⟩).center_mem_angularNeighborhood⟩)
  let chart : ∀ p : s, LocalChart Ω x RQ A₀ p.val.val M := fun p ↦ charts p.val
  obtain ⟨ε₁, hε₁, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : s ↦ (0 : ℝ)) (y := fun p ↦ (chart p).coefficientRadius)
    (fun p ↦ (chart p).coefficientRadius_pos)
  let V : Set E := ball x RQ ∩ ⋂ p : s, (chart p).physicalNeighborhood
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_iInter_of_finite fun p ↦ (chart p).isOpen_physicalNeighborhood)
  have hxV : x ∈ V := ⟨mem_ball_self hRQ,
    mem_iInter.mpr fun p ↦ (chart p).center_mem_physicalNeighborhood⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV x hxV
  have hball : closedBall x (4 * (r / 8)) ⊆ V :=
    (closedBall_subset_ball (by linarith : 4 * (r / 8) < r)).trans hrV
  refine ⟨s, chart, χ, min ε₀ ε₁, lt_min hε₀ hε₁, δ, hδ, r / 8,
    by positivity, ?_, fun y hy ↦ hKΩ (ball_subset_closedBall (hball hy).1),
    fun y hy ↦ ball_subset_closedBall (hball hy).1,
    fun p y hy ↦ mem_iInter.mp (hball hy).2 p,
    hχ, hrange, hcompact, hsupp, hsum, ?_⟩
  · intro p
    exact (min_le_right _ _).trans (by simpa using (hsmall p).le)
  · intro Q X hQ
    exact hstable Q X fun y hy ↦ (hQ y hy).trans (min_le_left _ _)

end JanetCartan.RegularSector.FiniteMasks.ActualFamily
