module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.RowBounds.Physical

/-!
# Graded primitive profiles for the two-time signed row

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`, a primitive profile
`A j * T ^ (j - R₀)` passes to the same actual characteristic and physical
rows. Natural subtraction is the nonnegative part of `j - R₀`. When `R₀ ≥ 1`,
the profile itself supplies the fixed `C¹` budgets. The constants precede the
scale and the primitive maps. There is no derivative reserve or
order-dependent enlargement of the low neighborhood.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.CharacteristicTransport.RowBounds

open RegularSector.Characteristic

variable {P X ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [Fintype ι]

/-- Primitive graded profiles imply the same graded profile for the actual
signed characteristic row, with zero reserve. The fixed low budget follows
from the profile at order one; it is not an extra analytic premise
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_rowTransport_graded_bounds (p : P) {σ R : ℝ}
    (hσ : 0 < σ) (hσR : σ < R) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    {R₀ : ℕ} (hR₀ : 1 ≤ R₀) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧ ∀ T : ℝ, 1 ≤ T →
      ∀ (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ),
      ContDiffOn ℝ ∞ c (ball (0, (0, p)) R) →
      ContDiffOn ℝ ∞ r (ball (0, p) R) →
      (∀ j, cNorm (closedBall (0, (0, p)) σ) j c ≤ A j * T ^ (j - R₀)) →
      (∀ j, cNorm (closedBall (0, p) σ) j r ≤ A j * T ^ (j - R₀)) →
      ∀ m, cNorm (closedBall (0, (0, p)) σ) m (rowTransport c r) ≤
        D m * T ^ (m - R₀) := by
  obtain ⟨C, hC, hb⟩ := exists_rowTransport_cNorm_bounds (ι := ι) p hσ hσR (hA 1)
  refine ⟨fun m ↦ C m * (1 + 2 * A m),
    fun m ↦ mul_pos (hC m) (by linarith [hA m]), ?_⟩
  intro T hT c r hc hr hcprof hrprof m
  have hclow : cNorm (closedBall (0, (0, p)) σ) 1 c ≤ A 1 := by
    simpa only [Nat.sub_eq_zero_of_le hR₀, pow_zero, mul_one] using hcprof 1
  have hrlow : cNorm (closedBall (0, p) σ) 1 r ≤ A 1 := by
    simpa only [Nat.sub_eq_zero_of_le hR₀, pow_zero, mul_one] using hrprof 1
  have hp : 1 ≤ T ^ (m - R₀) := one_le_pow₀ hT
  apply (hb c r hc hr hclow hrlow m).trans
  have hs : 1 + cNorm (closedBall (0, (0, p)) σ) m c +
      cNorm (closedBall (0, p) σ) m r ≤ (1 + 2 * A m) * T ^ (m - R₀) := by
    nlinarith [hcprof m, hrprof m]
  exact (mul_le_mul_of_nonneg_left hs (hC m).le).trans_eq (by ring)

/-- The same graded profile controls the *published* physical signed row
from profiles of `c,r,Y`. Every constant precedes the scale and the maps,
and the reserve is zero. The parent two-time Hamilton construction must
instantiate the primitive profiles and actual image containment; this
implication alone does not establish the regular-sector existence theorem
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_physicalRowTransport_graded_bounds (x : X) (p : P)
    {ρ σ Rx R : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hρRx : ρ < Rx) (hσR : σ < R)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) {R₀ : ℕ} (hR₀ : 1 ≤ R₀) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧ ∀ T : ℝ, 1 ≤ T →
      ∀ (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ) (Y : ℝ × (ℝ × X) → P),
      ContDiffOn ℝ ∞ c (ball (0, (0, p)) R) →
      ContDiffOn ℝ ∞ r (ball (0, p) R) →
      ContDiffOn ℝ ∞ Y (ball (0, (0, x)) Rx) →
      MapsTo (fun q ↦ (q.1, (q.2.1, Y q)))
        (closedBall (0, (0, x)) ρ) (closedBall (0, (0, p)) σ) →
      (∀ j, cNorm (closedBall (0, (0, p)) σ) j c ≤ A j * T ^ (j - R₀)) →
      (∀ j, cNorm (closedBall (0, p) σ) j r ≤ A j * T ^ (j - R₀)) →
      (∀ j, cNorm (closedBall (0, (0, x)) ρ) j Y ≤ A j * T ^ (j - R₀)) →
      ∀ m, cNorm (closedBall (0, (0, x)) ρ) m (physicalRowTransport c r Y) ≤
        D m * T ^ (m - R₀) := by
  obtain ⟨C, hC, hb⟩ := exists_physicalRowTransport_cNorm_bounds (ι := ι)
    x p hρ hσ hρRx hσR (hA 1)
  refine ⟨fun m ↦ C m * (1 + 3 * A m),
    fun m ↦ mul_pos (hC m) (by linarith [hA m]), ?_⟩
  intro T hT c r Y hc hr hY hmap hcprof hrprof hYprof m
  have hclow : cNorm (closedBall (0, (0, p)) σ) 1 c ≤ A 1 := by
    simpa only [Nat.sub_eq_zero_of_le hR₀, pow_zero, mul_one] using hcprof 1
  have hrlow : cNorm (closedBall (0, p) σ) 1 r ≤ A 1 := by
    simpa only [Nat.sub_eq_zero_of_le hR₀, pow_zero, mul_one] using hrprof 1
  have hYlow : cNorm (closedBall (0, (0, x)) ρ) 1 Y ≤ A 1 := by
    simpa only [Nat.sub_eq_zero_of_le hR₀, pow_zero, mul_one] using hYprof 1
  have hp : 1 ≤ T ^ (m - R₀) := one_le_pow₀ hT
  apply (hb c r Y hc hr hY hmap hclow hrlow hYlow m).trans
  have hs : 1 + cNorm (closedBall (0, (0, p)) σ) m c +
      cNorm (closedBall (0, p) σ) m r + cNorm (closedBall (0, (0, x)) ρ) m Y ≤
      (1 + 3 * A m) * T ^ (m - R₀) := by
    nlinarith [hcprof m, hrprof m, hYprof m]
  exact (mul_le_mul_of_nonneg_left hs (hC m).le).trans_eq (by ring)

end JanetCartan.CharacteristicTransport.RowBounds
