module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms.Membership
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms.WeakExtension

/-!
# Restriction Sobolev coefficient budgets for the finite sector assembly

For `app:not:fourier`, `app:ch_regular_base:eq:sector-theorem-solution`, and
`app:ch_regular_base:eq:sector-theorem-residual`, bound the original compact
`cNorm` budgets by the infimum over genuine weak Sobolev extensions. The
extension estimate passes through the infimum; supported smooth extensions
supply membership of the literal coefficients. The Frobenius matrix norm and
the existing coefficient-array norm are preserved, with no coordinate change.

One bounded norm ball, compactly contained in the original domain and with a
positive margin around the unchanged coefficient compact set, is chosen
before the coefficients. The derivative reserve is `d + 2`, independently of
the order and fields. The joint additive estimate supplies the coefficient
profile in `FiniteAssembly.exists_finite_direct_operator_bounds`; operator
and PDE assembly remain with that consumer.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms

open LocalSobolev

/-- The quantitative bound against every genuine weak extension descends to
its infimum (`app:not:fourier`). The constant is fixed before the ball, smooth
field and local class. Membership is required because the restriction norm is
zero off the restriction space; `smoothCoefficientL2_memRestrictionSobolev`
provides it for the sector coefficients. This supplies the infimum step for
`exists_coefficient_pair_restriction_bounds`, without choosing a smooth or
near-minimal extension. -/
theorem exists_cNorm_le_restrictionSobolevNorm (n m : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : Euclidean n) (RQ R : ℝ),
      0 < RQ → RQ < R → ∀ f : Euclidean n → F,
      ContDiffOn ℝ ∞ f (ball x R) → ∀ u : LocalL2 (ball x R) F,
      f =ᵐ[volume.restrict (ball x R)] u →
      MemRestrictionSobolev (ball x R) (m + n + 1) u →
      cNorm (closedBall x RQ) m f ≤
        C * restrictionSobolevNorm (ball x R) (m + n + 1) u := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_le_extension_jetNorm (F := F) n m
  refine ⟨C, hC, ?_⟩
  intro x RQ R hRQ hR f hf u hfu hu
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  rw [mul_comm C]
  apply (div_le_iff₀ hCpos).mp
  apply le_csInf (show (Set.range (SobolevExtension.jetNorm
    (U := ball x R) (s := m + n + 1) (u := u))).Nonempty from
      ⟨hu.some.jetNorm, hu.some, rfl⟩)
  rintro _ ⟨e, rfl⟩
  exact (div_le_iff₀ hCpos).mpr (by
    simpa only [mul_comm] using hbound x RQ R hRQ hR f hf u hfu e)

/-- Convert both original coefficient budgets to genuine restriction Sobolev
norms with the fixed reserve `d + 2`, preserving the supremum norm on the
array of Frobenius matrices and the Frobenius matrix norm itself
(`app:not:fourier`, `app:ch_regular_base:eq:sector-theorem-solution`,
`app:ch_regular_base:eq:sector-theorem-residual`). The profile is chosen before
all fields and even before the norm ball. All membership premises of the
infimum estimate are discharged by the supported smooth construction.

The consumer `FiniteAssembly.exists_finite_direct_operator_bounds` uses the
joint additive conclusion at `m = s - o + sectorLowOrder d` on these same
coefficients and compact set; it retains the operator and PDE assembly. -/
theorem exists_coefficient_pair_restriction_bounds (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
      ∀ (Ω : Set (Euclidean (d + 1))) (x : Euclidean (d + 1)) (RQ R : ℝ)
        (hΩ : IsOpen Ω) (hRQ : 0 < RQ) (hQR : RQ < R)
        (hball : closedBall x R ⊆ Ω)
        (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (B : Euclidean (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω),
      let uQ := smoothCoefficientL2 hΩ (hRQ.trans hQR) hball Q hQ
      let uB := smoothCoefficientL2 hΩ (hRQ.trans hQR) hball B hB
      (∀ k, MemRestrictionSobolev (ball x R) k uQ ∧
        MemRestrictionSobolev (ball x R) k uB) ∧
      ∀ m,
        cNorm (closedBall x RQ) m Q ≤
          C m * restrictionSobolevNorm (ball x R) (m + (d + 2)) uQ ∧
        cNorm (closedBall x RQ) m B ≤
          C m * restrictionSobolevNorm (ball x R) (m + (d + 2)) uB ∧
        1 + cNorm (closedBall x RQ) m Q + cNorm (closedBall x RQ) m B ≤
          C m * (1 + restrictionSobolevNorm (ball x R) (m + (d + 2)) uQ +
            restrictionSobolevNorm (ball x R) (m + (d + 2)) uB) := by
  choose CQ hCQ hQbound using fun m ↦ exists_cNorm_le_restrictionSobolevNorm
    (F := Fin (d + 1) → MetricTensor (d + 1)) (d + 1) m
  choose CB hCB hBbound using fun m ↦ exists_cNorm_le_restrictionSobolevNorm
    (F := MetricTensor (d + 1)) (d + 1) m
  let C : ℕ → ℝ := fun m ↦ max (CQ m) (CB m)
  have hC m : 1 ≤ C m := (hCQ m).trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro Ω x RQ R hΩ hRQ hQR hball Q B hQ hB
  dsimp only
  refine ⟨fun k ↦ coefficient_pair_memRestrictionSobolev
    hΩ (hRQ.trans hQR) hball Q B hQ hB k, ?_⟩
  intro m
  have hq := hQbound m x RQ R hRQ hQR Q
    (hQ.mono (ball_subset_closedBall.trans hball)) _
    (smoothCoefficientL2_coeFn hΩ (hRQ.trans hQR) hball Q hQ).symm
    (smoothCoefficientL2_memRestrictionSobolev hΩ (hRQ.trans hQR) hball Q hQ _)
  have hb := hBbound m x RQ R hRQ hQR B
    (hB.mono (ball_subset_closedBall.trans hball)) _
    (smoothCoefficientL2_coeFn hΩ (hRQ.trans hQR) hball B hB).symm
    (smoothCoefficientL2_memRestrictionSobolev hΩ (hRQ.trans hQR) hball B hB _)
  have hq' := hq.trans (mul_le_mul_of_nonneg_right
    (le_max_left (CQ m) (CB m)) restrictionSobolevNorm_nonneg)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (le_max_right (CQ m) (CB m)) restrictionSobolevNorm_nonneg)
  refine ⟨by simpa only [Nat.add_assoc] using hq',
    by simpa only [Nat.add_assoc] using hb', ?_⟩
  calc
    _ ≤ C m + C m * restrictionSobolevNorm (ball x R) (m + (d + 2))
          (smoothCoefficientL2 hΩ (hRQ.trans hQR) hball Q hQ) +
        C m * restrictionSobolevNorm (ball x R) (m + (d + 2))
          (smoothCoefficientL2 hΩ (hRQ.trans hQR) hball B hB) := by
      exact add_le_add (add_le_add (hC m) (by simpa only [Nat.add_assoc] using hq'))
        (by simpa only [Nat.add_assoc] using hb')
    _ = _ := by ring

/-- Choose one bounded norm ball with compact closure inside the original
domain and positive margin around the unchanged coefficient compact set,
then choose all constants before varying the coefficients. Their actual local
L² classes have restriction Sobolev membership at every order, and both
individual and joint additive coefficient estimates use the fixed reserve
`d + 2` (`app:not:fourier`,
`app:ch_regular_base:eq:sector-theorem-solution`,
`app:ch_regular_base:eq:sector-theorem-residual`).

This closes the coefficient-norm input to
`FiniteAssembly.exists_finite_direct_operator_bounds`; it changes none of
its selected family, masks, low-order neighborhood or radial threshold. -/
theorem exists_coefficient_restriction_norm_bounds {d : ℕ}
    {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ : ℝ}
    (hΩ : IsOpen Ω) (hRQ : 0 < RQ) (hQΩ : closedBall x RQ ⊆ Ω) :
    ∃ (R : ℝ) (hQR : RQ < R) (hball : closedBall x R ⊆ Ω),
      Bornology.IsBounded (ball x R) ∧ IsCompact (closure (ball x R)) ∧
      closure (ball x R) ⊆ Ω ∧
      (∃ ε : ℝ, 0 < ε ∧ closedBall x (RQ + ε) ⊆ ball x R) ∧
      ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
        ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
          (B : Euclidean (d + 1) → MetricTensor (d + 1))
          (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω),
        let uQ := smoothCoefficientL2 hΩ (hRQ.trans hQR) hball Q hQ
        let uB := smoothCoefficientL2 hΩ (hRQ.trans hQR) hball B hB
        (∀ k, MemRestrictionSobolev (ball x R) k uQ ∧
          MemRestrictionSobolev (ball x R) k uB) ∧
        ∀ m,
          cNorm (closedBall x RQ) m Q ≤
            C m * restrictionSobolevNorm (ball x R) (m + (d + 2)) uQ ∧
          cNorm (closedBall x RQ) m B ≤
            C m * restrictionSobolevNorm (ball x R) (m + (d + 2)) uB ∧
          1 + cNorm (closedBall x RQ) m Q + cNorm (closedBall x RQ) m B ≤
            C m * (1 + restrictionSobolevNorm (ball x R) (m + (d + 2)) uQ +
              restrictionSobolevNorm (ball x R) (m + (d + 2)) uB) := by
  obtain ⟨R, hQR, hbounded, hcompact, hclosure, hmargin⟩ :=
    exists_coefficient_norm_ball hΩ hRQ hQΩ
  have hball : closedBall x R ⊆ Ω := by
    simpa only [closure_ball x (hRQ.trans hQR).ne'] using hclosure
  obtain ⟨C, hC, hbound⟩ := exists_coefficient_pair_restriction_bounds d
  exact ⟨R, hQR, hball, hbounded, hcompact, hclosure, hmargin, C, hC,
    hbound Ω x RQ R hΩ hRQ hQR hball⟩

end JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms
