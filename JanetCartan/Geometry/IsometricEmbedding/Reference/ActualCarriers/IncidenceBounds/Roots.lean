module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Jets
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Denominator

/-!
# Tame bounds for supplied actual incidence roots

The final quantitative deduction in Step 3 of
`app:ch_seed:prop:seed-actual-menu`. A supplied smooth interior root satisfies a
one-high bound derived from the primitive frame and phase-gradient seminorms.
The denominator input is a fixed low transverse gap. It is supplied either by
the continued-root construction or by `exists_incidence_denominator_radius`.
The root equation, interior location, and smoothness remain construction inputs;
no root derivative estimate or incidence seminorm estimate is an input.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open Set Metric

namespace JanetCartan.ActualCarriers

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {n : ℕ}

/-- `app:ch_seed:eq:seed-phase-tame`: the existing transverse implicit-root
recurrence applied to the literal actual incidence equation. All derivatives
are joint in the physical, angular, and spectator variables represented by `P`.
For orders at least two there is no loss relative to the primitive fields;
orders zero and one use their fixed second-order budgets. The constant is
chosen before the fields and the root. Its order-zero budget is derived from
its location in the fixed buffered ball. -/
theorem exists_cNorm_incidence_root_le_primitive
    (a : P × ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {TQ : Set (Fin n → MetricTensor n)} {Tξ K : Set (Euclidean n)}
    (hTQ : IsCompact TQ) (hTξ : IsCompact Tξ) (hK : IsCompact K)
    {L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c) (r : ℕ)
    {W : Set (P × ℝ)} (hW : IsOpen W) (hballW : closedBall a ρ ⊆ W) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : P × ℝ → Fin n → MetricTensor n) (ξ k : P × ℝ → Euclidean n),
      ContDiffOn ℝ ∞ Q W → ContDiffOn ℝ ∞ ξ W → ContDiffOn ℝ ∞ k W →
      MapsTo Q (closedBall a ρ) TQ → MapsTo ξ (closedBall a ρ) Tξ →
      MapsTo k (closedBall a ρ) K →
      cNorm (closedBall a ρ) 1 Q + cNorm (closedBall a ρ) 1 ξ +
        cNorm (closedBall a ρ) 1 k ≤ L →
      ∀ (s U : Set P), IsOpen U → s ⊆ U → ∀ (g : P → ℝ),
      ContDiffOn ℝ ∞ g U →
      (∀ p ∈ U, fderiv ℝ (determinant (Q (p, g p))) (ξ (p, g p)) (k (p, g p)) = 0) →
      (∀ p ∈ s, (p, g p) ∈ closedBall a ρ) →
      (∀ p ∈ s, c ≤ |CharacteristicRoot.scalarDerivative
        (fun y ↦ fderiv ℝ (determinant (Q y)) (ξ y) (k y)) (p, g p)|) →
      cNorm s r g ≤ C * (1 + cNorm (closedBall a ρ) (max r 2) Q +
        cNorm (closedBall a ρ) (max r 2) ξ + cNorm (closedBall a ρ) (max r 2) k) := by
  let N := max r 2
  have hN : 2 ≤ N := le_max_right _ _
  have hrN : r ≤ N := le_max_left _ _
  obtain ⟨M, hM, hprofile⟩ := exists_incidence_jet_profile
    a hρ hTQ hTξ hK hN hL hW hballW
  obtain ⟨C, hC, hroot⟩ := CharacteristicRoot.exists_root_cNorm_bound_of_equation_profile
    (P := P) (G := ‖a.2‖ + ρ) (zero_le_one.trans hM) hc
      (add_nonneg (norm_nonneg _) hρ.le) r
  refine ⟨C, hC, ?_⟩
  intro Q ξ k hQ hξ hk hQT hξT hkK hlow s U hU hsU g hg heq hgraph hgap
  let f : P × ℝ → ℝ := fun y ↦ fderiv ℝ (determinant (Q y)) (ξ y) (k y)
  have hf : ContDiffOn ℝ ∞ f W :=
    contDiff_incidenceCoefficient.comp_contDiffOn ((hQ.prodMk hξ).prodMk hk)
  let H := 1 + cNorm (closedBall a ρ) N Q + cNorm (closedBall a ρ) N ξ +
    cNorm (closedBall a ρ) N k
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (closedBall a ρ) N Q, cNorm_nonneg (closedBall a ρ) N ξ,
      cNorm_nonneg (closedBall a ρ) N k]
  have hN' : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  let R : ℝ := H ^ (1 / ((N : ℝ) - 1))
  have hR : 1 ≤ R := Real.one_le_rpow hH (by positivity)
  have hpow (j : ℕ) (hj : 1 ≤ j) :
      R ^ (j - 1) = H ^ (((j : ℝ) - 1) / ((N : ℝ) - 1)) := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hH),
      Nat.cast_sub hj, Nat.cast_one]
    congr 1
    ring
  have hRN : R ^ (N - 1) = H := by
    rw [hpow N (by omega), div_self hN'.ne', Real.rpow_one]
  have hval (p : P) (hp : p ∈ s) : ‖g p‖ ≤ ‖a.2‖ + ρ := by
    apply norm_le_norm_add_const_of_dist_le
    exact (show dist (g p) a.2 ≤ dist (p, g p) a from le_max_right _ _).trans
      (hgraph p hp)
  have hb : cNorm s r g ≤ C * R ^ (r - 1) := by
    apply hroot R hR s U hU hsU f g
      (fun p hp ↦ (hf.contDiffAt (hW.mem_nhds (hballW (hgraph p hp)))).of_le (by simp))
      (hg.of_le (by simp)) heq hgap hval
    intro p hp j hj hjr
    rw [hpow j hj]
    exact hprofile Q ξ k hQ hξ hk hQT hξT hkK hlow j hj (hjr.trans hrN)
      (p, g p) (hgraph p hp)
  exact hb.trans (mul_le_mul_of_nonneg_left
    ((pow_le_pow_right₀ hR (Nat.sub_le_sub_right hrN 1)).trans_eq hRN) hC.le)

/-- `app:ch_seed:eq:seed-phase-tame`: the paper reserve `r + 6` follows from
primitive frame loss two and carrier-gradient loss four. The low orders use
`max r 2`; the elementary inequalities `max r 2 + 2 ≤ r + 6` and
`max r 2 + 4 ≤ r + 6` keep the reserve fixed. The actual producers must supply
these two primitive budgets, the low bounds/ranges, and the constructed root.
No identification of Euclidean data with a torus model is used. -/
theorem exists_cNorm_incidence_root_le_reserve_six
    (a : P × ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {TQ : Set (Fin n → MetricTensor n)} {Tξ K : Set (Euclidean n)}
    (hTQ : IsCompact TQ) (hTξ : IsCompact Tξ) (hK : IsCompact K)
    {L c A B D : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (r : ℕ)
    {W : Set (P × ℝ)} (hW : IsOpen W) (hballW : closedBall a ρ ⊆ W) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : P × ℝ → Fin n → MetricTensor n) (ξ k : P × ℝ → Euclidean n),
      ContDiffOn ℝ ∞ Q W → ContDiffOn ℝ ∞ ξ W → ContDiffOn ℝ ∞ k W →
      MapsTo Q (closedBall a ρ) TQ → MapsTo ξ (closedBall a ρ) Tξ →
      MapsTo k (closedBall a ρ) K →
      cNorm (closedBall a ρ) 1 Q + cNorm (closedBall a ρ) 1 ξ +
        cNorm (closedBall a ρ) 1 k ≤ L →
      ∀ (s U : Set P), IsOpen U → s ⊆ U → ∀ (g : P → ℝ),
      ContDiffOn ℝ ∞ g U →
      (∀ p ∈ U, fderiv ℝ (determinant (Q (p, g p))) (ξ (p, g p)) (k (p, g p)) = 0) →
      (∀ p ∈ s, (p, g p) ∈ closedBall a ρ) →
      (∀ p ∈ s, c ≤ |CharacteristicRoot.scalarDerivative
        (fun y ↦ fderiv ℝ (determinant (Q y)) (ξ y) (k y)) (p, g p)|) →
      ∀ {N : ℕ} (F : Euclidean n → Euclidean N) (KF : Set (Euclidean n)),
      cNorm (closedBall a ρ) (max r 2) Q ≤ A * (1 + cNorm KF (max r 2 + 2) F) →
      cNorm (closedBall a ρ) (max r 2) ξ ≤ B * (1 + cNorm KF (max r 2 + 4) F) →
      cNorm (closedBall a ρ) (max r 2) k ≤ D →
      cNorm s r g ≤ C * (1 + cNorm KF (r + 6) F) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_incidence_root_le_primitive
    a hρ hTQ hTξ hK hL hc r hW hballW
  refine ⟨C * (1 + A + B + D), mul_pos hC (by positivity), ?_⟩
  intro Q ξ k hQ hξ hk hQT hξT hkK hlow s U hU hsU g hg heq hgraph hgap
    N F KF hQnorm hξnorm hknorm
  have hb' := hb Q ξ k hQ hξ hk hQT hξT hkK hlow s U hU hsU g hg heq hgraph hgap
  have hQmono : cNorm KF (max r 2 + 2) F ≤ cNorm KF (r + 6) F :=
    cNorm_mono_order (by omega)
  have hξmono : cNorm KF (max r 2 + 4) F ≤ cNorm KF (r + 6) F :=
    cNorm_mono_order (by omega)
  have hQ' := hQnorm.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hQmono) hA)
  have hξ' := hξnorm.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hξmono) hB)
  apply hb'.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hF := cNorm_nonneg KF (r + 6) F
  nlinarith

end JanetCartan.ActualCarriers
