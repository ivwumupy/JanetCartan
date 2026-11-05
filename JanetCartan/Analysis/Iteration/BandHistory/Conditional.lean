module

public import JanetCartan.Analysis.Fourier.Periodic
public import JanetCartan.Analysis.Iteration.BandHistory.Geometric

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional reductions for band-limited histories

The numerical argument of `main:lem:history` is proved in `BandHistory.Geometric`.
This module applies it to the actual periodic norms, **conditional on the explicitly
quantified Bernstein estimates**. No analytic Bernstein theorem is asserted here.
The baseline sum and its smallness use the L² estimate; the sum of higher derivative
seminorms uses the sharp derivative-to-derivative estimate. The fixed-baseline numerical
profile is `initial_add_sum_history_profile_le`. The parent `BandHistory` module
discharges both Bernstein premises and assembles the actual map-history estimate.
-/

@[expose] public noncomputable section

open Filter Topology

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem history_cNorm_nonneg (r : ℕ) (f : Torus n → F) :
    0 ≤ cNorm (fundamentalCell n) r (periodicLift f) := by
  apply Finset.sum_nonneg
  intro j _
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  exact norm_nonneg _

/-- `main:eq:history-bernstein`: the exact L² Bernstein input and the history data
imply the required decay, with no loss beyond `B₀ + b_* (r_* + n/2) + 1`.
The band constant `L` is fixed independently of the stage and initial scale. -/
theorem periodic_history_increment_bound_of_bernstein
    (r₀ : ℕ) {C L R v b B k₀ : ℝ} {k : ℕ → ℝ} {u : ℕ → Torus n → F}
    (hR : 2 ≤ R) (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hbernstein : ∀ (M : ℝ), 1 ≤ M → ∀ f : Torus n → F,
      IsSmoothPeriodic f → HasFourierSupport M f →
      cNorm (fundamentalCell n) r₀ (periodicLift f) ≤
        C * M ^ ((r₀ : ℝ) + (n : ℝ) / 2) * periodicL2Norm f)
    (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1))
    (hk : ∀ i, k₀ ≤ k i) (i : ℕ) :
    cNorm (fundamentalCell n) r₀ (periodicLift (u i)) ≤
      (C * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)) *
        historyScale R v i ^ (-(k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)) := by
  let q : ℝ := (r₀ : ℝ) + (n : ℝ) / 2
  have hscale : 1 ≤ historyScale R v i :=
    Real.one_le_rpow (by linarith) (pow_nonneg (by linarith : 0 ≤ v) i)
  have hscale0 : 0 < historyScale R v i := lt_of_lt_of_le zero_lt_one hscale
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hband : 1 ≤ L * historyScale R v i ^ b :=
    one_le_mul_of_one_le_of_one_le hL (Real.one_le_rpow hscale hb)
  calc
    cNorm (fundamentalCell n) r₀ (periodicLift (u i)) ≤
        C * (L * historyScale R v i ^ b) ^ q * periodicL2Norm (u i) :=
      hbernstein _ hband _ (hsmooth i) (hsupport i)
    _ ≤ C * (L * historyScale R v i ^ b) ^ q * historyScale R v i ^ (-k i + B + 1) :=
      mul_le_mul_of_nonneg_left (hL2 i)
        (mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hband) q))
    _ = (C * L ^ q) * historyScale R v i ^ (b * q + (-k i + B + 1)) := by
      rw [Real.mul_rpow hL0 (Real.rpow_nonneg hscale0.le _),
        ← Real.rpow_mul hscale0.le, Real.rpow_add hscale0 (b * q) (-k i + B + 1)]
      ring
    _ ≤ (C * L ^ q) * historyScale R v i ^ (-(k₀ - (B + b * q) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg hL0 _))
      apply Real.rpow_le_rpow_of_exponent_le hscale
      linarith [hk i]

/-- `main:lem:history`: summability and the exact total bound for the actual baseline
periodic seminorms, conditional only on the displayed L² Bernstein input. -/
theorem periodic_history_summable_of_bernstein
    (r₀ : ℕ) {C L R v b B k₀ : ℝ} {k : ℕ → ℝ} {u : ℕ → Torus n → F}
    (hR : 2 ≤ R) (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)
    (hbernstein : ∀ (M : ℝ), 1 ≤ M → ∀ f : Torus n → F,
      IsSmoothPeriodic f → HasFourierSupport M f →
      cNorm (fundamentalCell n) r₀ (periodicLift f) ≤
        C * M ^ ((r₀ : ℝ) + (n : ℝ) / 2) * periodicL2Norm f)
    (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1))
    (hk : ∀ i, k₀ ≤ k i) :
    Summable (fun i ↦ cNorm (fundamentalCell n) r₀ (periodicLift (u i))) ∧
      (∑' i, cNorm (fundamentalCell n) r₀ (periodicLift (u i))) ≤
        historyBound (C * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)) R v
          (k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) := by
  have hdecay := periodic_history_increment_bound_of_bernstein r₀ hR hv hb hL hC
    hbernstein hsmooth hsupport hL2 hk
  have hconst := mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hL)
    ((r₀ : ℝ) + (n : ℝ) / 2))
  exact ⟨summable_of_history_bound (by linarith) hv hμ hconst
      (fun i ↦ history_cNorm_nonneg r₀ (u i)) hdecay,
    tsum_le_historyBound (by linarith) hv hμ hconst
      (fun i ↦ history_cNorm_nonneg r₀ (u i)) hdecay⟩

/-- `main:eq:total-small`: the total baseline displacement tends to zero, uniformly
for any initial-scale-indexed history satisfying the same constants and Bernstein input. -/
theorem tendsto_periodic_history_total_of_bernstein
    (r₀ : ℕ) {C L v b B k₀ : ℝ} {k : ℝ → ℕ → ℝ}
    {u : ℝ → ℕ → Torus n → F}
    (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)
    (hbernstein : ∀ (M : ℝ), 1 ≤ M → ∀ f : Torus n → F,
      IsSmoothPeriodic f → HasFourierSupport M f →
      cNorm (fundamentalCell n) r₀ (periodicLift f) ≤
        C * M ^ ((r₀ : ℝ) + (n : ℝ) / 2) * periodicL2Norm f)
    (hsmooth : ∀ R, 2 ≤ R → ∀ i, IsSmoothPeriodic (u R i))
    (hsupport : ∀ R, 2 ≤ R → ∀ i,
      HasFourierSupport (L * historyScale R v i ^ b) (u R i))
    (hL2 : ∀ R, 2 ≤ R → ∀ i,
      periodicL2Norm (u R i) ≤ historyScale R v i ^ (-k R i + B + 1))
    (hk : ∀ R, 2 ≤ R → ∀ i, k₀ ≤ k R i) :
    Tendsto (fun R ↦ ∑' i, cNorm (fundamentalCell n) r₀ (periodicLift (u R i)))
      atTop (𝓝 0) := by
  apply tendsto_tsum_of_history_bound hv hμ
    (mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hL)
      ((r₀ : ℝ) + (n : ℝ) / 2)))
  · exact fun R _ i ↦ history_cNorm_nonneg r₀ (u R i)
  · intro R hR
    exact periodic_history_increment_bound_of_bernstein r₀ hR hv hb hL hC
      hbernstein (hsmooth R hR) (hsupport R hR) (hL2 R hR) (hk R hR)

/-- `main:eq:history-current`: a sum of actual higher derivative seminorms has the
fixed-baseline profile, conditional on the two displayed Bernstein estimates.
The constant is independent of both `R₀ ≥ 2` and the finite history length `j`.
The sharp input is at one fixed pair of orders; no extra `n/2` loss is introduced. -/
theorem sum_periodic_history_high_norm_le_of_bernstein
    (r₀ r : ℕ) {C D L R v b B k₀ : ℝ} {k : ℕ → ℝ} {u : ℕ → Torus n → F}
    (hR : 2 ≤ R) (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)
    (hbernstein : ∀ (M : ℝ), 1 ≤ M → ∀ f : Torus n → F,
      IsSmoothPeriodic f → HasFourierSupport M f →
      cNorm (fundamentalCell n) r₀ (periodicLift f) ≤
        C * M ^ ((r₀ : ℝ) + (n : ℝ) / 2) * periodicL2Norm f)
    (hsharp : ∀ (M : ℝ), 1 ≤ M → ∀ f : Torus n → F,
      IsSmoothPeriodic f → HasFourierSupport M f →
      cNorm (fundamentalCell n) r (periodicLift f) ≤
        D * M ^ (r - r₀) * cNorm (fundamentalCell n) r₀ (periodicLift f))
    (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1))
    (hk : ∀ i, k₀ ≤ k i) (j : ℕ) :
    (∑ i ∈ Finset.range j, cNorm (fundamentalCell n) r (periodicLift (u i))) ≤
      ((D * L ^ (r - r₀)) *
        historyBound (C * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)) 2 v
          (k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)) *
        (historyScale R v j ^ (b / v)) ^ (r - r₀) := by
  have hdecay := periodic_history_increment_bound_of_bernstein r₀ hR hv hb hL hC
    hbernstein hsmooth hsupport hL2 hk
  apply sum_history_profile_le hR hv hμ hb
    (mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hL) _))
    (mul_nonneg hD (pow_nonneg (le_trans zero_le_one hL) _))
    (fun i ↦ history_cNorm_nonneg r₀ (u i)) hdecay r r₀ j
  intro i _
  have hscale : 1 ≤ historyScale R v i :=
    Real.one_le_rpow (by linarith) (pow_nonneg (by linarith : 0 ≤ v) i)
  have hband : 1 ≤ L * historyScale R v i ^ b :=
    one_le_mul_of_one_le_of_one_le hL (Real.one_le_rpow hscale hb)
  calc
    cNorm (fundamentalCell n) r (periodicLift (u i)) ≤
        D * (L * historyScale R v i ^ b) ^ (r - r₀) *
          cNorm (fundamentalCell n) r₀ (periodicLift (u i)) :=
      hsharp _ hband _ (hsmooth i) (hsupport i)
    _ = _ := by rw [mul_pow]; ring

end JanetCartan
