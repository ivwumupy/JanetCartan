module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets.Derivatives

/-!
# Uniform decay of physical kernel jets across a fixed gap

These estimates supply the uncut kernel jets used by the Leibniz estimate for
the two literal physical tails in `app:ch_regular:eq:resolved-angular-tail`.
The frequency exponent is `n + m`, independently of accuracy, as required by
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Uniform rapid decay of all actual output jets through order `m`. Every
constant is obtained from the fixed smooth compact symbol. The frequency
prefactor `ρ^(n+m)` is independent of the decay order
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_rightLocalizerScalarKernel_jet_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) (m : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 1 ≤ ρ → ∀ j ≤ m, ∀ x y : E,
      (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
        ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖ ≤
          C * ρ ^ (n + m) := by
  intro N
  choose B hB hb using fun j ↦
    PhysicalTailJets.exists_uniform_frequencySlice_fourier_jet_decay mi hi his j N
  let D := fun j ↦ B j / (2 * Real.pi) ^ (n + j)
  have hD j : 0 ≤ D j := div_nonneg (hB j) (by positivity)
  refine ⟨∑ j ∈ Finset.range (m + 1), D j, Finset.sum_nonneg (fun j _ ↦ hD j), ?_⟩
  intro ρ hρ j hj x y
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  rw [norm_iteratedFDeriv_rightLocalizerScalarKernel_eq_fourier hρpos mi hi his]
  have h := hb j y (-(ρ / (2 * Real.pi)) • (x - y))
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / (2 * Real.pi))] at h
  calc
    _ = (ρ / (2 * Real.pi)) ^ (n + j) *
        ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          ‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ)))
            (-(ρ / (2 * Real.pi)) • (x - y))‖) := by ring
    _ ≤ (ρ / (2 * Real.pi)) ^ (n + j) * B j :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = D j * ρ ^ (n + j) := by dsimp [D]; rw [div_pow]; ring
    _ ≤ (∑ k ∈ Finset.range (m + 1), D k) * ρ ^ (n + m) :=
      mul_le_mul (Finset.single_le_sum (fun k _ ↦ hD k) (Finset.mem_range.mpr (by omega)))
        (pow_le_pow_right₀ hρ (Nat.add_le_add_left hj n)) (by positivity)
        (Finset.sum_nonneg (fun k _ ↦ hD k))

/-- A fixed physical separation gives arbitrary frequency decay for every
output jet, retaining the requested spatial weight. This is the uncut input
to the physical-tail Leibniz estimate (`app:ch_regular:eq:chain-tail`). -/
theorem exists_rightLocalizerScalarKernel_separated_jet_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    {δ : ℝ} (hδ : 0 < δ) (m M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ j ≤ m, ∀ x y : E, δ ≤ ‖x - y‖ →
      (1 + ‖x - y‖) ^ M *
        ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖ ≤
          C * ρ ^ (n + m) * (L / ρ) ^ N := by
  intro N
  obtain ⟨B, hB, hb⟩ := exists_rightLocalizerScalarKernel_jet_decay mi hi his m (N + M)
  let a := δ / (2 * Real.pi)
  let c := min 1 (1 / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let D := a ^ N * c ^ M
  have hD : 0 < D := mul_pos (pow_pos ha _) (pow_pos hc _)
  refine ⟨B / D, div_nonneg hB hD.le, ?_⟩
  intro ρ L hL hLρ j hj x y hgap
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hfreq : ρ * a ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
    calc
      ρ * a = ρ / (2 * Real.pi) * δ := by dsimp [a]; ring
      _ ≤ ρ / (2 * Real.pi) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ ≤ _ := by linarith
  have hcρ : c ≤ ρ / (2 * Real.pi) :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right hρ (by positivity))
  have hspace : c * (1 + ‖x - y‖) ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
    calc
      _ = c + c * ‖x - y‖ := by ring
      _ ≤ _ := add_le_add (min_le_left _ _)
        (mul_le_mul_of_nonneg_right hcρ (norm_nonneg _))
  have hcombined :
      (ρ ^ N * D) * ((1 + ‖x - y‖) ^ M *
        ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖) ≤
          B * ρ ^ (n + m) := by
    calc
      _ = ((ρ * a) ^ N * (c * (1 + ‖x - y‖)) ^ M) *
          ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖ := by
            dsimp [D]
            simp only [mul_pow]
            ring
      _ ≤ ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ M) *
            ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖ := by gcongr
      _ ≤ B * ρ ^ (n + m) := by rw [← pow_add]; exact hb ρ hρ j hj x y
  have hdiv := (le_div_iff₀ (mul_pos (pow_pos hρpos N) hD)).mpr
    (show ((1 + ‖x - y‖) ^ M *
      ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖) *
        (ρ ^ N * D) ≤ B * ρ ^ (n + m) by simpa only [mul_comm] using hcombined)
  calc
    _ ≤ (B * ρ ^ (n + m)) / (ρ ^ N * D) := hdiv
    _ = (B / D) * ρ ^ (n + m) * (1 / ρ) ^ N := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := by gcongr

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
