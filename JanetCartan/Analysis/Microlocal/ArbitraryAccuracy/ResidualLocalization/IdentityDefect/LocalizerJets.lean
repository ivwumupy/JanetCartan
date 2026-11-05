module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerJets.Derivatives

/-!
# Rapid decay of all same-localizer identity jets

The strict diagonal plateau cancels every jet on one fixed neighborhood.
The exact Fourier jet formula gives arbitrary decay away from that
neighborhood. Consumer: the identity summand in principal-defect leakage
in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph
variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem multilinear_norm_le_unit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ v, (∀ i, ‖v i‖ ≤ 1) → ‖f v‖ ≤ D) : ‖f‖ ≤ D := by
  apply f.opNorm_le_bound hD
  intro v
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [f.map_coord_zero i hi, norm_zero]
    positivity
  · push Not at hz
    have hv i : ‖(‖v i‖⁻¹ : ℝ) • v i‖ ≤ 1 := (norm_smul_inv_norm (hz i)).le
    have he : v = fun i => ‖v i‖ • ((‖v i‖⁻¹ : ℝ) • v i) := by
      funext i
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz i)), one_smul]
    calc
      ‖f v‖ = (∏ i, ‖v i‖) * ‖f (fun i => (‖v i‖⁻¹ : ℝ) • v i)‖ := by
        conv_lhs => rw [he, f.map_smul_univ, norm_smul]
        rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))]
      _ ≤ (∏ i, ‖v i‖) * D := mul_le_mul_of_nonneg_left (hb _ hv)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      _ = _ := mul_comm _ _

/-- Uniform rapid decay of all output jets of the literal identity leakage.
The prefactor `ρ^(n+m)` is fixed before accuracy; the constants are produced
from the original compact smooth masks (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_jet_decay
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo) (m : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 1 ≤ ρ → ∀ j ≤ m, ∀ x y : E,
      (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
        ‖iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x‖ ≤
          C * ρ ^ (n + m) := by
  intro N
  choose B hB hb using fun j ↦
    exists_identityLeakageJetAmplitude_fourier_decay mi mo hi his ho hos j N
  let D := fun j ↦ B j / (2 * Real.pi) ^ n
  have hD j : 0 ≤ D j := div_nonneg (hB j) (by positivity)
  let C := ∑ j ∈ Finset.range (m + 1), D j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ ↦ hD j)
  refine ⟨C, hC, ?_⟩
  intro ρ hρ j hj x y
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  let w := (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N
  have hw : 0 < w := by dsimp [w]; positivity
  have heval (v : Fin j → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
      w * ‖iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x v‖ ≤
        C * ρ ^ (n + m) := by
    rw [iteratedFDeriv_identityLeakageScalarKernel_apply_eq_fourier hρpos mi mo hi his ho,
      norm_smul, Real.norm_of_nonneg (by positivity :
        0 ≤ (ρ / (2 * Real.pi)) ^ n * ρ ^ j)]
    have h := hb j ρ hρ x y v hv (-(ρ / (2 * Real.pi)) • (x - y))
    rw [norm_smul, norm_neg,
      Real.norm_of_nonneg (by positivity : 0 ≤ ρ / (2 * Real.pi))] at h
    calc
      _ = ((ρ / (2 * Real.pi)) ^ n * ρ ^ j) *
          (w * ‖𝓕 (identityLeakageJetAmplitude ρ mi mo x y j v)
            (-(ρ / (2 * Real.pi)) • (x - y))‖) := by ring
      _ ≤ ((ρ / (2 * Real.pi)) ^ n * ρ ^ j) * B j :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = D j * ρ ^ (n + j) := by dsimp [D]; rw [div_pow, pow_add]; ring
      _ ≤ C * ρ ^ (n + m) := mul_le_mul
        (Finset.single_le_sum (fun k _ ↦ hD k) (Finset.mem_range.mpr (by omega)))
        (pow_le_pow_right₀ hρ (Nat.add_le_add_left hj n)) (by positivity) hC
  have hn := multilinear_norm_le_unit
    (iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x)
    (D := C * ρ ^ (n + m) / w) (by positivity)
    (fun v hv ↦ (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using heval v hv))
  exact (mul_le_mul_of_nonneg_left hn hw.le).trans_eq (by field_simp)

/-- Every derivative vanishes on a fixed diagonal neighborhood, because the
full same-mask kernel itself vanishes on the original larger neighborhood.
This uses actual plateau cancellation, not separate low estimates for the
identity and the output localizer (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_jet_zero_near_diagonal
    (mi mo : LocalizerSymbol n) (his : HasCompactSupport mi)
    (hplateau : tsupport mi ⊆ interior {p | mo p = 1}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : ℝ) (j : ℕ) (x y : E), ‖x - y‖ ≤ δ →
      iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x = 0 := by
  obtain ⟨δ, hδ, hz⟩ := exists_identityLeakageScalarKernel_zero_near_diagonal mi mo his hplateau
  refine ⟨δ / 2, by positivity, ?_⟩
  intro ρ j x y hxy
  have hlt : ‖x - y‖ < δ := lt_of_le_of_lt hxy (by linarith)
  have he : (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
    filter_upwards [(isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).eventually_mem hlt]
      with z hz'
    exact hz ρ z y hz'.le
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- The SAME strict buffered plateau and fixed smooth masks produce arbitrary
weighted decay for all output jets of the literal identity leakage.
The polynomial loss `ρ^(n+m)` is independent of accuracy (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_buffered_jet_decay
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo)
    (hplateau : tsupport mi ⊆ interior {p | mo p = 1}) (m M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ j ≤ m, ∀ x y : E,
      (1 + ‖x - y‖) ^ M *
        ‖iteratedFDeriv ℝ j (fun x ↦ identityLeakageScalarKernel ρ mi mo x y) x‖ ≤
          C * ρ ^ (n + m) * (L / ρ) ^ N := by
  obtain ⟨δ, hδ, hz⟩ := exists_identityLeakageScalarKernel_jet_zero_near_diagonal mi mo his hplateau
  intro N
  obtain ⟨B, hB, hb⟩ := exists_identityLeakageScalarKernel_jet_decay mi mo hi his ho hos m (N + M)
  let a := δ / (2 * Real.pi)
  let c := min 1 (1 / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let D := a ^ N * c ^ M
  have hD : 0 < D := mul_pos (pow_pos ha _) (pow_pos hc _)
  refine ⟨B / D, div_nonneg hB hD.le, ?_⟩
  intro ρ L hL hLρ j hj x y
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  by_cases hxy : ‖x - y‖ ≤ δ
  · rw [hz ρ j x y hxy, norm_zero, mul_zero]
    positivity
  have hgap : δ ≤ ‖x - y‖ := (lt_of_not_ge hxy).le
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
        ‖iteratedFDeriv ℝ j (fun x ↦ identityLeakageScalarKernel ρ mi mo x y) x‖) ≤
          B * ρ ^ (n + m) := by
    calc
      _ = ((ρ * a) ^ N * (c * (1 + ‖x - y‖)) ^ M) *
          ‖iteratedFDeriv ℝ j (fun x ↦ identityLeakageScalarKernel ρ mi mo x y) x‖ := by
            dsimp [D]
            simp only [mul_pow]
            ring
      _ ≤ ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ M) *
            ‖iteratedFDeriv ℝ j (fun x ↦ identityLeakageScalarKernel ρ mi mo x y) x‖ := by gcongr
      _ ≤ B * ρ ^ (n + m) := by rw [← pow_add]; exact hb ρ hρ j hj x y
  have hdiv := (le_div_iff₀ (mul_pos (pow_pos hρpos N) hD)).mpr
    (show ((1 + ‖x - y‖) ^ M *
      ‖iteratedFDeriv ℝ j (fun x ↦ identityLeakageScalarKernel ρ mi mo x y) x‖) *
        (ρ ^ N * D) ≤ B * ρ ^ (n + m) by simpa only [mul_comm] using hcombined)
  calc
    _ ≤ (B * ρ ^ (n + m)) / (ρ ^ N * D) := hdiv
    _ = (B / D) * ρ ^ (n + m) * (1 / ρ) ^ N := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := by gcongr


end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
