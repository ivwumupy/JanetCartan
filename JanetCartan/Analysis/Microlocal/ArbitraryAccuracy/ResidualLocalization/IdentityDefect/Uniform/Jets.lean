module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.Uniform.Fourier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerJets.Derivatives

/-!
# Uniform output jets for the same-mask identity leakage

The common profiles and explicit diagonal buffer give constants before the
proof masks vary. The literal identity complement is retained throughout.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph
variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Unit-direction bounds control the same multilinear identity jet
(`app:ch_regular:eq:chain-tail`). -/
private theorem identityJet_norm_le_of_unit_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

/-- All output jets have one decay constant for the common frequency carrier
and derivative profiles, chosen before either mask. The source is the exact
Fourier identity for the differentiated kernel, with no assumed kernel bound.
Consumer: buffered identity leakage (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_jet_decay_of_uniform_profiles
    (R : ℝ) (I O : ℕ → ℝ) (hI : ∀ k, 0 ≤ I k) (hO : ∀ k, 0 ≤ O k) (m : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → Prod.snd '' tsupport mi ⊆ Metric.closedBall (0 : E) R →
      (∀ k z, ‖iteratedFDeriv ℝ k mi z‖ ≤ I k) →
      (∀ k z, ‖iteratedFDeriv ℝ k mo z‖ ≤ O k) →
      ∀ (ρ : ℝ), 1 ≤ ρ → ∀ j ≤ m, ∀ x y : E,
      (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
        ‖iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x‖ ≤
          C * ρ ^ (n + m) := by
  intro N
  choose B hB hb using fun j ↦
    exists_identityLeakageJetAmplitude_fourier_decay_of_uniform_profiles R I O hI hO j N
  let D := fun j ↦ B j / (2 * Real.pi) ^ n
  have hD j : 0 ≤ D j := div_nonneg (hB j) (by positivity)
  let C := ∑ j ∈ Finset.range (m + 1), D j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ ↦ hD j)
  refine ⟨C, hC, ?_⟩
  intro mi mo hi his ho hfreq hiBound hoBound ρ hρ j hj x y
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  let w := (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N
  have hw : 0 < w := by dsimp [w]; positivity
  have heval (v : Fin j → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
      w * ‖iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x v‖ ≤
        C * ρ ^ (n + m) := by
    rw [iteratedFDeriv_identityLeakageScalarKernel_apply_eq_fourier hρpos mi mo hi his ho,
      norm_smul, Real.norm_of_nonneg (by positivity :
        0 ≤ (ρ / (2 * Real.pi)) ^ n * ρ ^ j)]
    have h := hb j mi mo hi his ho hfreq hiBound hoBound ρ hρ x y v hv (-(ρ / (2 * Real.pi)) • (x - y))
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
  have hn := identityJet_norm_le_of_unit_bounds
    (iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x)
    (D := C * ρ ^ (n + m) / w) (by positivity)
    (fun v hv ↦ (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using heval v hv))
  exact (mul_le_mul_of_nonneg_left hn hw.le).trans_eq (by field_simp)

/-- The selected closed diagonal buffer kills every identity jet on the
SAME half-buffer. This uses the actual plateau from the nested even masks;
no vanishing kernel is an input (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem identityLeakageScalarKernel_jet_zero_of_uniform_buffer
    (mi mo : LocalizerSymbol n) {δ : ℝ} (hδ : 0 < δ)
    (hbuffer : ∀ p ∈ tsupport mi, Metric.closedBall p δ ⊆ interior {p | mo p = 1}) :
    ∀ (ρ : ℝ) (j : ℕ) (x y : E), ‖x - y‖ ≤ δ / 2 →
      iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x = 0 := by
  have hcancel (x y : E) (hxy : ‖x - y‖ ≤ δ) (η : E) :
      (1 - mo (x, η)) * mi (y, η) = 0 := by
    by_cases hi : mi (y, η) = 0
    · rw [hi, mul_zero]
    have hp := hbuffer (y, η) (subset_tsupport mi hi)
    have hmem : (x, η) ∈ Metric.closedBall (y, η) δ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def] using hxy
    have hmo : (x, η) ∈ {p | mo p = 1} := interior_subset (hp hmem)
    rw [hmo, sub_self, zero_mul]
  have hz (ρ : ℝ) (x y : E) (hxy : ‖x - y‖ ≤ δ) :
      identityLeakageScalarKernel ρ mi mo x y = 0 := by
    simp only [identityLeakageScalarKernel, hcancel x y hxy, Complex.ofReal_zero,
      mul_zero, integral_zero]
  intro ρ j x y hxy
  have hlt : ‖x - y‖ < δ := lt_of_le_of_lt hxy (half_lt_self hδ)
  have he : (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
    filter_upwards [(isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).eventually_mem hlt]
      with z hz'
    exact hz ρ z y hz'.le
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- The published common mask profiles and common positive buffer produce
arbitrary weighted decay of every literal identity jet, uniformly over masks.
Constants precede the varying coefficients through their mask witnesses.
Consumer: the identity summand of complete residual leakage
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_buffered_jet_decay_of_uniform_profiles
    (R : ℝ) (I O : ℕ → ℝ) (hI : ∀ k, 0 ≤ I k) (hO : ∀ k, 0 ≤ O k)
    {buffer : ℝ} (hbuffer : 0 < buffer) (m M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → Prod.snd '' tsupport mi ⊆ Metric.closedBall (0 : E) R →
      (∀ k z, ‖iteratedFDeriv ℝ k mi z‖ ≤ I k) →
      (∀ k z, ‖iteratedFDeriv ℝ k mo z‖ ≤ O k) →
      (∀ p ∈ tsupport mi, Metric.closedBall p buffer ⊆ interior {p | mo p = 1}) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ j ≤ m, ∀ x y : E,
      (1 + ‖x - y‖) ^ M *
        ‖iteratedFDeriv ℝ j (fun x ↦ identityLeakageScalarKernel ρ mi mo x y) x‖ ≤
          C * ρ ^ (n + m) * (L / ρ) ^ N := by
  let δ := buffer / 2
  have hδ : 0 < δ := half_pos hbuffer
  intro N
  obtain ⟨B, hB, hb⟩ := exists_identityLeakageScalarKernel_jet_decay_of_uniform_profiles R I O hI hO m (N + M)
  let a := δ / (2 * Real.pi)
  let c := min 1 (1 / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let D := a ^ N * c ^ M
  have hD : 0 < D := mul_pos (pow_pos ha _) (pow_pos hc _)
  refine ⟨B / D, div_nonneg hB hD.le, ?_⟩
  intro mi mo hi his ho hfreq hiBound hoBound hplateau ρ L hL hLρ j hj x y
  have hz := identityLeakageScalarKernel_jet_zero_of_uniform_buffer mi mo hbuffer hplateau
  have hb := hb mi mo hi his ho hfreq hiBound hoBound
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
