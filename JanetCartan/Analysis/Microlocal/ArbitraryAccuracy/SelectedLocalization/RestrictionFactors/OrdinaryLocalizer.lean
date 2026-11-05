module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Sobolev

/-!
# An ordinary left-localizer cost from the compact symbol

The cross Fourier kernel with zero complementary symbol is exactly the
ordinary left quantization. Its primitive Fourier decay and compact input
frequency support give the L² to Hᵐ estimate needed AFTER the hard L² boundary
projection in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set Metric
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds FiniteChain.Graph Pseudodifferential
open FiniteChains.CrossQuantization
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Uniform ordinary Sobolev cost of the actual left quantization. The
constant precedes the symbol, scales and bounded realization and depends
only on its primitive carrier, frequency radius and derivative profile.
Consumer: smoothing the discarded L² boundary tail in the residual factor
estimate (`app:ch_regular:eq:chain-tail`). -/
theorem exists_leftLocalizer_primitive_sobolev_bound
    (K : Set E) (hK : IsCompact K) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (b : ℕ) {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mi : LocalizerSymbol n), ContDiff ℝ ∞ mi →
      HasCompactSupport mi → Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ‖p.2‖ ≤ R) →
      ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ D k * L ^ (k + b)) →
      ∀ M : H →L[ℂ] H,
      (∀ u, (∀ a, Integrable (fun y ↦ u y a)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u, MemVectorFourierSobolev (m : ℝ) (M u) ∧
        vectorFourierSobolevNorm (m : ℝ) (M u) ≤
          C * ρ ^ m * L ^ (m + (n + 1) + b) * ‖u‖ := by
  obtain ⟨B, hB, hb⟩ := exists_crossQuantizationFourierKernel_frequency_decay
    K hK D (fun _ ↦ 0) hD (fun _ ↦ le_rfl) b 0
  obtain ⟨S, hS, hs⟩ := exists_channelFourierKernel_sobolev_constant (n := n) (r := r) m
  let c : ℝ := min 1 (1 / (2 * Real.pi))
  have hc : 0 < c := by dsimp [c]; positivity
  let J := m + (n + 1)
  let C := (1 + R) ^ m * (B J / c ^ J)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (div_nonneg (hB J) (pow_nonneg hc.le _))
  refine ⟨S * C, mul_nonneg hS hC, ?_⟩
  intro mi hi his hcarrier hann ρ L hρ hL hij M hM u
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  let k := crossQuantizationFourierKernel ρ mi (fun _ ↦ 0)
  have hkernel (ξ η : E) : (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) * ‖k ξ η‖ ≤
      C * ρ ^ m * L ^ (m + (n + 1) + b) := by
    have hzero : ∀ j (p : E × E), ‖iteratedFDeriv ℝ j (fun _ : E × E ↦ (0 : ℝ)) p‖ ≤
        0 * L ^ (j + 0) := by simp
    have hbase := hb mi (fun _ ↦ 0) hi contDiff_const hcarrier ρ L hL hij hzero J ξ η
    simp only [zero_add] at hbase
    have hspace : c * (1 + ‖ξ - η‖) ≤ 1 + ‖(2 * Real.pi)⁻¹ • (ξ - η)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
      have hc' : c ≤ (2 * Real.pi)⁻¹ := by
        simpa only [c, one_div] using min_le_right (1 : ℝ) (1 / (2 * Real.pi))
      calc
        _ = c + c * ‖ξ - η‖ := by ring
        _ ≤ _ := add_le_add (min_le_left _ _)
          (mul_le_mul_of_nonneg_right hc' (norm_nonneg _))
    have hdecay : (1 + ‖ξ - η‖) ^ J * ‖k ξ η‖ ≤ (B J / c ^ J) * L ^ (J + b) := by
      have hh : c ^ J * ((1 + ‖ξ - η‖) ^ J * ‖k ξ η‖) ≤ B J * L ^ (J + b) := by
        calc
          _ = (c * (1 + ‖ξ - η‖)) ^ J * ‖k ξ η‖ := by rw [mul_pow]; ring
          _ ≤ (1 + ‖(2 * Real.pi)⁻¹ • (ξ - η)‖) ^ J * ‖k ξ η‖ := by gcongr
          _ ≤ _ := hbase
      have hd := (le_div_iff₀ (pow_pos hc J)).mpr
        (show ((1 + ‖ξ - η‖) ^ J * ‖k ξ η‖) * c ^ J ≤ B J * L ^ (J + b) by
          simpa only [mul_comm] using hh)
      exact hd.trans_eq (by ring)
    by_cases hz : k ξ η = 0
    · rw [hz, norm_zero, mul_zero]
      positivity
    have hη : ρ⁻¹ • η ∈ Prod.snd '' tsupport mi := by
      by_contra hh
      exact hz (crossQuantizationFourierKernel_zero_off_input ρ mi (fun _ ↦ 0) ξ η hh)
    obtain ⟨p, hp, he⟩ := hη
    have hηnorm : ‖η‖ ≤ ρ * R := by
      have hsmall : ‖ρ⁻¹ • η‖ ≤ R := he ▸ hann p hp
      have hid : η = ρ • (ρ⁻¹ • η) := by simp [smul_smul, hρpos.ne']
      calc
        ‖η‖ = ρ * ‖ρ⁻¹ • η‖ := by
          conv_lhs => rw [hid]
          rw [norm_smul, Real.norm_of_nonneg hρpos.le]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hρpos.le
    have heta : 1 + ‖η‖ ≤ (1 + R) * ρ := by nlinarith
    have hxi : 1 + ‖ξ‖ ≤ ((1 + R) * ρ) * (1 + ‖ξ - η‖) := by
      have hn : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
        simpa only [sub_add_cancel] using norm_add_le (ξ - η) η
      calc
        _ ≤ (1 + ‖η‖) * (1 + ‖ξ - η‖) := by
          nlinarith [mul_nonneg (norm_nonneg η) (norm_nonneg (ξ - η))]
        _ ≤ _ := mul_le_mul_of_nonneg_right heta (by positivity)
    calc
      _ ≤ (((1 + R) * ρ) * (1 + ‖ξ - η‖)) ^ m *
          (1 + ‖ξ - η‖) ^ (n + 1) * ‖k ξ η‖ := by gcongr
      _ = ((1 + R) ^ m * ρ ^ m) * ((1 + ‖ξ - η‖) ^ J * ‖k ξ η‖) := by
        simp only [J, pow_add, mul_pow]
        ring
      _ ≤ ((1 + R) ^ m * ρ ^ m) * ((B J / c ^ J) * L ^ (J + b)) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by dsimp [C, J]; ring
  have hzero : ∀ v : H, (0 : H →L[ℂ] H) v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ (fun _ ↦ 0) (fun y ↦ (v y).ofLp) x) := by
    intro v
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)] with x hx
    simp [rightLocalizer, graphOperator]
  have haction := bounded_crossQuantization_schwartz_fourier_action hρpos.ne'
    mi (fun _ ↦ 0) hi his contDiff_const (HasCompactSupport.intro isCompact_empty (fun _ _ ↦ rfl))
    M 0 hM hzero
  simp only [sub_zero, one_apply_eq_self] at haction
  obtain ⟨hm, hn⟩ := hs k
    (contDiff_crossQuantizationFourierKernel ρ mi (fun _ ↦ 0) hi his contDiff_const).continuous.stronglyMeasurable
    (C * ρ ^ m * L ^ (m + (n + 1) + b)) (by positivity) hkernel M haction u
  exact ⟨hm, hn.trans_eq (by ring)⟩

/-- A fixed compact smooth left symbol supplies its own ordinary cost:
`C ρ^m`, with C independent of frequency and accuracy. This instantiates
the primitive profile theorem, so no localizer estimate is left as an
analytic premise of the boundary correction (`app:ch_regular:eq:chain-tail`). -/
theorem exists_leftLocalizer_fixed_sobolev_bound
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ M : H →L[ℂ] H,
      (∀ u, (∀ a, Integrable (fun y ↦ u y a)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u, MemVectorFourierSobolev (m : ℝ) (M u) ∧
        vectorFourierSobolevNorm (m : ℝ) (M u) ≤ C * ρ ^ m * ‖u‖ := by
  choose D hD hd using fun k ↦ his.exists_bound_iteratedFDeriv hi k
  obtain ⟨R, hR, hball⟩ := (his.image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : E)
  obtain ⟨C, hC, h⟩ := exists_leftLocalizer_primitive_sobolev_bound
    (r := r) (Prod.fst '' tsupport mi) (his.image continuous_fst) D
    hD 0 hR.le m
  refine ⟨C, hC, ?_⟩
  intro ρ hρ M hM u
  have hann p (hp : p ∈ tsupport mi) : ‖p.2‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hball ⟨p, hp, rfl⟩
  have hj k p : ‖iteratedFDeriv ℝ k mi p‖ ≤ D k * (1 : ℝ) ^ (k + 0) := by
    simpa only [one_pow, mul_one] using hd k k le_rfl p
  simpa only [one_pow, mul_one] using h mi hi his Subset.rfl hann ρ 1 hρ le_rfl hj M hM u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
