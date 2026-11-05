module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.HighFrequency
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Ordinary
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.SobolevScale

/-!
# The actual terminal angular defect on a protected localizer

For `app:ch_regular:eq:resolved-angular-tail` and the full terminal instance of
`app:ch_regular:eq:chain-tail`, the two concrete physical-tail producers give
the estimate for the literal `actualAngularPDO` and its literal Hilbert adjoint.
The source mask stays BEFORE the Fourier factor. The identity is subtracted
once from the full operator, which retains the original low-frequency bump.

The high-frequency leaf retains the explicit threshold `2*radialThreshold/lo`.
Below that threshold the ordinary uncut-localizer and fixed-mask estimates
give the same conclusion with an accuracy-dependent constant. The losses are
`c = d+1+m`, `b = 0`, independently of accuracy, for every `1 ≤ L ≤ ρ`.

Only primitive geometric data remain for the parent: the SAME finite sector
family, smooth compact proof symbol, strict angular plateau, positive annular
lower bound, physical plateaux of BOTH original masks, and the literal bounded
left-localizer action. `ProtectedMasks` and the sector family supply the
geometry; the bounded-localizer constructor supplies the action. Applying
these results to the current history and assembling principal leakage remains
the parent's obligation. No kernel decay, Sobolev membership or analytic
operator bound is an input here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph LowBounds Pseudodifferential RegularSector.FiniteMasks
open LocalSobolev
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Arbitrary accuracy for the FULL actual terminal angular defect on the
original right localizer, including bounded frequencies and both literal
orientations. The loss `d+1+m` and coefficient loss zero are independent of
`N`. All masks and the original finite symbol are fixed before accuracy,
frequency and datum. This supplies the global estimate behind
`finiteChain_observation_rapidDecayAt.hBnear`
(`app:ch_regular:eq:resolved-angular-tail`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_actualAngularPDO_sub_identity_sobolev_decay
    {Ω : Set E} {center : E} {RQ Mbound : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K Mbound) (backward : Bool)
    (mi : LocalizerSymbol (d + 1)) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo)
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hang : ∀ p ∈ tsupport mi,
      NormedSpace.normalize p.2 ∈ interior {η | ∑ i, f.angularMask i η = 1})
    (hout : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | f.outputMask x = 1})
    (hsource : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | f.inputMask x = 1})
    (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        let P := if backward then (actualAngularPDO (r := r) f).adjoint else actualAngularPDO f
        MemVectorFourierSobolev (m : ℝ) (((P - 1).comp M.adjoint) u) ∧
        vectorFourierSobolevNorm (m : ℝ) (((P - 1).comp M.adjoint) u) ≤
          C * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨A, hA, ha⟩ := exists_actualAngularPDO_sub_identity_sobolev_decay_high
    (r := r) f backward mi hi his hlo hann hang hout hsource m N
  obtain ⟨D, hD, hd⟩ := exists_actualAngularPDO_sub_identity_sobolev_bound (r := r) f backward m
  obtain ⟨S, hS, hs⟩ := exists_leftLocalizer_adjoint_sobolev_bound (r := r) mi hi his m
  let T := max 1 (2 * f.radialThreshold / lo)
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨max A (D * S * T ^ N), le_trans hA (le_max_left _ _), ?_⟩
  intro ρ L hL hLρ M hM u P
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  by_cases hh : 2 * f.radialThreshold / lo < ρ
  · obtain ⟨hm, hn⟩ := ha ρ L hL hLρ hh M hM u
    refine ⟨hm, hn.trans ?_⟩
    gcongr
    exact le_max_left _ _
  · have hρT : ρ ≤ T := (le_of_not_gt hh).trans (le_max_right _ _)
    obtain ⟨hsm, hsn⟩ := hs ρ hρ M hM u
    obtain ⟨hm, hn⟩ := hd (M.adjoint u) hsm
    have hratio : 1 ≤ T * (L / ρ) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hρpos).mpr
      calc
        1 * ρ = ρ := one_mul _
        _ ≤ T := hρT
        _ ≤ T * L := by nlinarith
    have hpow : 1 ≤ T ^ N * (L / ρ) ^ N := by
      simpa only [mul_pow] using one_le_pow₀ hratio
    refine ⟨hm, ?_⟩
    calc
      _ ≤ D * (S * ρ ^ (d + 1 + m) * ‖u‖) :=
        hn.trans (mul_le_mul_of_nonneg_left hsn hD)
      _ = (D * S * ρ ^ (d + 1 + m) * ‖u‖) * 1 := by ring
      _ ≤ (D * S * ρ ^ (d + 1 + m) * ‖u‖) * (T ^ N * (L / ρ) ^ N) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (D * S * T ^ N) * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖ := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- The matching actual restriction-space estimate. The output `v` is only
required to be the literal restriction of the SAME global output; all its
Sobolev membership and norm bounds are conclusions. The fixed losses are
written in the form consumed by `finiteChain_observation_rapidDecayAt.hBnear`.
The parent still instantiates its current-history masks and restricted
operators (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_actualAngularPDO_sub_identity_restriction_decay
    {Ω : Set E} {center : E} {RQ Mbound : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K Mbound) (backward : Bool)
    (mi : LocalizerSymbol (d + 1)) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo)
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hang : ∀ p ∈ tsupport mi,
      NormedSpace.normalize p.2 ∈ interior {η | ∑ i, f.angularMask i η = 1})
    (hout : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | f.outputMask x = 1})
    (hsource : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | f.inputMask x = 1})
    (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ (u : H) (U : Set E) (hU : MeasurableSet U) (v : LocalL2 U V),
        let P := if backward then (actualAngularPDO (r := r) f).adjoint else actualAngularPDO f
        ((((P - 1).comp M.adjoint) u : H) : E → V) =ᵐ[volume.restrict U] v →
        v ∈ (restrictionSobolevScale U V hU).level m ∧
        (restrictionSobolevScale U V hU).gradeNorm m v ≤
          C * ρ ^ ((d + 1 + m : ℕ) : ℝ) * L ^ (0 : ℕ) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨A, hA, ha⟩ := exists_actualAngularPDO_sub_identity_sobolev_decay
    (r := r) f backward mi hi his hlo hann hang hout hsource m N
  obtain ⟨D, hD, hd⟩ := exists_restrictionScale_fourier_comparison (d + 1) r m
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro ρ L hL hLρ M hM u U hU v P hv
  obtain ⟨hm, hn⟩ := ha ρ L hL hLρ M hM u
  obtain ⟨hvm, hvn⟩ := hd U hU _ v hm hv
  refine ⟨hvm, hvn.trans ?_⟩
  simpa only [Real.rpow_natCast, pow_zero, mul_one, mul_assoc] using
    mul_le_mul_of_nonneg_left hn hD.le

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
