module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CurrentNormalComparison.Decay
public import JanetCartan.Analysis.Iteration.ErrorInduction
public import JanetCartan.Analysis.Iteration.MeanRecurrence.EqualGap

/-!
# Numerical budgets for the original canonical scales

For `main:eq:A-choice`, `main:eq:canonical-range` and
`main:lem:mean-recurrence`, derive the contraction and raw-tail thresholds
from the original `forcingExponent`, `fineExponent` and ceiling. The fixed
contraction exponent is independent of the target, history and precision.
The order and dyadic threshold depend only on the finite precision count.

These scalar results supply the numerical premises of
`exists_admissible_history_canonicalRun_precision`; the actual common-event
comparison and primitive raw/inverse estimates remain with their producers.
-/

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean

/-- A fixed contraction exponent below both original decay margins in
`main:lem:mean-recurrence`; it does not change `main:eq:A-choice`. -/
def canonicalContractionExponent : ℝ := 1 / 1040

/-- Positivity of the fixed exponent used in `main:lem:mean-recurrence`. -/
theorem canonicalContractionExponent_pos : 0 < canonicalContractionExponent := by
  norm_num [canonicalContractionExponent]

/-- The original forcing and fine cutoff give the exact nonlinear decay in
`main:eq:A-choice`, in units of the unchanged ceiling `H = R^(1+θ)`. -/
theorem original_forcing_nonlinear_decay (n : ℕ) {R : ℝ} (hR : 0 < R) :
    R ^ (-2 * forcingExponent n) * (R ^ fineExponent) ^ meanDerivativeLoss n =
      (R ^ (1 + meanSlack)) ^ (-((n : ℝ) + 1) / 260) := by
  rw [← Real.rpow_mul hR.le, ← Real.rpow_add hR, ← Real.rpow_mul hR.le]
  congr 1
  dsimp [forcingExponent, meanDerivativeLoss, fineExponent, meanSlack]
  ring

/-- The exact nonlinear margin dominates the fixed normal-comparison decay,
uniformly in dimension (`main:eq:canonical-range`, `main:eq:A-choice`). -/
theorem original_forcing_nonlinear_le_normal_decay (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    R ^ (-2 * forcingExponent n) * (R ^ fineExponent) ^ meanDerivativeLoss n ≤
      (R ^ (1 + meanSlack)) ^
        (-CurrentNormalComparison.normalDecayExponent
          samplingSlack meanSlack separationExponent carrierExponent) := by
  rw [original_forcing_nonlinear_decay n (by linarith),
    CurrentNormalComparison.fixed_normalDecayExponent_eq]
  apply Real.rpow_le_rpow_of_exponent_le
    (Real.one_le_rpow hR (by norm_num [meanSlack]))
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- All scalar contraction budgets for the original scales can be fixed
before the varying source and finite history (`main:lem:mean-recurrence`).
The normal-error input is precisely the common-event comparison decay;
`nonlinearC` is instantiated by the proved raw/measurement constants, not
by an assumed current-mean estimate. The small residual-weight budget is
also discharged from `main:eq:A-choice`. -/
theorem exists_originalScale_canonicalContraction_threshold (n : ℕ)
    (normalC inverseBound nonlinearC : ℝ) (hinverse : 0 ≤ inverseBound)
    (hnonlinear : 0 ≤ nonlinearC) {smallBound : ℝ} (hsmall : 0 < smallBound) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R : ℝ, Rmin ≤ R →
      let H := R ^ (1 + meanSlack)
      let ε := R ^ (-2 * forcingExponent n)
      let Kmax := R ^ fineExponent
      2 ≤ H ∧ 1 ≤ Kmax ∧ H ^ (-canonicalContractionExponent) ≤ 1/2 ∧
        2 * ε * Kmax ^ ((n : ℝ) / 2) ≤ smallBound ∧
        ∀ comparisonError : ℝ,
          comparisonError ≤ normalC * H ^
            (-CurrentNormalComparison.normalDecayExponent
              samplingSlack meanSlack separationExponent carrierExponent) →
          comparisonError * inverseBound + nonlinearC * ε * Kmax ^ meanDerivativeLoss n ≤
            H ^ (-canonicalContractionExponent) / 2 := by
  obtain ⟨Tq, hTq, hq⟩ := exists_rpow_absorption_threshold (a := -canonicalContractionExponent)
    (b := 0) (η := 1/2) 1 (by linarith [canonicalContractionExponent_pos]) (by norm_num)
  obtain ⟨Ts, hTs, hs⟩ := exists_rpow_absorption_threshold (a := -(1/260 : ℝ))
    (b := 0) (η := smallBound) 2 (by norm_num) hsmall
  obtain ⟨Tb, hTb, hb⟩ := exists_rpow_absorption_threshold (a := -(1/260 : ℝ))
    (b := -canonicalContractionExponent) (η := 1/2) (normalC * inverseBound + nonlinearC)
    (by norm_num [canonicalContractionExponent]) (by norm_num)
  refine ⟨max 2 (max Tq (max Ts Tb)), le_max_left _ _, ?_⟩
  intro R hR
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hRH : R ≤ R ^ (1 + meanSlack) := by
    calc
      R = R ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hRone (by norm_num [meanSlack])
  have hK : 1 ≤ R ^ fineExponent := Real.one_le_rpow hRone (by norm_num [fineExponent, meanSlack])
  have hdecay := original_forcing_nonlinear_le_normal_decay n hRone
  rw [CurrentNormalComparison.fixed_normalDecayExponent_eq] at hdecay
  have hTqR : Tq ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hTsR : Ts ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hTbR : Tb ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  refine ⟨hRtwo.trans hRH, hK, ?_, ?_, ?_⟩
  · simpa only [one_mul, Real.rpow_zero, mul_one] using hq _ (hTqR.trans hRH)
  · have hpow : (R ^ fineExponent) ^ ((n : ℝ) / 2) ≤
        (R ^ fineExponent) ^ meanDerivativeLoss n :=
      Real.rpow_le_rpow_of_exponent_le hK (by dsimp [meanDerivativeLoss]; linarith)
    calc
      _ ≤ 2 * (R ^ (-2 * forcingExponent n) * (R ^ fineExponent) ^ meanDerivativeLoss n) := by
        have := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hRpos.le (-2 * forcingExponent n))
        linarith
      _ ≤ 2 * (R ^ (1 + meanSlack)) ^ (-(1/260 : ℝ)) := by gcongr
      _ ≤ smallBound := by simpa only [Real.rpow_zero, mul_one] using hs _ (hTsR.trans hRH)
  · intro comparisonError hcomparison
    rw [CurrentNormalComparison.fixed_normalDecayExponent_eq] at hcomparison
    calc
      _ ≤ (normalC * (R ^ (1 + meanSlack)) ^ (-(1/260 : ℝ))) * inverseBound +
          nonlinearC * (R ^ (1 + meanSlack)) ^ (-(1/260 : ℝ)) := by
        have h₁ := mul_le_mul_of_nonneg_right hcomparison hinverse
        have h₂ := mul_le_mul_of_nonneg_left hdecay hnonlinear
        nlinarith only [h₁, h₂]
      _ = (normalC * inverseBound + nonlinearC) *
          (R ^ (1 + meanSlack)) ^ (-(1/260 : ℝ)) := by ring
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hb _ (hTbR.trans hRH)

/-- The original input and final bands in `main:lem:mean-recurrence` are
exact powers of the SAME ceiling, retaining `fineExponent`. -/
theorem original_mean_bands_eq {R : ℝ} (hR : 0 ≤ R) :
    (R ^ (1 + meanSlack)) ^ (1 / (1 + meanSlack)) = R ∧
      (R ^ (1 + meanSlack)) ^ (fineExponent / (1 + meanSlack)) = R ^ fineExponent := by
  constructor
  · rw [← Real.rpow_mul hR]
    norm_num [meanSlack]
  · rw [← Real.rpow_mul hR]
    congr 1
    norm_num [meanSlack, fineExponent]

/-- The fixed original bands admit all dyadic schedule, carrier plateau and
finite raw-tail threshold conditions in `main:lem:mean-recurrence`. The
threshold is chosen before histories and sources. Only the derivative order
and threshold depend on the requested finite count; neither the masks nor
the original scale exponents change. -/
theorem exists_originalScale_canonicalCutoff_threshold (I : ℕ) (Ctail : ℕ → ℝ)
    {carrierPlateau : ℝ} (hcarrier : 0 < carrierPlateau) :
    let dIn := 1 / (1 + meanSlack)
    let dFinal := fineExponent / (1 + meanSlack)
    let s := MeanRecurrence.EqualGap.tailOrder dIn dFinal canonicalContractionExponent I
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧
      dFinal / 2 + 2 * canonicalContractionExponent + 1 <
        MeanRecurrence.EqualGap.gap dIn dFinal I * s ∧
      ∀ R : ℝ, Rmin ≤ R →
        let H := R ^ (1 + meanSlack)
        let K := MeanRecurrence.EqualGap.cutoff H dIn dFinal I
        (∀ l, 1 ≤ K l) ∧ (∀ i k, i ≤ k → K i ≤ K k) ∧
        (∀ l < I, R ≤ K l ∧ K l ≤ R ^ fineExponent ∧ 1 ≤ carrierPlateau * K l) ∧
        Ctail s ≤ H / 2 := by
  dsimp only
  let dIn := 1 / (1 + meanSlack)
  let dFinal := fineExponent / (1 + meanSlack)
  let s := MeanRecurrence.EqualGap.tailOrder dIn dFinal canonicalContractionExponent I
  have hd : dIn < dFinal := by norm_num [dIn, dFinal, fineExponent, meanSlack]
  have hgap := MeanRecurrence.EqualGap.gap_pos hd I
  refine ⟨max 2 (max (MeanRecurrence.EqualGap.threshold dIn dFinal I)
      (max carrierPlateau⁻¹ (2 * Ctail s))), le_max_left _ _,
    MeanRecurrence.EqualGap.tailOrder_spec hd canonicalContractionExponent I, ?_⟩
  intro R hR
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  let H := R ^ (1 + meanSlack)
  have hRH : R ≤ H := by
    change R ≤ R ^ (1 + meanSlack)
    calc
      _ = R ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hRone (by norm_num [meanSlack])
  have hHone : 1 ≤ H := hRone.trans hRH
  have hHpos : 0 < H := hRpos.trans_le hRH
  have hthreshold : MeanRecurrence.EqualGap.threshold dIn dFinal I ≤ H :=
    (le_max_left _ _).trans (((le_max_right _ _).trans hR).trans hRH)
  have hcarrierR : carrierPlateau⁻¹ ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have htailR : 2 * Ctail s ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hexp (l : ℕ) : dIn ≤ MeanRecurrence.EqualGap.exponent dIn dFinal I l := by
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hgap.le)
  have hlower (l : ℕ) : R ≤ MeanRecurrence.EqualGap.cutoff H dIn dFinal I l := by
    calc
      _ = H ^ dIn := (original_mean_bands_eq hRpos.le).1.symm
      _ ≤ H ^ MeanRecurrence.EqualGap.exponent dIn dFinal I l :=
        Real.rpow_le_rpow_of_exponent_le hHone (hexp l)
      _ ≤ _ := (MeanRecurrence.EqualGap.cutoff_bounds hHpos dIn dFinal I l).1
  refine ⟨fun l ↦ hRone.trans (hlower l), ?_, ?_, by linarith [htailR.trans hRH]⟩
  · intro i k hik
    unfold MeanRecurrence.EqualGap.cutoff
    simp only [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact_mod_cast Int.ceil_mono (Real.logb_le_logb_of_le (by norm_num)
      (Real.rpow_pos_of_pos hHpos _)
      (Real.rpow_le_rpow_of_exponent_le hHone (by
        dsimp only [MeanRecurrence.EqualGap.exponent]
        have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
        nlinarith)))
  · intro l hl
    refine ⟨hlower l, ?_, ?_⟩
    · have h := (MeanRecurrence.EqualGap.cutoff_lt_final hd hl hthreshold).le
      rwa [(original_mean_bands_eq hRpos.le).2] at h
    · calc
        1 = carrierPlateau * carrierPlateau⁻¹ := (mul_inv_cancel₀ hcarrier.ne').symm
        _ ≤ carrierPlateau * R := mul_le_mul_of_nonneg_left hcarrierR hcarrier.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlower l) hcarrier.le

end JanetCartan.CurrentMean
