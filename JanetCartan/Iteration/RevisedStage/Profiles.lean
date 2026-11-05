module

public import JanetCartan.Iteration.RevisedStage.Metric

/-!
# The actual secondary derivative profile in the revised step

For §15 Steps 4--5 of `paper-v2.tex`, the lower primary, mean, and pair
profiles yield the precise common exponent `B₀ + am₀`. In particular, the
secondary derivative bound is proved for `W = b² V + S`, not put in a new
record. The lower derivative estimates are the explicit consumers of the
still-separate physical `H^m₀ → C¹` theorem and the actual wave/response
Sobolev estimates; no periodic Sobolev norm is substituted.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RevisedStage

variable {n N : ℕ}

/-- §15 Steps 4--5: the sharper primary profile with its `λ⁻¹` factor fits
the exact revised common derivative loss without changing the field. -/
theorem fderiv_primary_le_of_profile
    {P : Euclidean n → Euclidean N} {x : Euclidean n} {CP δ R : ℝ}
    (hCP : 0 ≤ CP) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (hP : ‖fderiv ℝ P x‖ ≤ CP * δ *
      R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1)) :
    ‖fderiv ℝ P x‖ ≤ CP * δ * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 ≤ RevisedScales.forcingExponent n := by
    unfold RevisedScales.forcingExponent
    positivity
  have he : RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 +
      carrierExponent * ((RevisedScales.baselineOrder n : ℝ) - 1) ≤
      RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n := by
    unfold RevisedScales.displacementLoss
    norm_num [samplingSlack, carrierExponent]
    linarith
  calc
    _ ≤ CP * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1) := hP
    _ = CP * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 +
        carrierExponent * ((RevisedScales.baselineOrder n : ℝ) - 1)) := by
      rw [← Real.rpow_mul hRp.le, mul_assoc (CP * δ), ← Real.rpow_add hRp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR he)
      (mul_nonneg hCP hδ)

/-- §15 Steps 4--5: the SAME secondary `W = b²V+S` satisfies the derivative
profile by adding the actual scaled mean and pair derivatives. The pair term
has exactly `B₀ = 2A+1+ε+a`, not a relaxed exponent. -/
theorem fderiv_secondary_le_of_profiles
    {V S W : Euclidean n → Euclidean N} {x : Euclidean n} {b CV CS δ R : ℝ}
    (hCV : 0 ≤ CV) (hR : 1 ≤ R)
    (hb : b = δ * R ^ RevisedScales.forcingExponent n)
    (hV : DifferentiableAt ℝ V x) (hS : DifferentiableAt ℝ S x)
    (hW : W = b ^ 2 • V + S)
    (hDV : ‖fderiv ℝ V x‖ ≤ CV * R ^ (RevisedScales.baselineOrder n : ℝ))
    (hDS : ‖fderiv ℝ S x‖ ≤ CS * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + 1)) :
    ‖fderiv ℝ W x‖ ≤ (CV + CS) * δ ^ 2 * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hm : (0 : ℝ) ≤ RevisedScales.baselineOrder n := Nat.cast_nonneg _
  have hmeanExp : 2 * RevisedScales.forcingExponent n + RevisedScales.baselineOrder n ≤
      RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n := by
    unfold RevisedScales.displacementLoss
    norm_num [samplingSlack, carrierExponent]
    linarith
  have hp : (R ^ RevisedScales.forcingExponent n) ^ 2 =
      R ^ (2 * RevisedScales.forcingExponent n) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hRp.le]
    congr 1
    ring
  have hv : ‖b ^ 2 • fderiv ℝ V x‖ ≤ CV * δ ^ 2 * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg b)]
    calc
      _ ≤ b ^ 2 * (CV * R ^ (RevisedScales.baselineOrder n : ℝ)) :=
        mul_le_mul_of_nonneg_left hDV (sq_nonneg b)
      _ = CV * δ ^ 2 * R ^ (2 * RevisedScales.forcingExponent n +
          RevisedScales.baselineOrder n) := by
        rw [hb, mul_pow, hp, Real.rpow_add hRp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR hmeanExp) (by positivity)
  have hs : ‖fderiv ℝ S x‖ ≤ CS * δ ^ 2 * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n) := by
    apply hDS.trans_eq
    rw [← Real.rpow_mul hRp.le, mul_assoc (CS * δ ^ 2), ← Real.rpow_add hRp]
    congr 2
    unfold RevisedScales.displacementLoss
    ring
  rw [hW, fderiv_add (hV.const_smul _) hS, fderiv_const_smul hV]
  exact ((norm_add_le _ _).trans (add_le_add hv hs)).trans_eq (by ring)

/-- `main:eq:step-error` directly from the separate primary, mean, and pair
profiles. In contrast to the intermediate metric theorem, neither the combined
secondary derivative nor background derivative growth is assumed: both are
proved for the actual `W=b²V+S`. Doubling a common constant costs no exponent. -/
theorem cNorm_metric_error_le_of_separate_profiles
    {F P V S W U : Euclidean n → Euclidean N}
    {g e eR H Hself Qoff Emean : MetricField n} {D : Set (Euclidean n)}
    {b C CF CE δ R Q : ℝ} {m Qp Qm q k : ℕ}
    (hC : 0 ≤ C) (hCF : 0 ≤ CF) (hCE : 0 ≤ CE)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) (hQ : 0 ≤ Q)
    (hb : b = δ * R ^ RevisedScales.forcingExponent n)
    (hm : 2 * Q < (1 - coefficientExponent) * (m : ℝ))
    (hQp : Q + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (Qp : ℝ))
    (hQm : Q + 2 * RevisedScales.forcingExponent n < (Qm : ℝ))
    (hq : Q + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (q : ℝ))
    (hk : Q + RevisedScales.cubicLoss n < carrierExponent * cutoffSlack * (k : ℝ))
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (hP : ∀ x ∈ D, DifferentiableAt ℝ P x)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
    (hS : ∀ x ∈ D, DifferentiableAt ℝ S x)
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x)
    (he : Set.EqOn e (g - inducedMetric F) D) (hW : W = b ^ 2 • V + S)
    (hself : Set.EqOn Hself (b ^ 2 • H) D)
    (hoff : Set.EqOn Qoff (inducedMetric P - Hself) D)
    (hmean : Set.EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) D)
    (hsmoothingSmall : ∀ x ∈ D, ‖eR x - e x‖ ≤ C * δ ^ 2)
    (hsmoothingHigh : ∀ x ∈ D, ‖eR x - e x‖ ≤
      C * (R ^ coefficientExponent / R) ^ m)
    (hstrain : ∀ x ∈ D, ‖linearizedMetric F P x‖ ≤ C * δ *
      R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 -
        carrierExponent * (Qp : ℝ)))
    (hmeanBound : ∀ x ∈ D, ‖Emean x‖ ≤ C * R ^ (-(Qm : ℝ)))
    (hpair : ∀ x ∈ D, ‖linearizedMetric F S x + Qoff x‖ ≤ C * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack -
        (carrierExponent - separationExponent) * (q : ℝ)))
    (hDF : ∀ x ∈ D, ‖fderiv ℝ F x‖ ≤ CF)
    (hDP : ∀ x ∈ D, ‖fderiv ℝ P x‖ ≤ C * δ *
      R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1))
    (hDV : ∀ x ∈ D, ‖fderiv ℝ V x‖ ≤ C * R ^ (RevisedScales.baselineOrder n : ℝ))
    (hDS : ∀ x ∈ D, ‖fderiv ℝ S x‖ ≤ C * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + 1))
    (htail : ∀ x ∈ D, ‖fderiv ℝ (U - (P + W)) x‖ ≤
      CE * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) -
          cutoffSlack * (k : ℝ))) :
    cNorm D 0 (inducedMetric (F + U) - g) ≤
      metricErrorConstant n (2 * C) CF CE *
        (δ * R ^ (-Q) + δ ^ 3 * R ^ RevisedScales.cubicLoss n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hdouble : C ≤ 2 * C := by linarith
  apply cNorm_metric_error_le_of_components (by positivity) hCF hCE hδ hδ1 hR hQ
    hb hm hQp hQm hq hk hF hP hV hS hU he hW hself hoff hmean
  · intro x hx
    exact (hsmoothingSmall x hx).trans
      (mul_le_mul_of_nonneg_right hdouble (sq_nonneg δ))
  · intro x hx
    exact (hsmoothingHigh x hx).trans
      (mul_le_mul_of_nonneg_right hdouble (by positivity))
  · intro x hx
    exact (hstrain x hx).trans (by gcongr)
  · intro x hx
    exact (hmeanBound x hx).trans (mul_le_mul_of_nonneg_right hdouble (by positivity))
  · intro x hx
    exact (hpair x hx).trans (by gcongr)
  · exact hDF
  · intro x hx
    exact (fderiv_primary_le_of_profile hC hδ.le hR (hDP x hx)).trans (by gcongr)
  · intro x hx
    simpa only [two_mul] using fderiv_secondary_le_of_profiles hC hR hb
      (hV x hx) (hS x hx) hW (hDV x hx) (hDS x hx)
  · exact htail

end JanetCartan.RevisedStage
