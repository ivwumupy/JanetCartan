module

public import JanetCartan.Iteration.RevisedStage.Accuracy
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricLedger
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricRemainder

/-!
# The revised physical metric ledger and its cutoff perturbation

This is the analytic assembly in §15 of `paper-v2.tex`, from the four LOWER
component errors and the actual differentials of the SAME real global fields.
The exact ledger is reused; the cubic estimate uses the existing tensor bound,
not its legacy-exponent corollary. The final cutoff has its genuine difference
`U - (P + W)`, and its quadratic metric contribution is retained.

The uncut and cutoff estimates are proved here. Actual primary waves, mean and
pair responses, the physical Sobolev-to-C¹ estimate, and the cutoff derivative
tail remain explicit producer boundaries. In particular, these results do not
assert the unconditional existence part of `main:thm:step`, or identify a global
physical field with a periodic one.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RevisedStage

variable {n N : ℕ}

/-- §15 Step 5: the last two actual tensors of the ledger have exactly the
revised cubic loss, from one `δ` derivative factor and one `δ²` factor. -/
theorem norm_metricRemainder_le_revised_cubic
    {P W : Euclidean n → Euclidean N} {x : Euclidean n} {C δ R : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hDP : ‖fderiv ℝ P x‖ ≤ C * δ * R ^ (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n))
    (hDW : ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^ (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n)) :
    ‖metricRemainder P W x‖ ≤
      3 * n * C ^ 2 * δ ^ 3 * R ^ RevisedScales.cubicLoss n := by
  rw [cubicLoss_eq_twice_derivative_loss]
  exact norm_metricRemainder_le_rpow hC hδ hδ1 (zero_lt_one.trans_le hR).le hDP hDW

/-- `new:eq:uncut-error`: the exact ledger plus the four separate errors and
the primary/secondary derivative profiles. No final metric bound is an input. -/
theorem norm_uncut_metric_error_le
    {F P V S W : Euclidean n → Euclidean N}
    {g e eR H Hself Qoff Emean : MetricField n} {x : Euclidean n}
    {b C δ R Q : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) (hb : b ≠ 0)
    (hF : DifferentiableAt ℝ F x) (hP : DifferentiableAt ℝ P x)
    (hV : DifferentiableAt ℝ V x) (hS : DifferentiableAt ℝ S x)
    (he : e x = g x - inducedMetric F x) (hW : W = b ^ 2 • V + S)
    (hself : Hself x = b ^ 2 • H x)
    (hoff : Qoff x = inducedMetric P x - Hself x)
    (hmean : Emean x = linearizedMetric F V x + H x - (b ^ 2)⁻¹ • eR x)
    (hsmoothing : ‖eR x - e x‖ ≤ C * δ * R ^ (-Q))
    (hstrain : ‖linearizedMetric F P x‖ ≤ C * δ * R ^ (-Q))
    (hmeanBound : ‖b ^ 2 • Emean x‖ ≤ C * δ * R ^ (-Q))
    (hpair : ‖linearizedMetric F S x + Qoff x‖ ≤ C * δ * R ^ (-Q))
    (hDP : ‖fderiv ℝ P x‖ ≤ C * δ * R ^ (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n))
    (hDW : ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^ (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n)) :
    ‖inducedMetric (F + P + W) x - g x‖ ≤
      4 * C * δ * R ^ (-Q) +
        3 * n * C ^ 2 * δ ^ 3 * R ^ RevisedScales.cubicLoss n := by
  have hcubic := norm_metricRemainder_le_revised_cubic hC hδ hδ1 hR hDP hDW
  have hledger := inducedMetric_metricLedger hF hP hV hS hb he hW hself hoff hmean
  have hgroup : inducedMetric (F + P + W) x - g x =
      ((((eR x - e x) + linearizedMetric F P x) + b ^ 2 • Emean x) +
        (linearizedMetric F S x + Qoff x)) + metricRemainder P W x := by
    rw [hledger]
    simp only [metricRemainder, Pi.add_apply]
    abel
  rw [hgroup]
  have h01 := (norm_add_le (eR x - e x) (linearizedMetric F P x)).trans
    (add_le_add hsmoothing hstrain)
  have h012 := (norm_add_le _ (b ^ 2 • Emean x)).trans (add_le_add h01 hmeanBound)
  have h0123 := (norm_add_le _ (linearizedMetric F S x + Qoff x)).trans
    (add_le_add h012 hpair)
  exact ((norm_add_le _ _).trans (add_le_add h0123 hcubic)).trans_eq (by ring)

/-- `new:eq:uncut-error`, uniformly on the physical measurement domain, with
all four finite accuracies absorbed from their RAW lower component estimates.
The unnormalized mean bound is multiplied by the SAME `b²`, not supplied as a
new hypothesis. Smoothing uses both independent tails of the SAME tensor. -/
theorem cNorm_uncut_metric_error_le_of_components
    {F P V S W : Euclidean n → Euclidean N}
    {g e eR H Hself Qoff Emean : MetricField n} {D : Set (Euclidean n)}
    {b C δ R Q : ℝ} {m Qp Qm q : ℕ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hb : b = δ * R ^ RevisedScales.forcingExponent n)
    (hm : 2 * Q < (1 - coefficientExponent) * (m : ℝ))
    (hQp : Q + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (Qp : ℝ))
    (hQm : Q + 2 * RevisedScales.forcingExponent n < (Qm : ℝ))
    (hq : Q + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (q : ℝ))
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (hP : ∀ x ∈ D, DifferentiableAt ℝ P x)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
    (hS : ∀ x ∈ D, DifferentiableAt ℝ S x)
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
    (hDP : ∀ x ∈ D, ‖fderiv ℝ P x‖ ≤ C * δ * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n))
    (hDW : ∀ x ∈ D, ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n)) :
    cNorm D 0 (inducedMetric (F + P + W) - g) ≤
      4 * C * δ * R ^ (-Q) +
        3 * n * C ^ 2 * δ ^ 3 * R ^ RevisedScales.cubicLoss n := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hb0 : b ≠ 0 := by rw [hb]; exact (mul_pos hδ (Real.rpow_pos_of_pos hRp _)).ne'
  apply cNorm_zero_le_of_norm_bound (by positivity)
  intro x hx
  apply norm_uncut_metric_error_le hC hδ hδ1 hR hb0
    (hF x hx) (hP x hx) (hV x hx) (hS x hx) (he hx) hW (hself hx) (hoff hx) (hmean hx)
  · exact smoothing_error_le_of_accuracy (norm_nonneg _) hC hδ.le hR hm
      (hsmoothingSmall x hx) (hsmoothingHigh x hx)
  · exact primary_error_le_of_accuracy hC hδ.le hR hQp (hstrain x hx)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg b), hb]
    exact mean_error_le_of_accuracy hC hδ.le hδ1 hR hQm (hmeanBound x hx)
  · exact pair_error_le_of_accuracy hC hδ.le hδ1 hR hq (hpair x hx)
  · exact hDP x hx
  · exact hDW x hx

/-- §15 Step 6: the SAME background `G = F+P+W` inherits its derivative
bound from the original immersion and the primary/secondary profiles. This
closes the background-growth premise rather than moving it into a record. -/
theorem fderiv_background_le_of_components
    {F P W : Euclidean n → Euclidean N} {x : Euclidean n} {C CF δ R : ℝ}
    (hC : 0 ≤ C) (hCF : 0 ≤ CF) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hF : DifferentiableAt ℝ F x) (hP : DifferentiableAt ℝ P x)
    (hW : DifferentiableAt ℝ W x) (hDF : ‖fderiv ℝ F x‖ ≤ CF)
    (hDP : ‖fderiv ℝ P x‖ ≤ C * δ * R ^ (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n))
    (hDW : ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^ (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n)) :
    ‖fderiv ℝ (F + P + W) x‖ ≤ (CF + 2 * C) * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n) := by
  let L := R ^ (RevisedScales.displacementLoss n +
    carrierExponent * RevisedScales.baselineOrder n)
  have hL : 1 ≤ L := Real.one_le_rpow hR (derivative_loss_nonneg n)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hF' : ‖fderiv ℝ F x‖ ≤ CF * L :=
    hDF.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hCF)
  have hP' : ‖fderiv ℝ P x‖ ≤ C * L := hDP.trans (by
    calc C * δ * L ≤ C * 1 * L := by gcongr
         _ = C * L := by ring)
  have hW' : ‖fderiv ℝ W x‖ ≤ C * L := hDW.trans (by
    calc C * δ ^ 2 * L ≤ C * 1 * L := by
           exact mul_le_mul_of_nonneg_right
             (mul_le_mul_of_nonneg_left ((quadratic_amplitude_le hδ hδ1).trans hδ1) hC) hL0
         _ = C * L := by ring)
  rw [fderiv_add (hF.add hP) hW, fderiv_add hF hP]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hF' hP')) hW')).trans_eq (by dsimp [L]; ring)

/-- §15 Step 6: the actual cutoff perturbation, including its quadratic
term, has the required metric accuracy at exactly `aζk > Q+B₃`. The derivative
tail is for the SAME `U-(P+W)` and the background bound is proved above. -/
theorem cNorm_cutoff_metric_error_le_of_components
    {F P W U : Euclidean n → Euclidean N} {D : Set (Euclidean n)}
    {C CF CE δ R Q : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hCF : 0 ≤ CF) (hCE : 0 ≤ CE)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) (hQ : 0 ≤ Q)
    (hk : Q + RevisedScales.cubicLoss n < carrierExponent * cutoffSlack * (k : ℝ))
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (hP : ∀ x ∈ D, DifferentiableAt ℝ P x)
    (hW : ∀ x ∈ D, DifferentiableAt ℝ W x)
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x)
    (hDF : ∀ x ∈ D, ‖fderiv ℝ F x‖ ≤ CF)
    (hDP : ∀ x ∈ D, ‖fderiv ℝ P x‖ ≤ C * δ * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n))
    (hDW : ∀ x ∈ D, ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n))
    (htail : ∀ x ∈ D, ‖fderiv ℝ (U - (P + W)) x‖ ≤
      CE * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) -
          cutoffSlack * (k : ℝ))) :
    cNorm D 0 (inducedMetric (F + U) - inducedMetric (F + P + W)) ≤
      n * (2 * (CF + 2 * C) * CE + CE ^ 2) * δ * R ^ (-Q) := by
  have hG : ∀ x ∈ D, DifferentiableAt ℝ (F + P + W) x :=
    fun x hx ↦ ((hF x hx).add (hP x hx)).add (hW x hx)
  have hE : ∀ x ∈ D, DifferentiableAt ℝ (U - (P + W)) x :=
    fun x hx ↦ (hU x hx).sub ((hP x hx).add (hW x hx))
  have heq : F + U = (F + P + W) + (U - (P + W)) := by abel
  rw [heq]
  apply cNorm_metric_cutoff_le hG hE (by positivity) hCE hδ hδ1 hR
    (derivative_loss_nonneg n) hQ
  · intro x hx
    exact fderiv_background_le_of_components hC hCF hδ.le hδ1 hR
      (hF x hx) (hP x hx) (hW x hx) (hDF x hx) (hDP x hx) (hDW x hx)
  · intro x hx
    exact cutoff_derivative_le_of_accuracy hCE hδ.le hR hk (htail x hx)

/-- A single explicit constant for `main:eq:step-error`; it depends on the
component constants, never on an additional frequency exponent. -/
def metricErrorConstant (n : ℕ) (C CF CE : ℝ) : ℝ :=
  4 * C + 3 * n * C ^ 2 + n * (2 * (CF + 2 * C) * CE + CE ^ 2)

/-- `main:eq:step-error` for the SAME real physical fields, from the five
finite accuracies and raw component estimates. This combines the exact uncut
ledger and the actual cutoff perturbation; no final error is hypothesized.
The construction of the fields and their lower analytic estimates is separate. -/
theorem cNorm_metric_error_le_of_components
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
    (hDP : ∀ x ∈ D, ‖fderiv ℝ P x‖ ≤ C * δ * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n))
    (hDW : ∀ x ∈ D, ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^
      (RevisedScales.displacementLoss n + carrierExponent * RevisedScales.baselineOrder n))
    (htail : ∀ x ∈ D, ‖fderiv ℝ (U - (P + W)) x‖ ≤
      CE * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) -
          cutoffSlack * (k : ℝ))) :
    cNorm D 0 (inducedMetric (F + U) - g) ≤
      metricErrorConstant n C CF CE *
        (δ * R ^ (-Q) + δ ^ 3 * R ^ RevisedScales.cubicLoss n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hb0 : b ≠ 0 := by rw [hb]; exact (mul_pos hδ (Real.rpow_pos_of_pos hRp _)).ne'
  have hWdiff : ∀ x ∈ D, DifferentiableAt ℝ W x := by
    intro x hx
    rw [hW]
    exact ((hV x hx).const_smul _).add (hS x hx)
  apply cNorm_zero_le_of_norm_bound (by unfold metricErrorConstant; positivity)
  intro x hx
  have hmeanBound' : ‖b ^ 2 • Emean x‖ ≤ C * δ * R ^ (-Q) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg b), hb]
    exact mean_error_le_of_accuracy hC hδ.le hδ1 hR hQm (hmeanBound x hx)
  have huncut := norm_uncut_metric_error_le hC hδ hδ1 hR hb0
    (hF x hx) (hP x hx) (hV x hx) (hS x hx) (he hx) hW (hself hx) (hoff hx) (hmean hx)
    (smoothing_error_le_of_accuracy (norm_nonneg _) hC hδ.le hR hm
      (hsmoothingSmall x hx) (hsmoothingHigh x hx))
    (primary_error_le_of_accuracy hC hδ.le hR hQp (hstrain x hx)) hmeanBound'
    (pair_error_le_of_accuracy hC hδ.le hδ1 hR hq (hpair x hx)) (hDP x hx) (hDW x hx)
  have hcut := cNorm_cutoff_metric_error_le_of_components (D := {x})
    hC hCF hCE hδ hδ1 hR hQ hk
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hF x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hP x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hWdiff x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hU x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hDF x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hDP x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hDW x hx)
    (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using htail x hx)
  simp only [cNorm_order_zero, Set.image_singleton, csSup_singleton, Pi.sub_apply] at hcut
  change ‖inducedMetric (F + U) x - g x‖ ≤ _
  have heq : inducedMetric (F + U) x - g x =
      (inducedMetric (F + P + W) x - g x) +
        (inducedMetric (F + U) x - inducedMetric (F + P + W) x) := by abel
  rw [heq]
  apply ((norm_add_le _ _).trans (add_le_add huncut hcut)).trans
  unfold metricErrorConstant
  have ha : 0 ≤ δ * R ^ (-Q) := by positivity
  have hb' : 0 ≤ δ ^ 3 * R ^ RevisedScales.cubicLoss n := by positivity
  nlinarith [mul_nonneg (show 0 ≤ 4 * C + n * (2 * (CF + 2 * C) * CE + CE ^ 2)
      by positivity) hb',
    mul_nonneg (show 0 ≤ 3 * n * C ^ 2 by positivity) ha]

end JanetCartan.RevisedStage
