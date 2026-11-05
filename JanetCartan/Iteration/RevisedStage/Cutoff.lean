module

public import JanetCartan.Iteration.RevisedStage.Profiles
public import JanetCartan.Analysis.PhysicalCutoff.Contraction

/-!
# The same constructed physical increment in the revised step

For §15 Steps 6--7 of `paper-v2.tex`, choose the actual real Schwartz cutoff
of the primary plus secondary field. The real-even multiplier producer proves
its exact physical band and L² contraction. The metric theorem is specialized
to that very output, not to a separate field selected by an abstract existence
hypothesis. The derivative tail of the actual cutoff is still an explicit
analytic producer boundary, as are the original wave/response profiles.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RevisedStage

variable {n N : ℕ}

/-- §15 Step 6: the actual real global increment `Π(P+W)`, using the physical
Fourier variable and the fixed inner/outer symbol radii `1` and `2`. -/
def increment (R : ℝ) (P W : SchwartzMap (Euclidean n) (Euclidean N)) :
    SchwartzMap (Euclidean n) (Euclidean N) :=
  PhysicalCutoff.truncate (R ^ bandExponent) (P + W)

/-- `main:eq:step-band`: the SAME increment has exact physical Fourier support
with accuracy-independent constant `2` and exactly the manuscript's `b_*`. -/
theorem hasFourierSupport_increment {R : ℝ} (hR : 0 < R)
    (P W : SchwartzMap (Euclidean n) (Euclidean N)) :
    PhysicalBernstein.HasFourierSupport (2 * R ^ bandExponent) (increment R P W) :=
  PhysicalCutoff.hasFourierSupport_truncate (Real.rpow_pos_of_pos hR _) (P + W)

/-- `main:eq:step-L2`: contraction of the actual cutoff and the two lower
physical L² bounds preserve the exact revised `B₀`; `δ²` is absorbed into `δ`. -/
theorem physicalL2Norm_increment_le
    {P W : SchwartzMap (Euclidean n) (Euclidean N)} {C δ R : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hP : PhysicalBernstein.physicalL2Norm P ≤
      C * δ * R ^ RevisedScales.displacementLoss n)
    (hW : PhysicalBernstein.physicalL2Norm W ≤
      C * δ ^ 2 * R ^ RevisedScales.displacementLoss n) :
    PhysicalBernstein.physicalL2Norm (increment R P W) ≤
      2 * C * δ * R ^ RevisedScales.displacementLoss n := by
  calc
    _ ≤ PhysicalBernstein.physicalL2Norm P + PhysicalBernstein.physicalL2Norm W :=
      PhysicalCutoff.physicalL2Norm_truncate_add_le (R ^ bandExponent) P W
    _ ≤ C * δ * R ^ RevisedScales.displacementLoss n +
        C * δ ^ 2 * R ^ RevisedScales.displacementLoss n := add_le_add hP hW
    _ ≤ C * δ * R ^ RevisedScales.displacementLoss n +
        C * δ * R ^ RevisedScales.displacementLoss n := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (quadratic_amplitude_le hδ hδ1) hC)
        (Real.rpow_nonneg hR _)
    _ = _ := by ring

/-- `main:thm:step`, SAME-output assembly: choose the actual cutoff increment
and prove its band, physical L² bound, and revised metric estimate. Only lower
analytic producers remain inputs: the four errors, separate primary/mean/pair
profiles, and the derivative tail for THIS constructed cutoff. In particular,
no output field, final metric bound, output band, or output L² bound is assumed. -/
theorem increment_estimates_of_components
    {F : Euclidean n → Euclidean N}
    {P V S W : SchwartzMap (Euclidean n) (Euclidean N)}
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
    (hPL2 : PhysicalBernstein.physicalL2Norm P ≤ C * δ * R ^ RevisedScales.displacementLoss n)
    (hWL2 : PhysicalBernstein.physicalL2Norm W ≤ C * δ ^ 2 * R ^ RevisedScales.displacementLoss n)
    (htail : ∀ x ∈ D, ‖fderiv ℝ (⇑(increment R P W) - (⇑P + ⇑W)) x‖ ≤
      CE * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) -
          cutoffSlack * (k : ℝ))) :
    PhysicalBernstein.HasFourierSupport (2 * R ^ bandExponent) (increment R P W) ∧
      PhysicalBernstein.physicalL2Norm (increment R P W) ≤
        2 * C * δ * R ^ RevisedScales.displacementLoss n ∧
      cNorm D 0 (inducedMetric (F + ⇑(increment R P W)) - g) ≤
        metricErrorConstant n (2 * C) CF CE *
          (δ * R ^ (-Q) + δ ^ 3 * R ^ RevisedScales.cubicLoss n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  refine ⟨hasFourierSupport_increment hRp P W,
    physicalL2Norm_increment_le hC hδ.le hδ1 hRp.le hPL2 hWL2, ?_⟩
  apply cNorm_metric_error_le_of_separate_profiles hC hCF hCE hδ hδ1 hR hQ
    hb hm hQp hQm hq hk hF
    (fun _ _ ↦ P.differentiableAt) (fun _ _ ↦ V.differentiableAt)
    (fun _ _ ↦ S.differentiableAt) (fun _ _ ↦ (increment R P W).differentiableAt)
    he _ hself hoff hmean hsmoothingSmall hsmoothingHigh hstrain hmeanBound hpair
    hDF hDP hDV hDS htail
  rw [hW]
  rfl

end JanetCartan.RevisedStage
