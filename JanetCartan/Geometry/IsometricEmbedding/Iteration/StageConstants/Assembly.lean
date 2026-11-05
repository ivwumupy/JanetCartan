module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.StageConstants.Selection

/-!
# Assembly from the finite physical profiles

This is the conditional application of `main:thm:step` used to select Section 9's
uniform constants. The analytic fields and component estimates remain inputs.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.StageConstants

/-- The common metric/L² constant from `main:thm:step`, after deriving the
background derivative bound. It depends only on the supplied numerical data. -/
def correctionConstant (n t : ℕ) (c : ComponentBounds) : ℝ :=
  FiniteStage.stageConstant n (componentConstant n t c)
    (max 0 c.reference + 2 * componentConstant n t c)

/-- Nonnegativity of the selected Section 9 metric/L² constant. -/
theorem correctionConstant_nonneg (n t : ℕ) (c : ComponentBounds) :
    0 ≤ correctionConstant n t c := by
  have := componentConstant_nonneg n t c
  unfold correctionConstant FiniteStage.stageConstant FiniteStage.errorConstant
  positivity

/-- `main:thm:step` at `Q=2k` from separate constants and thresholds for the
actual fields. Component derivatives, the derivative of `F+P+W`, and the tail of
the actual fixed cutoff are all proved here from the physical profiles.
The only Sobolev orders consumed are `0,m,t,m+t`, with `m=n+2`. -/
theorem correction_of_profiles {n N : ℕ} (c τ : ComponentBounds)
    (Lref : ℝ) (k q t : ℕ)
    (hq : forcingExponent n + (1 + samplingSlack) / 2 + max (2 * (k : ℝ)) 0 ≤
      carrierExponent * q)
    (ht : displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2) +
      (max (2 * (k : ℝ)) 0 + backgroundExponent n Lref) ≤
      (carrierExponent * cutoffSlack) * t)
    (a : Fields n N) (ha : Identities a)
    (he : ComponentEstimates c τ Lref k q t a)
    (hT : stageThreshold n t τ ≤ a.R) :
    ∃ U : Torus n → Euclidean N,
      U = FiniteStage.increment a.R a.P a.W ∧ IsSmoothPeriodic U ∧
      cNorm a.D 0 (inducedMetric (a.F + periodicLift U) - a.g) ≤
        correctionConstant n t c *
          (a.δ * a.R ^ (-2 * (k : ℝ)) + a.δ ^ 3 * a.R ^ cubicLoss n) ∧
      periodicL2Norm U ≤ correctionConstant n t c * a.δ * a.R ^ displacementLoss n ∧
      HasFourierSupport (2 * a.R ^ bandExponent) U ∧
      ∀ r : ℕ, cNorm (fundamentalCell n) r (periodicLift U) ≤
        FiniteStage.crConstant n r (componentConstant n t c) * a.δ *
          a.R ^ (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) := by
  let C := componentConstant n t c
  have hC : 0 ≤ C := componentConstant_nonneg n t c
  have hR : 1 ≤ a.R := (one_le_stageThreshold n t τ).trans hT
  have hR0 : 0 < a.R := lt_of_lt_of_le zero_lt_one hR
  have hδ : 0 ≤ a.δ := ha.amplitude_pos.le
  have hconst (x : ℝ) (hx : x ∈ usedConstants n t c) : x ≤ C := le_componentConstant hx
  have hthreshold (x : ℝ) (hx : x ∈ usedThresholds n t τ) : x ≤ a.R :=
    (le_stageThreshold hx).trans hT
  have hprofileP (r : ℕ) (hr : r ∈ profileOrders n t) :
      periodicSobolevNorm r a.P ≤ profileConstant c r * a.δ *
        a.R ^ displacementLoss n * (a.R ^ carrierExponent) ^ (r : ℝ) := by
    apply (he.primarySobolev r hr (hthreshold _ ?_)).trans
    · gcongr
      exact (le_max_left _ _).trans (le_max_right _ _)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
  have hprofileW (r : ℕ) (hr : r ∈ profileOrders n t) :
      periodicSobolevNorm r a.W ≤ profileConstant c r * a.δ ^ 2 *
        a.R ^ displacementLoss n * (a.R ^ carrierExponent) ^ (r : ℝ) := by
    apply (he.secondarySobolev r hr (hthreshold _ ?_)).trans
    · gcongr
      exact (le_max_right _ _).trans (le_max_right _ _)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hPzero : periodicSobolevNorm 0 a.P ≤
      profileConstant c 0 * a.δ * a.R ^ displacementLoss n := by
    simpa using hprofileP 0 (by simp [profileOrders])
  have hWzero : periodicSobolevNorm 0 a.W ≤
      profileConstant c 0 * a.δ ^ 2 * a.R ^ displacementLoss n := by
    simpa using hprofileW 0 (by simp [profileOrders])
  obtain ⟨hDP₀, hDW₀⟩ := FiniteStage.component_derivative_bounds_of_profiles
    ha.smooth_P ha.smooth_W (interpolationOrder_gt n) hR hPzero
    (hprofileP (interpolationOrder n) (by simp [profileOrders])) hWzero
    (hprofileW (interpolationOrder n) (by simp [profileOrders]))
  have hdC : derivativeConstant n c ≤ C := hconst _ (by simp [usedConstants])
  have hDP : ∀ x ∈ a.D, ‖fderiv ℝ (periodicLift a.P) x‖ ≤ C * a.δ *
      a.R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) := by
    intro x _
    apply (hDP₀ x).trans
    change derivativeConstant n c * _ * _ ≤ _
    gcongr
  have hDW : ∀ x ∈ a.D, ‖fderiv ℝ (periodicLift a.W) x‖ ≤ C * a.δ ^ 2 *
      a.R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) := by
    intro x _
    apply (hDW₀ x).trans
    change derivativeConstant n c * _ * _ ≤ _
    gcongr
  have htail₀ := FiniteStage.increment_derivative_tail_le_profiles ha.smooth_P ha.smooth_W
    (interpolationOrder_gt n) hR (le_max_left 0 _) (le_max_left 0 _) hδ ha.amplitude_le_one
    (hprofileP t (by simp [profileOrders]))
    (hprofileP (interpolationOrder n + t) (by simp [profileOrders]))
    (hprofileW t (by simp [profileOrders]))
    (hprofileW (interpolationOrder n + t) (by simp [profileOrders]))
  have htC : tailConstant n t c ≤ C := hconst _ (by simp [usedConstants])
  have htail : ∀ x ∈ a.D,
      ‖fderiv ℝ (periodicLift (FiniteStage.increment a.R a.P a.W) -
        (periodicLift a.P + periodicLift a.W)) x‖ ≤
      (C * a.δ) * (a.R ^ displacementLoss n * (a.R ^ carrierExponent) ^
        (meanDerivativeLoss n + 1 / 2 - cutoffSlack * t)) := by
    intro x _
    apply (htail₀ x).trans
    change (tailConstant n t c * _) * _ ≤ _
    gcongr
  have hreference : ∀ x ∈ a.D, ‖fderiv ℝ a.F x‖ ≤ max 0 c.reference * a.R ^ Lref := by
    intro x hx
    apply (he.reference (hthreshold _ (by simp [usedThresholds])) x hx).trans
    gcongr
    exact le_max_right _ _
  have hbackground := background_derivative_le ha hC (le_max_left 0 c.reference)
    hR hreference hDP hDW
  have hQ : max (2 * (k : ℝ)) 0 = 2 * (k : ℝ) := max_eq_left (by positivity)
  have hsmoothing : ∀ x ∈ a.D, ‖a.eR x - a.e x‖ ≤ C * a.δ * a.R ^ (-max (2 * (k : ℝ)) 0) := by
    intro x hx
    rw [hQ, ← neg_mul]
    apply (he.smoothing (hthreshold _ (by simp [usedThresholds])) x hx).trans
    gcongr
    exact hconst _ (by simp [usedConstants])
  have hstrain : ∀ x ∈ a.D, ‖linearizedMetric a.F (periodicLift a.P) x‖ ≤
      (C * a.δ) * (a.R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
        (a.R ^ carrierExponent) ^ (-(q : ℝ))) := by
    intro x hx
    apply (he.strain (hthreshold _ (by simp [usedThresholds])) x hx).trans
    gcongr
    exact hconst _ (by simp [usedConstants])
  have hmean : ∀ x ∈ a.D, ‖a.b ^ 2 • a.Emean x‖ ≤ C * a.δ * a.R ^ (-max (2 * (k : ℝ)) 0) := by
    intro x hx
    rw [hQ, ← neg_mul]
    apply (he.mean (hthreshold _ (by simp [usedThresholds])) x hx).trans
    gcongr
    exact hconst _ (by simp [usedConstants])
  have hpair : ∀ x ∈ a.D, ‖linearizedMetric a.F a.S x + a.Qoff x‖ ≤
      C * a.δ * a.R ^ (-max (2 * (k : ℝ)) 0) := by
    intro x hx
    rw [hQ, ← neg_mul]
    apply (he.pair (hthreshold _ (by simp [usedThresholds])) x hx).trans
    gcongr
    exact hconst _ (by simp [usedConstants])
  have hPL2 : periodicL2Norm a.P ≤ C * a.δ * a.R ^ displacementLoss n := by
    apply (he.primaryL2 (hthreshold _ (by simp [usedThresholds]))).trans
    gcongr
    exact hconst _ (by simp [usedConstants])
  have hWL2 : periodicL2Norm a.W ≤ C * a.δ ^ 2 * a.R ^ displacementLoss n := by
    apply (he.secondaryL2 (hthreshold _ (by simp [usedThresholds]))).trans
    gcongr
    exact hconst _ (by simp [usedConstants])
  obtain ⟨U, hU, hs, _, hm, hl, hb, hr⟩ :=
    FiniteStage.correction_of_component_estimates hC
      (show 0 ≤ max 0 c.reference + 2 * C by positivity)
      ha.amplitude_pos ha.amplitude_le_one hR (le_max_left 0 _) ha.b_ne_zero hq ht
      ha.differentiable_F ha.smooth_P ha.smooth_W ha.differentiable_V ha.differentiable_S
      ha.defect ha.secondary ha.self ha.off ha.mean hsmoothing hstrain hmean hpair
      hPL2 hWL2 hDP hDW hbackground htail
  exact ⟨U, hU, hs, by simpa only [correctionConstant, C, neg_mul] using hm, hl, hb, hr⟩

end JanetCartan.StageConstants
