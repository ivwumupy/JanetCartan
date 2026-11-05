module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.RescaledCutoffs.ScalarJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.RescaledCutoffs.Scaling

/-!
# Uniform primitive profiles of the rescaled transport coefficients

The consumer is the global high-cutoff and regularized symbol assembly in
`TransportSymbol`, implementing `app:ch_background:prop:bg-frame`, Step 1.
Only the scalar high coefficient changes under frequency dilation. Its uniform
profiles come from the fixed masks; the unchanged coefficients use their
original primitive profiles or buffered finite norms. No amplitude estimate is
an input, and no regularization-dependent low norm occurs.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Primitive smoothness survives rescaling of the high mask. Combined with
`PrimitiveRegularity.regularized`, this supplies the shell estimate's regularity
input for every regularization radius and dilation. Source:
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem PrimitiveRegularity.rescaled {a : Coefficients n N}
    {J : InputVariables n → ℝ} {W : Set (InputVariables n)}
    (ha : PrimitiveRegularity a J W) (t : ℝ) :
    PrimitiveRegularity (rescaledCoefficients a t) J W := by
  exact { ha with high := ha.high.comp (contDiff_const.mul contDiff_id) }

/-- Replacing the high coefficient uses its own primitive profile and the
unchanged profiles from the homogeneous coefficients. The latter impose no
bound on any high mask. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem CoefficientShellProfiles.replaceHigh
    {s : ℕ} {H A B : ℝ} {a : Coefficients n N} {p : InputVariables n}
    (ha : CoefficientShellProfiles s H A (homogeneousCoefficients a) p)
    {f : ℝ → ℝ} (hf : ShellJetProfile s H B f ‖p.2.2‖)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    CoefficientShellProfiles s H (A + B) {a with high := f} p := by
  exact {
    leftMeasurement := ha.leftMeasurement.mono (le_add_of_nonneg_right hB) hH
    rightMeasurement := ha.rightMeasurement.mono (le_add_of_nonneg_right hB) hH
    angular := ha.angular.mono (le_add_of_nonneg_right hB) hH
    high := hf.mono (le_add_of_nonneg_left hA) hH
    leftNormal := ha.leftNormal.mono (le_add_of_nonneg_right hB) hH
    rightNormal := ha.rightNormal.mono (le_add_of_nonneg_right hB) hH
    leftReduced := ha.leftReduced.mono (le_add_of_nonneg_right hB) hH
    rightReduced := ha.rightReduced.mono (le_add_of_nonneg_right hB) hH }

/-- Profiles of the unregularized rescaled coefficients, uniformly in the
frequency dilation and varying geometry. The fixed high mask is displayed
explicitly; its profiles are proved from that mask.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and bg-frame Step 1. -/
theorem exists_rescaled_coefficientShellProfiles
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (t H : ℝ), 1 ≤ t → 1 ≤ H → ∀ (a : Coefficients n N)
      (p : InputVariables n), ε ≤ ‖p.2.2‖ →
      CoefficientShellProfiles s H M (homogeneousCoefficients a) p →
      CoefficientShellProfiles s H C
        (rescaledCoefficients {a with high := h} t) p := by
  obtain ⟨C, hC, hb⟩ := exists_rescaledHigh_shellJetProfile hh htail hε s hs
  refine ⟨M + C, by linarith, ?_⟩
  intro t H ht hH a p hp ha
  exact ha.replaceHigh (hb t H ht hH _ hp) hM hC.le (zero_le_one.trans hH)

/-- Profiles of the actual rescaled regularized coefficients. The density
squares `h(t r) χ(t r/R)`, preserving the paper's carrier regularization.
The constant precedes `t`, `R`, `H`, and all varying coefficients.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_rescaled_regularized_coefficientShellProfiles
    {h χ : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (t R H : ℝ), 1 ≤ t → 1 ≤ R → 1 ≤ H →
      ∀ (a : Coefficients n N) (p : InputVariables n), ε ≤ ‖p.2.2‖ →
      CoefficientShellProfiles s H M (homogeneousCoefficients a) p →
      CoefficientShellProfiles s H C
        (rescaledCoefficients (regularizedCoefficients {a with high := h} χ R) t) p := by
  obtain ⟨C, hC, hb⟩ := exists_rescaledRegularizedHigh_shellJetProfile hh htail hχ hc hε s hs
  refine ⟨M + C, by linarith, ?_⟩
  intro t R H ht hR hH a p hp ha
  exact ha.replaceHigh (hb t R H ht hR hH _ hp) hM hC.le (zero_le_one.trans hH)

/-- Unchanged primitive finite norms supply the homogeneous coefficient
profiles. Only the four unchanged primitives are assumed; there is no finite
norm assumption for a rescaled mask. The high coordinate of `D` is unused.
Consumed by the uniform rescaled coefficient theorem below; source:
`app:ch_background:eq:bg-mixed-input`. -/
theorem exists_homogeneousCoefficient_profiles_of_unchanged_norms
    (D : CoefficientNormCharts n) {s : ℕ} (hs : 2 ≤ s)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ (a : Coefficients n N) (H : ℝ), 1 ≤ H →
      D.measurement.Controls s M B H a.measurement →
      D.angular.Controls s M B H a.angular →
      D.field.Controls s M B H a.normal → D.field.Controls s M B H a.reduced →
      ∀ p : InputVariables n,
      p.1.1 ∈ D.measurement.carrier → p.1.2 ∈ D.measurement.carrier →
      (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ∈ D.angular.carrier →
      (p.1.1, p.2.1) ∈ D.field.carrier → (p.1.2, p.2.1) ∈ D.field.carrier →
      CoefficientShellProfiles s H C (homogeneousCoefficients a) p := by
  obtain ⟨C₁, h₁, hb₁⟩ := D.measurement.exists_profiles (F := ℝ) hs hM hB
  obtain ⟨C₂, h₂, hb₂⟩ := D.angular.exists_profiles (F := ℝ) hs hM hB
  obtain ⟨C₃, h₃, hb₃⟩ := D.field.exists_profiles (F := Euclidean N) hs hM hB
  obtain ⟨C₄, h₄, hb₄⟩ := D.field.exists_profiles (F := Fin n → ℝ) hs hM hB
  let C := C₁ + C₂ + C₃ + C₄ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a H hH hm ha hn hq p hp₁ hp₂ hp₃ hp₄ hp₅
  have hH0 := zero_le_one.trans hH
  refine {
    leftMeasurement := (hb₁ a.measurement H hH hm _ hp₁).mono (by dsimp [C]; linarith) hH0
    rightMeasurement := (hb₁ a.measurement H hH hm _ hp₂).mono (by dsimp [C]; linarith) hH0
    angular := (hb₂ a.angular H hH ha _ hp₃).mono (by dsimp [C]; linarith) hH0
    high := ?_
    leftNormal := (hb₃ a.normal H hH hn _ hp₄).mono (by dsimp [C]; linarith) hH0
    rightNormal := (hb₃ a.normal H hH hn _ hp₅).mono (by dsimp [C]; linarith) hH0
    leftReduced := (hb₄ a.reduced H hH hq _ hp₄).mono (by dsimp [C]; linarith) hH0
    rightReduced := (hb₄ a.reduced H hH hq _ hp₅).mono (by dsimp [C]; linarith) hH0 }
  refine ⟨contDiffAt_const, ?_, ?_⟩
  · simpa [homogeneousCoefficients] using (show (1 : ℝ) ≤ C by dsimp [C]; linarith)
  · intro i hi _
    simp only [homogeneousCoefficients, iteratedFDeriv_const_of_ne (by omega : i ≠ 0),
      Pi.zero_apply, norm_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg hH0 _)

/-- Complete primitive profile interface for the regularized rescaled shell
estimate, with constants preceding dilation, regularization, high norm, and
varying coefficients. The inputs are only original finite norms and chart
range conditions, never composed-mask jets or amplitude estimates.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and bg-frame Step 1. -/
theorem exists_rescaled_regularized_profiles_of_primitiveNorms
    (D : CoefficientNormCharts n) {h χ : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {ε M B : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (t R H : ℝ), 1 ≤ t → 1 ≤ R → 1 ≤ H →
      ∀ a : Coefficients n N,
      D.measurement.Controls s M B H a.measurement →
      D.angular.Controls s M B H a.angular →
      D.field.Controls s M B H a.normal → D.field.Controls s M B H a.reduced →
      ∀ p : InputVariables n, ε ≤ ‖p.2.2‖ →
      p.1.1 ∈ D.measurement.carrier → p.1.2 ∈ D.measurement.carrier →
      (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ∈ D.angular.carrier →
      (p.1.1, p.2.1) ∈ D.field.carrier → (p.1.2, p.2.1) ∈ D.field.carrier →
      CoefficientShellProfiles s H C
        (rescaledCoefficients (regularizedCoefficients {a with high := h} χ R) t) p := by
  obtain ⟨A, hA, ha⟩ := exists_homogeneousCoefficient_profiles_of_unchanged_norms
    (N := N) D hs hM hB
  obtain ⟨C, hC, hb⟩ := exists_rescaled_regularized_coefficientShellProfiles
    (n := n) (N := N) hh htail hχ hc hε hA.le s hs
  refine ⟨C, hC, ?_⟩
  intro t R H ht hR hH a hm hang hn hq p hp hp₁ hp₂ hp₃ hp₄ hp₅
  exact hb t R H ht hR hH a p hp (ha a H hH hm hang hn hq p hp₁ hp₂ hp₃ hp₄ hp₅)

/-- Complete primitive profile interface for the unregularized rescaled shell
estimate. No rescaled low norm is an input.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and bg-frame Step 1. -/
theorem exists_rescaled_profiles_of_primitiveNorms
    (D : CoefficientNormCharts n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    {ε M B : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ C > 0, ∀ (t H : ℝ), 1 ≤ t → 1 ≤ H → ∀ a : Coefficients n N,
      D.measurement.Controls s M B H a.measurement →
      D.angular.Controls s M B H a.angular →
      D.field.Controls s M B H a.normal → D.field.Controls s M B H a.reduced →
      ∀ p : InputVariables n, ε ≤ ‖p.2.2‖ →
      p.1.1 ∈ D.measurement.carrier → p.1.2 ∈ D.measurement.carrier →
      (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ∈ D.angular.carrier →
      (p.1.1, p.2.1) ∈ D.field.carrier → (p.1.2, p.2.1) ∈ D.field.carrier →
      CoefficientShellProfiles s H C (rescaledCoefficients {a with high := h} t) p := by
  obtain ⟨A, hA, ha⟩ := exists_homogeneousCoefficient_profiles_of_unchanged_norms
    (N := N) D hs hM hB
  obtain ⟨C, hC, hb⟩ := exists_rescaled_coefficientShellProfiles
    (n := n) (N := N) hh htail hε hA.le s hs
  refine ⟨C, hC, ?_⟩
  intro t H ht hH a hm hang hn hq p hp hp₁ hp₂ hp₃ hp₄ hp₅
  exact hb t H ht hH a p hp (ha a H hH hm hang hn hq p hp₁ hp₂ hp₃ hp₄ hp₅)

end JanetCartan.ContinuumNormalReduction.TransportSymbol
