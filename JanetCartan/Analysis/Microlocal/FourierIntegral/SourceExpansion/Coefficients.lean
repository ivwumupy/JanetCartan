module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxScaling
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Summability
public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction.Character

/-!
# Fourier expansion in the Euclidean source variable

The source expansion in `app:ch_regular_base:thm:actual-calculus`, Step 1.
Only the amplitude is periodized: the source data still live on Euclidean space
with Lebesgue measure. A single cutoff supported inside the larger cell removes
all periodic copies. The coefficients have physical modes `2π k / ℓ`.

The estimates here concern source derivatives of a scalar slice, uniformly in
any frozen output and covector parameters. Commutation with joint output/covector
derivatives and identification of the full graph operator are separate obligations.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.FourierIntegral.SourceExpansion

open AmplitudeBound

variable {n : ℕ}

/-- Actual source coefficient on the fixed larger box of side `ℓ`
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def scalarCoefficient (ℓ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : Fin n → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ f) k

/-- A zero source fiber has zero coefficients; this retains the original
output/covector supports in Step 1 of `app:ch_regular_base:thm:actual-calculus`. -/
@[simp] theorem scalarCoefficient_zero (ℓ : ℝ) (k : Fin n → ℤ) :
    scalarCoefficient ℓ (fun _ ↦ 0) k = 0 := by
  simp [scalarCoefficient, boxAmplitudePeriodization, amplitudePeriodization,
    UnitAddTorus.mFourierCoeff]

/-- Source-independent cutoffs pass through the actual coefficients exactly.
In particular this applies to the original frequency regularization, in Step 1
of `app:ch_regular_base:thm:actual-calculus`. -/
theorem scalarCoefficient_const_mul (ℓ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (c : ℂ) (k : Fin n → ℤ) :
    scalarCoefficient ℓ (fun y ↦ c * f y) k = c * scalarCoefficient ℓ f k := by
  simp only [scalarCoefficient, UnitAddTorus.mFourierCoeff, boxAmplitudePeriodization,
    amplitudePeriodization, Function.comp_apply, smul_eq_mul, mul_left_comm _ c]
  exact MeasureTheory.integral_const_mul _ _

/-- Physical source character at scale `ℓ` in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. -/
def sourceMode (ℓ : ℝ) (k : Fin n → ℤ) (y : EuclideanSpace ℝ (Fin n)) : ℂ :=
  UnitAddTorus.mFourier k (scaledTorusChart ℓ y)

/-- The source modes use physical frequency `2π k / ℓ`, with no rescaling of
the graph covector (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceMode_eq_exp (ℓ : ℝ) (k : Fin n → ℤ) (y : EuclideanSpace ℝ (Fin n)) :
    sourceMode ℓ k y =
      Complex.exp (((ℓ⁻¹ * periodicFourierPhase k y : ℝ) : ℂ) * Complex.I) := by
  rw [sourceMode, scaledTorusChart, mFourier_torusQuotient_eq_exp]
  simp only [map_smul, smul_eq_mul]

/-- The decay weight for the fixed source series in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. This uses `1 + |2π k|`, an equivalent
Japanese bracket, and keeps the fixed box scale in the constant. -/
def decayWeight (N : ℕ) (k : Fin n → ℤ) : ℝ :=
  ((1 + frequencyNorm k) ^ N)⁻¹

/-- Explicit source integration-by-parts constant, including every dilation
factor (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def coefficientConstant (n N : ℕ) (ℓ : ℝ) : ℝ :=
  2 ^ (N - 1) * (1 + (n : ℝ) ^ N * |ℓ| ^ N)

/-- Positivity of the fixed source constant in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem coefficientConstant_pos (n N : ℕ) (ℓ : ℝ) :
    0 < coefficientConstant n N ℓ := by
  unfold coefficientConstant
  positivity

/-- Source coefficient decay from the actual physical derivatives, at every
order `N`, in `app:ch_regular_base:thm:actual-calculus`, Step 1. In applications
`f` is the full amplitude slice, including all original source cutoffs. -/
theorem norm_scalarCoefficient_le (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : SupportedInCenteredBox R f) (hf : ContDiff ℝ ∞ f)
    (N : ℕ) {A : ℝ} (hzero : ∀ y, ‖f y‖ ≤ A)
    (hderiv : ∀ i y, ‖euclideanCoordinateDerivList (List.replicate N i) f y‖ ≤ A)
    (k : Fin n → ℤ) :
    ‖scalarCoefficient ℓ f k‖ ≤ coefficientConstant n N ℓ * A * decayWeight N k := by
  have hz : ‖scalarCoefficient ℓ f k‖ ≤ A :=
    norm_mFourierCoeff_le _ k (norm_boxAmplitudePeriodization_le hzero ℓ)
  have hd : frequencyNorm k ^ N * ‖scalarCoefficient ℓ f k‖ ≤
      (n : ℝ) ^ N * (|ℓ| ^ N * A) := by
    apply frequencyNorm_pow_mul_norm_complex_mFourierCoeff_le
      (isSmoothPeriodic_boxAmplitudePeriodization hℓ hR hs hf) hn
    intro i z
    simpa only [List.length_replicate] using
      norm_coordinateDerivList_boxAmplitudePeriodization_le hℓ hR hs hf
        (List.replicate N i) (hderiv i) z
  have hp : 0 < (1 + frequencyNorm k) ^ N := by
    apply pow_pos
    linarith [frequencyNorm_nonneg k]
  rw [decayWeight, ← div_eq_mul_inv, le_div_iff₀ hp]
  calc
    _ = (1 + frequencyNorm k) ^ N * ‖scalarCoefficient ℓ f k‖ := mul_comm _ _
    _ ≤ (2 ^ (N - 1) * (1 + frequencyNorm k ^ N)) *
        ‖scalarCoefficient ℓ f k‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
        (frequencyNorm_nonneg k) N
    _ = 2 ^ (N - 1) * (‖scalarCoefficient ℓ f k‖ +
        frequencyNorm k ^ N * ‖scalarCoefficient ℓ f k‖) := by ring
    _ ≤ 2 ^ (N - 1) * (A + (n : ℝ) ^ N * (|ℓ| ^ N * A)) :=
      mul_le_mul_of_nonneg_left (add_le_add hz hd) (by positivity)
    _ = _ := by unfold coefficientConstant; ring

/-- One source derivative reserve, chosen before any requested high order in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def lowReserve (n : ℕ) : ℕ := n + 2

/-- The fixed reserve is strictly larger than `n+1`, as stipulated in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem dimension_add_one_lt_lowReserve (n : ℕ) : n + 1 < lowReserve n := by
  unfold lowReserve
  omega

/-- The single chosen source weight is summable by the existing physical
lattice estimate (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem summable_decayWeight_lowReserve (n : ℕ) :
    Summable (decayWeight (n := n) (lowReserve n)) := by
  apply (summable_one_add_frequencyNorm_inv_pow n).of_nonneg_of_le
  · intro k
    exact inv_nonneg.mpr (pow_nonneg (by linarith [frequencyNorm_nonneg k]) _)
  · intro k
    apply inv_anti₀ (pow_pos (by linarith [frequencyNorm_nonneg k]) _)
    apply pow_le_pow_right₀ (by linarith [frequencyNorm_nonneg k])
    exact Nat.le_add_right (n + 1) 1

/-- Absolute source coefficient convergence from one fixed physical derivative
reserve (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem summable_norm_scalarCoefficient (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : SupportedInCenteredBox R f) (hf : ContDiff ℝ ∞ f)
    {A : ℝ} (hzero : ∀ y, ‖f y‖ ≤ A)
    (hderiv : ∀ i y,
      ‖euclideanCoordinateDerivList (List.replicate (lowReserve n) i) f y‖ ≤ A) :
    Summable (fun k ↦ ‖scalarCoefficient ℓ f k‖) :=
  ((summable_decayWeight_lowReserve n).mul_left _).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (norm_scalarCoefficient_le hn hℓ hR hs hf _ hzero hderiv)

/-- A fixed cutoff equal to one on the original support and supported inside
the enlarged cell removes all periodic copies. This is an equality on Euclidean
space, not an identification of torus and Lebesgue data
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem cutoff_periodization_eq {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox R f)
    (β : EuclideanSpace ℝ (Fin n) → ℂ)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ y, f y ≠ 0 → β y = 1) (y : EuclideanSpace ℝ (Fin n)) :
    β y * boxAmplitudePeriodization ℓ f (scaledTorusChart ℓ y) = f y := by
  by_cases hb : β y = 0
  · have hz : f y = 0 := by
      by_contra hz
      have := hβone y hz
      simp [hb] at this
    simp [hb, hz]
  · have he := periodicLift_amplitudePeriodization_eq hR
      (supportedInCenteredBox_comp_smul hℓ hs) (hβcell y hb)
    change boxAmplitudePeriodization ℓ f (scaledTorusChart ℓ y) = f (ℓ • (ℓ⁻¹ • y)) at he
    rw [smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul] at he
    rw [he]
    by_cases hz : f y = 0
    · simp [hz]
    · rw [hβone y hz, one_mul]

/-- Exact source Fourier expansion with one fixed cutoff, at every physical
source point (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem hasSum_scalarCoefficient_cutoff (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : SupportedInCenteredBox R f) (hf : ContDiff ℝ ∞ f)
    {A : ℝ} (hzero : ∀ y, ‖f y‖ ≤ A)
    (hderiv : ∀ i y,
      ‖euclideanCoordinateDerivList (List.replicate (lowReserve n) i) f y‖ ≤ A)
    (β : EuclideanSpace ℝ (Fin n) → ℂ)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ y, f y ≠ 0 → β y = 1) (y : EuclideanSpace ℝ (Fin n)) :
    HasSum (fun k ↦ scalarCoefficient ℓ f k * (β y * sourceMode ℓ k y)) (f y) := by
  have he := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := ⟨boxAmplitudePeriodization ℓ f,
      (isSmoothPeriodic_boxAmplitudePeriodization hℓ hR hs hf).1⟩)
    (summable_norm_scalarCoefficient hn hℓ hR hs hf hzero hderiv).of_norm
    (scaledTorusChart ℓ y)
  have he' := he.mul_left (β y)
  change HasSum (fun k ↦ β y * (scalarCoefficient ℓ f k * sourceMode ℓ k y))
    (β y * boxAmplitudePeriodization ℓ f (scaledTorusChart ℓ y)) at he'
  rw [cutoff_periodization_eq hℓ hR hs β hβcell hβone y] at he'
  convert he' using 1
  funext k
  ring

end JanetCartan.FourierIntegral.SourceExpansion
