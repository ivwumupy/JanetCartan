module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Matrices
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The literal source expansion of compact-frequency graph integrals

Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. The consumer is the
bounded-operator identification in `FourierIntegral.SourceExpansion`. All
integrals below use Euclidean Lebesgue measure and physical covectors.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.SourceExpansion

open AmplitudeBound

variable {n r : ℕ}

private theorem norm_mulVec_le (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    ‖M.mulVec v‖ ≤ (r : ℝ) * ‖M‖ * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖M.mulVec v i‖ ≤ ∑ j, ‖M i j * v j‖ := by
      simpa only [Matrix.mulVec, dotProduct] using norm_sum_le Finset.univ (fun j ↦ M i j * v j)
    _ ≤ ∑ _j : Fin r, ‖M‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (norm_matrixEntry_le_frobenius M i j) (norm_le_pi_norm v j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

private theorem hasSum_mulVec {ι : Type*} {M : ι → Matrix (Fin r) (Fin r) ℂ}
    {a : Matrix (Fin r) (Fin r) ℂ} (h : HasSum M a) (v : Fin r → ℂ) :
    HasSum (fun k ↦ (M k).mulVec v) (a.mulVec v) := by
  apply Pi.hasSum.mpr
  intro i
  simpa only [Matrix.mulVec, dotProduct] using
    hasSum_sum (s := Finset.univ) (fun j _ ↦ ((Pi.hasSum.mp (Pi.hasSum.mp h i)) j).mul_right (v j))

private theorem norm_graphOscillation (S : Euclidean n → Euclidean n → ℝ)
    (x y η : Euclidean n) : ‖graphOscillation S x y η‖ = 1 := by
  simp [graphOscillation, Complex.norm_exp]

private theorem continuous_graphOscillation
    {S : Euclidean n → Euclidean n → ℝ}
    (hS : Continuous (Function.uncurry S)) (x : Euclidean n) :
    Continuous (fun p : Euclidean n × Euclidean n ↦ graphOscillation S x p.2 p.1) := by
  unfold graphOscillation
  have h : Continuous (fun p : Euclidean n × Euclidean n ↦ S x p.1) :=
    hS.comp (continuous_const.prodMk continuous_fst)
  fun_prop

/-- Parameter measurability of the actual coefficients, used for Fubini and
termwise integration in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem stronglyMeasurable_matrixCoefficient_entry (ℓ : ℝ) (A : FullAmplitude n r)
    (hA : ∀ x, Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (k : Fin n → ℤ) (x : Euclidean n) (i j : Fin r) :
    StronglyMeasurable (fun η ↦ matrixCoefficient ℓ A k x η i j) := by
  have hb : StronglyMeasurable (Function.uncurry (fun η y ↦ A x y η i j)) :=
    ((matrixEntryEvaluation i j).continuous.comp (hA x)).stronglyMeasurable
  exact (((UnitAddTorus.mFourier (-k)).continuous.stronglyMeasurable.comp_measurable
    measurable_snd).mul (stronglyMeasurable_boxAmplitudePeriodization hb ℓ)).integral_prod_right
      (ν := Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle))

/-- Reconstruction survives the ordered matrix action on a Euclidean vector.
This is the pointwise integrand identity for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem hasSum_source_kernel (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hf : ∀ x η, ContDiff ℝ ∞ (fun y ↦ A x y η))
    {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
        (fun y ↦ A x y η) y‖ ≤ B)
    (β : Euclidean n → ℂ)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ x η y, A x y η ≠ 0 → β y = 1)
    (S : Euclidean n → Euclidean n → ℝ) (θ : Euclidean n → ℂ)
    (v : Euclidean n → Fin r → ℂ) (x y η : Euclidean n) :
    HasSum (fun k ↦ graphOscillation S x y η •
      (θ η • matrixCoefficient ℓ A k x η).mulVec ((β y * sourceMode ℓ k y) • v y))
      (graphOscillation S x y η • (θ η • A x y η).mulVec (v y)) := by
  have h := (hasSum_mulVec
    (hasSum_matrixCoefficient_cutoff hn hℓ hR A hs hf hzero hderiv β hβcell hβone x y η)
    (v y)).const_smul (θ η) |>.const_smul (graphOscillation S x y η)
  simpa only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm (θ η)] using h

private theorem stronglyMeasurable_sourceKernel (ℓ : ℝ) (A : FullAmplitude n r)
    (hA : ∀ x, Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    {S : Euclidean n → Euclidean n → ℝ} (hS : Continuous (Function.uncurry S))
    {θ β : Euclidean n → ℂ} (hθ : Continuous θ) (hβ : Continuous β)
    {v : Euclidean n → Fin r → ℂ} (hv : Continuous v)
    (k : Fin n → ℤ) (x : Euclidean n) :
    StronglyMeasurable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x p.2 p.1 • (θ p.1 • matrixCoefficient ℓ A k x p.1).mulVec
        ((β p.2 * sourceMode ℓ k p.2) • v p.2)) := by
  apply Measurable.stronglyMeasurable
  apply Measurable.of_eval
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply]
  apply (continuous_graphOscillation hS x).measurable.mul
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · exact (hθ.measurable.comp measurable_fst).mul
      ((stronglyMeasurable_matrixCoefficient_entry ℓ A hA k x i j).measurable.comp
        measurable_fst)
  · exact ((hβ.measurable.comp measurable_snd).mul
      (((UnitAddTorus.mFourier k).continuous.measurable.comp
        (measurable_scaledTorusChart ℓ)).comp measurable_snd)).mul
      (((continuous_apply j).comp hv).measurable.comp measurable_snd)

private theorem norm_sourceKernel_le (ℓ : ℝ) (A : FullAmplitude n r)
    (S : Euclidean n → Euclidean n → ℝ) (θ β : Euclidean n → ℂ)
    (v : Euclidean n → Fin r → ℂ) (k : Fin n → ℤ) (x y η : Euclidean n)
    {C : ℝ} (hC : ‖matrixCoefficient ℓ A k x η‖ ≤ C) :
    ‖graphOscillation S x y η • (θ η • matrixCoefficient ℓ A k x η).mulVec
      ((β y * sourceMode ℓ k y) • v y)‖ ≤
      (r : ℝ) * C * (‖θ η‖ * ‖β y • v y‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  rw [norm_smul, norm_graphOscillation, one_mul]
  calc
    _ ≤ (r : ℝ) * ‖θ η • matrixCoefficient ℓ A k x η‖ *
        ‖(β y * sourceMode ℓ k y) • v y‖ := norm_mulVec_le _ _
    _ ≤ (r : ℝ) * (‖θ η‖ * C) * (‖β y‖ * 1 * ‖v y‖) := by
      simp only [norm_smul, norm_mul]
      gcongr
      exact norm_mFourier_apply_le_one k _
    _ = _ := by rw [norm_smul]; ring

/-- Exact source series for the same compact-frequency, iterated Euclidean
kernel, including `(2π)⁻ⁿ`. The source bounds use only the fixed reserve `n+2`.
All integrability and series/integral exchanges are derived here, for the
bounded-operator identification in `app:ch_regular_base:thm:actual-calculus`,
Step 1. Smoothness in the unused output parameter is harmless; the proof needs
only joint continuity and smooth source slices. -/
theorem hasSum_graphOperator_sourceExpansion (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hA : ∀ x, Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hf : ∀ x η, ContDiff ℝ ∞ (fun y ↦ A x y η))
    {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
        (fun y ↦ A x y η) y‖ ≤ B)
    (β : Euclidean n → ℂ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ x η y, A x y η ≠ 0 → β y = 1)
    (S : Euclidean n → Euclidean n → ℝ) (hS : Continuous (Function.uncurry S))
    (θ : Euclidean n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (x : Euclidean n) :
    HasSum (fun k ↦ graphOperator S (fun x _ η ↦ θ η • matrixCoefficient ℓ A k x η)
      (fun y ↦ (β y * sourceMode ℓ k y) • v y) x)
      (graphOperator S (fun x y η ↦ θ η • A x y η) v x) := by
  let F := fun (k : Fin n → ℤ) (p : Euclidean n × Euclidean n) ↦
    graphOscillation S x p.2 p.1 • (θ p.1 • matrixCoefficient ℓ A k x p.1).mulVec
      ((β p.2 * sourceMode ℓ k p.2) • v p.2)
  let H := fun p : Euclidean n × Euclidean n ↦
    graphOscillation S x p.2 p.1 • (θ p.1 • A x p.2 p.1).mulVec (v p.2)
  let q := fun p : Euclidean n × Euclidean n ↦ ‖θ p.1‖ * ‖β p.2 • v p.2‖
  let w := fun k : Fin n → ℤ ↦
    (r : ℝ) * ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ * B *
      decayWeight (lowReserve n) k)
  have hw : Summable w := ((summable_decayWeight_lowReserve n).mul_left _).mul_left _
  have hq : Integrable q (volume.prod volume) :=
    (hθ.continuous.integrable_of_hasCompactSupport hθc).norm.mul_prod
      ((hβ.continuous.smul hv.continuous).integrable_of_hasCompactSupport
        hβc.smul_right).norm
  have hFm (k) : StronglyMeasurable (F k) :=
    stronglyMeasurable_sourceKernel ℓ A hA hS hθ.continuous hβ.continuous hv.continuous k x
  have hFb (k p) : ‖F k p‖ ≤ w k * q p :=
    norm_sourceKernel_le ℓ A S θ β v k x p.2 p.1
      (norm_matrixCoefficient_le hn hℓ hR A hs hf _ hzero hderiv k x p.1)
  have hFi (k) : Integrable (F k) (volume.prod volume) :=
    (hq.const_mul (w k)).mono' (hFm k).aestronglyMeasurable
      (Eventually.of_forall (hFb k))
  have hHi : Integrable H (volume.prod volume) := by
    have hq0 : Integrable (fun p : Euclidean n × Euclidean n ↦ ‖θ p.1‖ * ‖v p.2‖)
        (volume.prod volume) := (hθ.continuous.integrable_of_hasCompactSupport hθc).norm.mul_prod
      (hv.continuous.integrable_of_hasCompactSupport hvc).norm
    apply (hq0.const_mul ((r : ℝ) * B)).mono'
    · exact ((continuous_graphOscillation hS x).smul
        (((hθ.continuous.comp continuous_fst).smul (hA x)).matrix_mulVec
          (hv.continuous.comp continuous_snd))).aestronglyMeasurable
    · apply Eventually.of_forall
      intro p
      dsimp only [H]
      rw [norm_smul, norm_graphOscillation, one_mul]
      calc
        _ ≤ (r : ℝ) * ‖θ p.1 • A x p.2 p.1‖ * ‖v p.2‖ := norm_mulVec_le _ _
        _ ≤ (r : ℝ) * (‖θ p.1‖ * B) * ‖v p.2‖ := by rw [norm_smul]; gcongr; exact hzero _ _ _
        _ = _ := by ring
  have hsum : HasSum (fun k ↦ ∫ p, F k p ∂(volume.prod volume))
      (∫ p, H p ∂(volume.prod volume)) := by
    apply hasSum_integral_of_dominated_convergence (fun k p ↦ w k * q p)
    · exact fun k ↦ (hFm k).aestronglyMeasurable
    · exact fun k ↦ Eventually.of_forall (hFb k)
    · exact Eventually.of_forall fun p ↦ hw.mul_right (q p)
    · simpa only [tsum_mul_right] using hq.const_mul (∑' k, w k)
    · exact Eventually.of_forall fun p ↦
        hasSum_source_kernel hn hℓ hR A hs hf hzero hderiv β hβcell hβone S θ v x p.2 p.1
  simp_rw [integral_prod _ (hFi _)] at hsum
  rw [integral_prod _ hHi] at hsum
  exact hsum.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- Jointly smooth full amplitudes give a convergent series of the literal
regularizations, as functions of the output point. The coefficients here are
those of the *same regularized amplitude*: `matrixCoefficient_external_smul`
identifies them with `θ η • matrixCoefficient ℓ A k x η`. This is the exact
identity required before taking bounded-operator limits in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem hasSum_graphOperator_regularizedSourceExpansion (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
        (fun y ↦ A x y η) y‖ ≤ B)
    (β : Euclidean n → ℂ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ x η y, A x y η ≠ 0 → β y = 1)
    (S : Euclidean n → Euclidean n → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (θ : Euclidean n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    HasSum (fun k ↦ graphOperator S
      (fun x _ η ↦ matrixCoefficient ℓ (fun x y η ↦ θ η • A x y η) k x η)
      (fun y ↦ (β y * sourceMode ℓ k y) • v y))
      (graphOperator S (fun x y η ↦ θ η • A x y η) v) := by
  have hAc (x) : Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1) :=
    hA.continuous.comp (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1))
      (by fun_prop)
  have hAf (x η) : ContDiff ℝ ∞ (fun y ↦ A x y η) :=
    hA.comp (f := fun y : Euclidean n ↦ (x, y, η)) (by fun_prop)
  apply Pi.hasSum.mpr
  intro x
  simpa only [matrixCoefficient_external_smul] using
    hasSum_graphOperator_sourceExpansion hn hℓ hR A hAc hs hAf hzero hderiv
      β hβ hβc hβcell hβone S hS.continuous θ hθ hθc v hv hvc x

/-- The literal full graph regularization equals its source-independent graph
series, with physical modes and unchanged matrix multiplication order
(`app:ch_regular_base:thm:actual-calculus`, Step 1). Convergence is supplied by
`hasSum_graphOperator_regularizedSourceExpansion`, not postulated. -/
theorem graphOperator_eq_tsum_sourceExpansion (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
        (fun y ↦ A x y η) y‖ ≤ B)
    (β : Euclidean n → ℂ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ x η y, A x y η ≠ 0 → β y = 1)
    (S : Euclidean n → Euclidean n → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (θ : Euclidean n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    graphOperator S (fun x y η ↦ θ η • A x y η) v =
      ∑' k, graphOperator S (fun x _ η ↦ θ η • matrixCoefficient ℓ A k x η)
        (fun y ↦ (β y * sourceMode ℓ k y) • v y) := by
  simpa only [matrixCoefficient_external_smul] using
    (hasSum_graphOperator_regularizedSourceExpansion hn hℓ hR A hA hs hzero hderiv
      β hβ hβc hβcell hβone S hS θ hθ hθc v hv hvc).tsum_eq.symm

end JanetCartan.FourierIntegral.SourceExpansion
