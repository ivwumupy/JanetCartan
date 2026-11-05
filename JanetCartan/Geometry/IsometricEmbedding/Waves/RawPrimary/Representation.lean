module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Integral representation of demodulated primary fields

The exact integral identity from `app:ch_waves:eq:individual-representation` and
its order-zero Fourier-variation estimate. The phase and atomic amplitude are
explicit inputs: identifying the latter with the differential of the constructed
WKB wave is a separate obligation. No derivative or slice estimate is assumed here.

We integrate a complex density against an arbitrary positive measure. This covers
ordinary Fourier densities and atomic data, without identifying the initial
Fourier measure with a physical-variable measure. The codomain is an arbitrary
complex normed space, so these identities also apply to Frobenius matrix norms.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {X P F : Type*} [AddCommGroup P] [Module ℝ P] [MeasurableSpace P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- The exact shifted phase quotient in `app:ch_waves:eq:individual-representation`.
Applications use a nonzero inverse frequency; this algebraic definition is total. -/
def rawPrimaryPhaseDifference (S : X → P → ℝ) (ζ : P) (τ : ℝ) (x : X) (η : P) : ℝ :=
  (S x (ζ + τ • η) - S x ζ) / τ

/-- Integral of the shifted modulated atomic amplitude
(`app:ch_waves:eq:WKB-W`, after differentiation of the atomic wave). -/
def rawPrimaryShiftedIntegral (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) (x : X) : F :=
  ∫ η, Complex.exp (Complex.I * (S x (ζ + τ • η) / τ : ℝ)) •
    (f η • A x (ζ + τ • η)) ∂μ

/-- The right side of `app:ch_waves:eq:individual-representation`. -/
def rawPrimaryDemodulatedIntegral (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) (x : X) : F :=
  ∫ η, Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
    (f η • A x (ζ + τ • η)) ∂μ

/-- Exact demodulation under the Fourier integral
(`app:ch_waves:eq:individual-representation`). -/
theorem rawPrimaryDemodulatedIntegral_eq (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) (x : X) :
    rawPrimaryDemodulatedIntegral S A ζ τ μ f x =
      Complex.exp (-Complex.I * (S x ζ / τ : ℝ)) •
        rawPrimaryShiftedIntegral S A ζ τ μ f x := by
  rw [rawPrimaryDemodulatedIntegral, rawPrimaryShiftedIntegral, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  have hphase : Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ) =
      -Complex.I * (S x ζ / τ : ℝ) +
        Complex.I * (S x (ζ + τ • η) / τ : ℝ) := by
    simp only [rawPrimaryPhaseDifference, sub_div, Complex.ofReal_sub]
    ring
  rw [hphase, Complex.exp_add, mul_smul]

omit [MeasurableSpace P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- The norm of the integrand loses no oscillatory factor
(`app:ch_waves:eq:raw-physical-bound`, order zero). -/
theorem norm_rawPrimaryDemodulatedIntegrand (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (f : P → ℂ) (x : X) (η : P) :
    ‖Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
      (f η • A x (ζ + τ • η))‖ = ‖f η‖ * ‖A x (ζ + τ • η)‖ := by
  simp only [norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- Fourier `L¹` data and a bounded, measurable atomic integrand give a genuine
Bochner integral (`app:ch_waves:thm:individual`). -/
theorem integrable_rawPrimaryDemodulatedIntegrand (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) {μ : Measure P} {f : P → ℂ} (x : X)
    (hf : Integrable f μ) {C : ℝ}
    (hA : ∀ᵐ η ∂μ, ‖A x (ζ + τ • η)‖ ≤ C)
    (hm : AEStronglyMeasurable (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
        (f η • A x (ζ + τ • η))) μ) :
    Integrable (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
        (f η • A x (ζ + τ • η))) μ := by
  apply (hf.norm.mul_const C).mono' hm
  filter_upwards [hA] with η hη
  rw [norm_rawPrimaryDemodulatedIntegrand]
  exact mul_le_mul_of_nonneg_left hη (norm_nonneg _)

omit [IsScalarTower ℝ ℂ F] in
/-- The order-zero physical estimate with exactly the Fourier-density `L¹` mass
(`app:ch_waves:eq:raw-physical-bound`). Higher physical orders require the WKB
phase and amplitude grading, and are not asserted by this theorem. -/
theorem norm_rawPrimaryDemodulatedIntegral_le (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) {μ : Measure P} {f : P → ℂ} (x : X)
    (hf : Integrable f μ) {C : ℝ}
    (hA : ∀ᵐ η ∂μ, ‖A x (ζ + τ • η)‖ ≤ C) :
    ‖rawPrimaryDemodulatedIntegral S A ζ τ μ f x‖ ≤ C * ∫ η, ‖f η‖ ∂μ := by
  calc
    _ ≤ ∫ η, ‖f η‖ * C ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.mul_const C)
      filter_upwards [hA] with η hη
      rw [norm_rawPrimaryDemodulatedIntegrand]
      exact mul_le_mul_of_nonneg_left hη (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

omit [IsScalarTower ℝ ℂ F] in
/-- The separate zero Fourier atom yields the unshifted derivative amplitude
(`app:ch_waves:eq:WKB-W`); no annular half-derivative is applied to it. -/
theorem rawPrimaryDemodulatedIntegral_zero_atom [MeasurableSingletonClass P] [CompleteSpace F]
    (S : X → P → ℝ) (A : X → P → F) (ζ : P) (τ : ℝ) (c : ℂ) (x : X) :
    rawPrimaryDemodulatedIntegral S A ζ τ (Measure.dirac 0) (fun _ ↦ c) x =
      c • A x ζ := by
  simp [rawPrimaryDemodulatedIntegral, rawPrimaryPhaseDifference]

/-- Complex homogeneity in the Fourier density (`app:ch_waves:eq:WKB-W`). -/
theorem rawPrimaryDemodulatedIntegral_smul (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) (c : ℂ) (x : X) :
    rawPrimaryDemodulatedIntegral S A ζ τ μ (c • f) x =
      c • rawPrimaryDemodulatedIntegral S A ζ τ μ f x := by
  unfold rawPrimaryDemodulatedIntegral
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_comm _ c]
  exact integral_smul c _

omit [IsScalarTower ℝ ℂ F] in
/-- Additivity in Fourier data when both atomic integrands are integrable
(`app:ch_waves:eq:WKB-W`). Integrability can be supplied by
`integrable_rawPrimaryDemodulatedIntegrand`. -/
theorem rawPrimaryDemodulatedIntegral_add (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f g : P → ℂ) (x : X)
    (hf : Integrable (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
        (f η • A x (ζ + τ • η))) μ)
    (hg : Integrable (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
        (g η • A x (ζ + τ • η))) μ) :
    rawPrimaryDemodulatedIntegral S A ζ τ μ (f + g) x =
      rawPrimaryDemodulatedIntegral S A ζ τ μ f x +
        rawPrimaryDemodulatedIntegral S A ζ τ μ g x := by
  simp only [rawPrimaryDemodulatedIntegral, Pi.add_apply, add_smul, smul_add]
  exact integral_add hf hg

end JanetCartan
