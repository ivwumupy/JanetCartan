module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.PhysicalFourier
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Exact source symbol and remainder

Definitions for `app:ch_regular_base:eq:fixed-source-multiplication`. The phase
and symbol arguments are the globally extended ones: angular and low-frequency
pieces are retained in these arguments. No truncation of the shift integral is
made. The parent construction must supply these extensions and their bounds.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.FourierIntegral

variable {n r : ℕ}

/-- The matrix extended norm used for the absolutely convergent symbol integral
in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
local instance sourceSymbolContinuousENorm {r : ℕ} : ContinuousENorm (Matrix (Fin r) (Fin r) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin r) (Fin r) ℂ) inferInstance).toContinuousENorm

/-- The ordinary finite matrix topology used for the source integral's
measurability in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
local instance sourceSymbolPseudoMetrizableSpace {r : ℕ} : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin r → Fin r → ℂ))

/-- The exact shifted integrand defining `b` in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceSymbolIntegrand (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η v : Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  (sourceFourierTransform m v *
    Complex.exp (Complex.I * ((S x (η + v) - S x η : ℝ) : ℂ))) • A x (η + v)

/-- The literal absolutely convergent source symbol of
`app:ch_regular_base:eq:fixed-source-multiplication`. Convergence follows from
`sourceSymbolIntegrand_integrable` under finite polynomial growth. -/
def sourceSymbol (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ := ∫ v, sourceSymbolIntegrand S A m x η v

/-- The exact remainder, including all extended angular and bounded-frequency
pieces, of `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceRemainder (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  sourceSymbol S A m x η - m (gradient (S x) η) • A x η

/-- The segment used in the FTC proof following
`app:ch_regular_base:eq:fixed-source-multiplication`. Its endpoints are the exact
shifted amplitude and the Fourier representation of the principal amplitude. -/
def sourceSymbolSegment (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η v : Euclidean n) (t : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Complex.exp (Complex.I * ((S x (η + t • v) - S x η +
    (1 - t) * inner ℝ (gradient (S x) η) v : ℝ) : ℂ)) • A x (η + t • v)

/-- The two differentiated amplitudes in the manuscript's source FTC formula:
`v · A_η` and `i (S_η(η+tv) - S_η(η)) · v A`.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceSymbolSegmentDerivative (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η v : Euclidean n) (t : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Complex.exp (Complex.I * ((S x (η + t • v) - S x η +
    (1 - t) * inner ℝ (gradient (S x) η) v : ℝ) : ℂ)) •
      (fderiv ℝ (A x) (η + t • v) v +
        (Complex.I * ((inner ℝ (gradient (S x) (η + t • v) -
          gradient (S x) η) v : ℝ) : ℂ)) • A x (η + t • v))

/-- The shift integral for the source symbol is absolutely integrable. The only
growth input is a finite polynomial bound on the supplied extended symbol;
Schwartz moments are proved, not assumed. This is the convergence assertion in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbolIntegrand_integrable
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) (C : ℝ) (k : ℕ)
    (hbound : ∀ v, ‖A x (η + v)‖ ≤ C * (1 + ‖v‖ ^ k)) :
    Integrable (sourceSymbolIntegrand S A m x η) := by
  have hmajor : Integrable (fun v ↦ C *
      (‖sourceFourierTransform m v‖ + ‖v‖ ^ k * ‖sourceFourierTransform m v‖)) :=
    ((sourceFourierTransform m).integrable.norm.add
      (sourceFourierTransform_integrable_moment m k)).const_mul C
  apply hmajor.mono'
  · exact (by unfold sourceSymbolIntegrand; fun_prop :
      Continuous (sourceSymbolIntegrand S A m x η)).aestronglyMeasurable
  · filter_upwards [] with v
    simp only [sourceSymbolIntegrand, norm_smul, norm_mul]
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
    calc
      _ ≤ ‖sourceFourierTransform m v‖ * (C * (1 + ‖v‖ ^ k)) :=
        mul_le_mul_of_nonneg_left (hbound v) (norm_nonneg _)
      _ = _ := by ring

/-- Translation of the primitive polynomial symbol bound into the shift bound
used by `sourceSymbolIntegrand_integrable`. The constant may depend on the base
covector; quantitative uniform bounds belong to the separate remainder task.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceAmplitude_shifted_growth
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η : Euclidean n) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ ξ, ‖A x ξ‖ ≤ C * (1 + ‖ξ‖ ^ k)) :
    ∃ D : ℝ, ∀ v, ‖A x (η + v)‖ ≤ D * (1 + ‖v‖ ^ k) := by
  refine ⟨C * (1 + 2 ^ (k - 1) * (‖η‖ ^ k + 1)), fun v ↦ ?_⟩
  have hpow : ‖η + v‖ ^ k ≤ 2 ^ (k - 1) * (‖η‖ ^ k + ‖v‖ ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le η v) k).trans
      (add_pow_le (norm_nonneg η) (norm_nonneg v) k)
  apply (hbound (η + v)).trans
  have hweight : 1 + ‖η + v‖ ^ k ≤
      (1 + 2 ^ (k - 1) * (‖η‖ ^ k + 1)) * (1 + ‖v‖ ^ k) := by
    have ha : 0 ≤ 2 ^ (k - 1) * ‖η‖ ^ k * ‖v‖ ^ k := by positivity
    have hb : 0 ≤ (2 : ℝ) ^ (k - 1) := by positivity
    have hc : 0 ≤ ‖v‖ ^ k := by positivity
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hweight hC

/-- Absolute convergence from an ordinary global polynomial symbol bound.
This discharges the shifted-growth premise of the source integral from the
primitive hypothesis in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbolIntegrand_integrable_of_polynomialGrowth
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ ξ, ‖A x ξ‖ ≤ C * (1 + ‖ξ‖ ^ k)) :
    Integrable (sourceSymbolIntegrand S A m x η) := by
  obtain ⟨D, hD⟩ := sourceAmplitude_shifted_growth A x η C hC k hbound
  exact sourceSymbolIntegrand_integrable S A m x η hS hA D k hD

end JanetCartan.FourierIntegral
