module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.OperatorIdentity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Source-first graph integrals on Schwartz data

The Fourier representation below evaluates the inner, physical source integral
of `graphOperator`. Polynomial growth then suffices for the outer integral and
for passage to frequency regularizations. These are the limiting steps needed
by `app:ch_regular_base:eq:fixed-source-multiplication`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Matrix.Norms.Frobenius RealInnerProductSpace Topology
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Unnormalized physical Fourier transform of vector input data. The prefactor
remains in `graphOperator`, as in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceInputFourierTransform (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    SchwartzMap (Euclidean n) (Fin r → ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean n)
      (Units.mk0 (2 * Real.pi)⁻¹ (by positivity))) (𝓕 u)

/-- The literal vector Fourier integral in physical covectors, used to evaluate
the source-first integral in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceInputFourierTransform_eq_integral
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (η : Euclidean n) :
    sourceInputFourierTransform u η =
      ∫ y, Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y := by
  change 𝓕 (u : Euclidean n → Fin r → ℂ) ((2 * Real.pi)⁻¹ • η) = _
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [real_inner_smul_right]
  congr 2
  have h : -2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ y η) = -inner ℝ y η := by
    field_simp
  rw [h, mul_comm]

/-- Evaluation of the source integral without changing the order of integration.
No integrability of the amplitude in frequency is required. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_eq_sourceFourierIntegral
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n) :
    graphOperator S (fun z _ η ↦ A z η) u x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η,
        Complex.exp (Complex.I * (S x η : ℂ)) •
          (A x η).mulVec (sourceInputFourierTransform u η) := by
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  have hi : Integrable (fun y ↦
      Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y) := by
    apply u.integrable.norm.mono'
    · exact (by fun_prop : Continuous (fun y ↦
        Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y)).aestronglyMeasurable
    · filter_upwards [] with y
      simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hL := (sourceMatrixAction (A x η)).integral_comp_comm hi
  change (∫ y, (A x η).mulVec
    (Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y)) =
    (A x η).mulVec (∫ y, Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y) at hL
  rw [sourceInputFourierTransform_eq_integral, ← hL, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Matrix.mulVec_smul, smul_smul, ← Complex.exp_add]
  congr 2
  simp only [graphOscillation, Complex.ofReal_sub, Complex.ofReal_neg]
  congr 1
  ring

/-- Absolute frequency convergence for polynomial amplitudes on Schwartz input.
The phase has modulus one, and the Fourier moments are proved by Schwartz
regularity (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem sourceFourierIntegral_integrable
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : AEStronglyMeasurable (A x))
    (C : ℝ) (k : ℕ) (hbound : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    Integrable (fun η ↦ Complex.exp (Complex.I * (S x η : ℂ)) •
      (A x η).mulVec (sourceInputFourierTransform u η)) := by
  let L := sourceMatrixAction (r := r)
  let f := sourceInputFourierTransform u
  apply ((f.integrable.norm.add (f.integrable_pow_mul volume k)).const_mul
    (L.opNorm * C)).mono'
  · exact (by fun_prop : Continuous (fun η ↦
      Complex.exp (Complex.I * (S x η : ℂ)))).aestronglyMeasurable.smul
        (L.continuous₂.comp_aestronglyMeasurable
          (hA.prodMk f.continuous.aestronglyMeasurable))
  · filter_upwards [] with η
    simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc
      _ ≤ L.opNorm * ‖A x η‖ * ‖f η‖ := L.le_opNorm₂ _ _
      _ ≤ L.opNorm * (C * (1 + ‖η‖ ^ k)) * ‖f η‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound η) (ContinuousLinearMap.opNorm_nonneg L))
          (norm_nonneg _)
      _ = _ := by simp only [Pi.add_apply]; ring

/-- Dominated convergence for source-first graphs on Schwartz data. This proves
agreement with literal frequency regularizations using only a common polynomial
bound, rather than assuming the operator limit in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_tendsto_of_polynomialBound
    (S : Euclidean n → Euclidean n → ℝ)
    (A : ℕ → Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : ∀ j, AEStronglyMeasurable (A j x))
    (C : ℝ) (k : ℕ) (hbound : ∀ j η, ‖A j x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (hlim : ∀ η, Tendsto (fun j ↦ A j x η) atTop (𝓝 (B x η))) :
    Tendsto (fun j ↦ graphOperator S (fun z _ η ↦ A j z η) u x)
      atTop (𝓝 (graphOperator S (fun z _ η ↦ B z η) u x)) := by
  simp_rw [graphOperator_eq_sourceFourierIntegral]
  apply Filter.Tendsto.const_smul
  let L := sourceMatrixAction (r := r)
  let f := sourceInputFourierTransform u
  apply tendsto_integral_of_dominated_convergence
    (fun η ↦ L.opNorm * C * (‖f η‖ + ‖η‖ ^ k * ‖f η‖))
  · intro j
    exact (sourceFourierIntegral_integrable S (A j) u x hS (hA j)
      C k (hbound j)).aestronglyMeasurable
  · exact (f.integrable.norm.add (f.integrable_pow_mul volume k)).const_mul _
  · intro j
    filter_upwards [] with η
    simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc
      _ ≤ L.opNorm * ‖A j x η‖ * ‖f η‖ := L.le_opNorm₂ _ _
      _ ≤ L.opNorm * (C * (1 + ‖η‖ ^ k)) * ‖f η‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound j η) L.opNorm_nonneg) (norm_nonneg _)
      _ = _ := by ring
  · filter_upwards [] with η
    exact (L.continuous₂.tendsto (B x η, f η) |>.comp
      ((hlim η).prodMk_nhds tendsto_const_nhds)).const_smul _

end JanetCartan.FourierIntegral
