module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Compact
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Literal forward integral of the compact L² graph

The definition of `T₀` immediately before
`app:ch_regular_base:eq:actual-normal-kernel` uses a source-independent amplitude
and Euclidean volume. We identify that iterated vector Bochner integral with
`compactGraph` on inputs whose scalar L² representatives also belong to L¹.

The source integral is evaluated by the ordinary Fourier transform, including
all finite matrix sums. Compact amplitude support makes the remaining frequency
integral integrable. The change `η = 2πξ` supplies exactly `(2π)⁻ⁿ`, and the L¹–L²
Fourier identification then gives coordinatewise almost-everywhere agreement.
This supplies the literal forward identification for the normal-kernel assembly;
no physical source cutoff is introduced.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped RealInnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ}

/-- Phase factorization used by `integral_graphOscillation_mulVec`, for the definition
of `T₀` preceding `app:ch_regular_base:eq:actual-normal-kernel`. -/
private theorem graphOscillation_eq_fourierChar
    (S : Euclidean n → Euclidean n → ℝ) (x y η : Euclidean n) :
    graphOscillation S x y η = Complex.exp (Complex.I * (S x η : ℂ)) *
      (Real.fourierChar (-⟪y, (2 * Real.pi)⁻¹ • η⟫) : ℂ) := by
  rw [graphOscillation, Real.fourierChar_apply, ← Complex.exp_add]
  congr 1
  simp only [real_inner_smul_right, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_ofNat]
  field_simp
  ring

/-- Evaluate the source integral of `T₀`, justifying vector evaluation and the
finite matrix sum using L¹ integrability. Used by `graphOperator_eq_physicalFourierIntegral`
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
private theorem integral_graphOscillation_mulVec (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (v : Euclidean n → Fin r → ℂ) (hv : ∀ k, Integrable (fun y ↦ v y k))
    (x η : Euclidean n) :
    (∫ y, graphOscillation S x y η • (A x η).mulVec (v y)) =
      fun i ↦ ∑ k, physicalEntry S (fun z η ↦ A z η i k) x η *
        𝓕 (fun y ↦ v y k) ((2 * Real.pi)⁻¹ • η) := by
  have he (y : Euclidean n) (i : Fin r) :
      (graphOscillation S x y η • (A x η).mulVec (v y)) i =
        ∑ k, physicalEntry S (fun z η ↦ A z η i k) x η *
          (Real.fourierChar (-⟪y, (2 * Real.pi)⁻¹ • η⟫) • v y k) := by
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum,
      graphOscillation_eq_fourierChar, physicalEntry, Circle.smul_def]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hi (i k : Fin r) := ((Real.fourierIntegral_convergent_iff
    ((2 * Real.pi)⁻¹ • η)).mpr (hv k)).const_mul
      (physicalEntry S (fun z η ↦ A z η i k) x η)
  funext i
  rw [eval_integral (fun i ↦ by
    simp_rw [he]
    exact integrable_finsetSum _ fun k _ ↦ hi i k)]
  simp_rw [he]
  rw [integral_finsetSum _ fun k _ ↦ hi i k]
  simp_rw [integral_const_mul, ← Real.fourier_eq]

/-- Compact amplitude support gives the frequency integrability needed by
`graphOperator_eq_physicalFourierIntegral`
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
private theorem integrable_physicalEntry_fourier
    {S : Euclidean n → Euclidean n → ℝ} {a : Euclidean n → Euclidean n → ℂ}
    (hS : Continuous (Function.uncurry S)) (ha : Continuous (Function.uncurry a))
    (hs : HasCompactSupport (Function.uncurry a))
    {v : Euclidean n → ℂ} (hv : Integrable v) (x : Euclidean n) :
    Integrable (fun η ↦ physicalEntry S a x η * 𝓕 v ((2 * Real.pi)⁻¹ • η)) := by
  have hc : Continuous (𝓕 v) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hv
  have hax : HasCompactSupport (a x) :=
    HasCompactSupport.of_support_subset_isCompact (hs.image continuous_snd) fun η hη ↦
      ⟨(x, η), subset_tsupport (Function.uncurry a) hη, rfl⟩
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((continuous_const.mul (Complex.continuous_ofReal.comp
      (hS.comp (continuous_const.prodMk continuous_id)))).cexp.mul
      (ha.comp (continuous_const.prodMk continuous_id))).mul
      (hc.comp (by fun_prop))
  · exact (hax.mul_left (f := fun η ↦ Complex.exp (Complex.I * (S x η : ℂ)))).mul_right

/-- Pass vector evaluation and the matrix sum through the outer integral of `T₀`.
Used by `compactGraph_ae_graphOperator`
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
private theorem graphOperator_eq_physicalFourierIntegral
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (v : Euclidean n → Fin r → ℂ) (hv : ∀ k, Integrable (fun y ↦ v y k))
    (x : Euclidean n) (i : Fin r) :
    graphOperator S (fun x _ η ↦ A x η) v x i =
      ∑ k, ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
        physicalEntry S (fun z η ↦ A z η i k) x η *
          𝓕 (fun y ↦ v y k) ((2 * Real.pi)⁻¹ • η) := by
  have hi (i k : Fin r) := integrable_physicalEntry_fourier hS
    (a := fun z η ↦ A z η i k) (hA i k) (hsA i k) (hv k) x
  simp only [graphOperator, integral_graphOscillation_mulVec S A v hv, Pi.smul_apply, smul_eq_mul]
  rw [eval_integral (fun i ↦ integrable_finsetSum _ fun k _ ↦ hi i k)]
  rw [integral_finsetSum _ fun k _ ↦ hi i k, Finset.mul_sum]

/-- The exact Euclidean Jacobian in `η = 2πξ`, used by
`compactGraph_ae_graphOperator` (`app:ch_regular_base:eq:actual-normal-kernel`). -/
private theorem frequencyIntegral_eq_physicalFourierIntegral
    (S : Euclidean n → Euclidean n → ℝ) (a : Euclidean n → Euclidean n → ℂ)
    (v : Euclidean n → ℂ) (x : Euclidean n) :
    (∫ ξ, frequencyEntry S a x ξ * 𝓕 v ξ) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
        physicalEntry S a x η * 𝓕 v ((2 * Real.pi)⁻¹ • η) := by
  have he (ξ : Euclidean n) :
      frequencyEntry S a x ξ * 𝓕 v ξ =
        (fun η ↦ physicalEntry S a x η * 𝓕 v ((2 * Real.pi)⁻¹ • η))
          ((2 * Real.pi) • ξ) := by
    simp only [frequencyEntry, smul_smul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  simp_rw [he]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun η ↦ physicalEntry S a x η * 𝓕 v ((2 * Real.pi)⁻¹ • η)) (2 * Real.pi) (hR := by positivity)]
  simp [finrank_euclideanSpace, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul]

/-- The compact graph agrees with the literal source-independent graph on L¹ ∩ L² data.
Source: `app:ch_regular_base:eq:actual-normal-kernel`, preceding definition of `T₀`. -/
theorem compactGraph_ae_graphOperator
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (f : NormalOutputL2 n r) (hf : ∀ k, Integrable (f k : Euclidean n → ℂ))
    (i : Fin r) :
    (compactGraph hS hA hsA f) i =ᵐ[volume]
      fun x ↦ graphOperator S (fun x _ η ↦ A x η) (fun y k ↦ f k y) x i := by
  refine (compactGraph_ae_frequencyIntegral hS hA hsA f i).trans
    (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [graphOperator_eq_physicalFourierIntegral hS hA hsA _ hf x i]
  apply Finset.sum_congr rfl
  intro k _
  rw [← frequencyIntegral_eq_physicalFourierIntegral]
  apply integral_congr_ae
  have he := Localization.fourierTransform_coeFn_ae_integral_hilbert (f k) (hf k)
  change fourierL2 n (f k) =ᵐ[volume] 𝓕 (f k : Euclidean n → ℂ) at he
  filter_upwards [he] with ξ hξ
  rw [hξ]

end JanetCartan.FourierIntegral.NormalKernel
