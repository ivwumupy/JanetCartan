module
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PhaseTrade
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Actual first output derivatives of full graph kernels

The integrand formulas used for the order-minus-one gain in
`app:ch_regular_base:eq:fio-input`. The full matrix amplitude retains both
physical positions and every mask. Matrix calculus uses the Frobenius norm.

These are pointwise differentiation formulas, not differentiation under an
unregularized oscillatory integral or an assertion of symbol bounds.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- The complete first output amplitude of the forward graph.
Source: the gain-one argument following `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def graphFirstOutputAmplitude (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (i : Fin n) : FullAmplitude n r :=
  fun x y η ↦ partialDeriv (fun z ↦ A z y η) x i +
    (Complex.I * ((partialDeriv (fun z ↦ S z η) x i : ℝ) : ℂ)) • A x y η

/-- The complete first output amplitude of the literal adjoint, in original
`(x,y,η)` order; the output is `y`. This retains the conjugate transpose and
source-position masks. Source: `app:ch_regular_base:eq:fio-input`, gain-one argument. -/
def adjointFirstOutputAmplitude (A : FullAmplitude n r) (i : Fin n) : FullAmplitude n r :=
  fun x y η ↦ partialDeriv (fun z ↦ (A x z η).conjTranspose) y i +
    (Complex.I * (η i : ℂ)) • (A x y η).conjTranspose

/-- Actual first differentiation of the forward full matrix kernel.
Source: `app:ch_regular_base:eq:fio-input`, order-minus-one gain. -/
theorem partialDeriv_graphOscillation_smul_amplitude
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x y η : Euclidean n) (i : Fin n)
    (hS : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hA : DifferentiableAt ℝ (fun z ↦ A z y η) x) :
    partialDeriv (fun z ↦ graphOscillation S z y η • A z y η) x i =
      graphOscillation S x y η • graphFirstOutputAmplitude S A i x y η := by
  have hp : DifferentiableAt ℝ (fun z ↦ graphOscillation S z y η) x := by
    unfold graphOscillation
    fun_prop
  have hprod : partialDeriv (fun z ↦ graphOscillation S z y η • A z y η) x i =
      graphOscillation S x y η • partialDeriv (fun z ↦ A z y η) x i +
      partialDeriv (fun z ↦ graphOscillation S z y η) x i • A x y η := by
    simp only [partialDeriv, fderiv_fun_smul hp hA, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  rw [hprod, partialDeriv_graphOscillation_left hS]
  simp only [graphFirstOutputAmplitude, smul_add, smul_smul]
  rw [mul_comm (graphOscillation S x y η)]

/-- Actual first differentiation of the literal conjugate-transpose kernel.
Source: `app:ch_regular_base:eq:fio-input`, order-minus-one gain.
No phase linearization or weighted reverse-graph replacement is made. -/
theorem partialDeriv_adjointGraphOscillation_smul_amplitude
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x y η : Euclidean n) (i : Fin n)
    (hA : DifferentiableAt ℝ (fun z ↦ A x z η) y) :
    partialDeriv (fun z ↦ star (graphOscillation S x z η) • (A x z η).conjTranspose) y i =
      star (graphOscillation S x y η) • adjointFirstOutputAmplitude A i x y η := by
  have hp : DifferentiableAt ℝ (fun z ↦ star (graphOscillation S x z η)) y := by
    simp_rw [star_graphOscillation]
    have hr := ((innerSL ℝ η).hasFDerivAt (x := y)).sub_const (S x η)
    have hc := Complex.ofRealCLM.hasFDerivAt.comp y hr
    convert! (hc.const_mul Complex.I).cexp.differentiableAt using 1
    ext z
    simp [real_inner_comm]
  have hA' : DifferentiableAt ℝ (fun z ↦ (A x z η).conjTranspose) y := hA.star
  have hprod : partialDeriv
      (fun z ↦ star (graphOscillation S x z η) • (A x z η).conjTranspose) y i =
      star (graphOscillation S x y η) • partialDeriv (fun z ↦ (A x z η).conjTranspose) y i +
      partialDeriv (fun z ↦ star (graphOscillation S x z η)) y i • (A x y η).conjTranspose := by
    simp only [partialDeriv, fderiv_fun_smul hp hA', add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  rw [hprod, partialDeriv_star_graphOscillation_right]
  simp only [adjointFirstOutputAmplitude, smul_add, smul_smul]
  rw [mul_comm (star (graphOscillation S x y η))]

end JanetCartan.FourierIntegral
