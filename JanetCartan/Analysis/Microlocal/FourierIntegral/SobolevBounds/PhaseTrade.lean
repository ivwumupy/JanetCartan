module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Nonlinear graph phase derivative trades

The two phase identities used in Step 3 of
`app:ch_regular_base:thm:actual-calculus`. The phase and mixed matrix are the
actual definitions of `FourierIntegral.Kernel`, in physical covectors.

The hypotheses are local differentiability, local degree-one homogeneity, and
(for the reverse trade) invertibility of the actual mixed matrix. They must be
instantiated by the Hamilton phase and compatible geometry constructions.
No operator derivative identity or Sobolev bound is assumed or asserted here.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan.FourierIntegral

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ} {x η : Euclidean n}

/-- Euler's forward trade `S_x = S_{xη} η`, derived by differentiating
local homogeneity first in position and then in the radial parameter.
Source: Step 3 preceding `app:ch_regular_base:eq:actual-adjoint-trade`.
The nested neighborhood hypothesis allows a physical neighborhood depending
on the radial parameter, so only homogeneity on the actual phase chart is needed. -/
theorem partialDeriv_eq_mixedPhaseMatrix_mulVec
    (hx : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hη : ∀ i, DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η)
    (hhom : ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η)) (i : Fin n) :
    partialDeriv (fun z ↦ S z η) x i =
      ∑ j, mixedPhaseMatrix S x η i j * η j := by
  let f := fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i
  have hscale : ∀ᶠ t : ℝ in 𝓝 1, f (t • η) = t * f η := by
    filter_upwards [hhom] with t ht
    have hd := (hx.hasFDerivAt.const_mul t).congr_of_eventuallyEq ht
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hd.fderiv
  have hd : HasDerivAt (fun t : ℝ ↦ f (t • η)) (fderiv ℝ f η η) 1 := by
    have hf : HasFDerivAt f (fderiv ℝ f η) ((1 : ℝ) • η) := by
      simpa [f] using (hη i).hasFDerivAt
    convert! hf.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const η) using 1
    simp
  have he := (hd.congr_of_eventuallyEq (Filter.EventuallyEq.symm hscale)).unique
    ((hasDerivAt_id (1 : ℝ)).mul_const (f η))
  simp only [one_mul] at he
  have hs := congrArg (fderiv ℝ f η) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr η)
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul] at hs
  exact he.symm.trans (by simpa [f, mixedPhaseMatrix, partialDeriv, mul_comm] using hs.symm)

/-- The actual graph exponential differentiated in its output position.
Source: the first-output-derivative argument for `app:ch_regular_base:eq:fio-input`.
The covector is physical, so there is no extra `2π` factor. -/
theorem partialDeriv_graphOscillation_left
    (hx : DifferentiableAt ℝ (fun z ↦ S z η) x) (y : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ graphOscillation S z y η) x i =
      Complex.I * ((partialDeriv (fun z ↦ S z η) x i : ℝ) : ℂ) * graphOscillation S x y η := by
  have hr := hx.hasFDerivAt.sub_const (inner ℝ y η)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  have he := (hc.const_mul Complex.I).cexp
  have h := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) he.fderiv
  simpa [partialDeriv, graphOscillation, mul_comm, mul_left_comm, mul_assoc] using h

/-- The literal conjugate phase, with both physical positions retained.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem star_graphOscillation (x y η : Euclidean n) :
    star (graphOscillation S x y η) =
      Complex.exp (Complex.I * ((inner ℝ y η - S x η : ℝ) : ℂ)) := by
  change starRingEnd ℂ (Complex.exp _) = _
  simp only [← Complex.exp_conj, map_mul, Complex.conj_I, map_sub,
    Complex.conj_ofReal, Complex.ofReal_sub]
  congr 1
  ring

/-- The literal conjugate phase differentiated in the original output position.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem partialDeriv_star_graphOscillation_left
    (hx : DifferentiableAt ℝ (fun z ↦ S z η) x) (y : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ star (graphOscillation S z y η)) x i =
      -(Complex.I * ((partialDeriv (fun z ↦ S z η) x i : ℝ) : ℂ) *
        star (graphOscillation S x y η)) := by
  simp_rw [star_graphOscillation]
  have hr := hx.hasFDerivAt.const_sub (inner ℝ y η)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  have he := (hc.const_mul Complex.I).cexp
  have h := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) he.fderiv
  simpa [partialDeriv, mul_comm, mul_left_comm, mul_assoc] using h

/-- The actual graph phase differentiated in its source position.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem partialDeriv_graphOscillation_right (x y η : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ graphOscillation S x z η) y i =
      -(Complex.I * (η i : ℂ) * graphOscillation S x y η) := by
  have hr := ((innerSL ℝ η).hasFDerivAt (x := y)).const_sub (S x η)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp y hr
  have he := (hc.const_mul Complex.I).cexp
  have h := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) he.fderiv
  simpa [partialDeriv, graphOscillation, EuclideanSpace.inner_single_right,
    real_inner_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- The first output derivative of the literal adjoint phase (the original
source position). Source: the gain-one argument for `app:ch_regular_base:eq:fio-input`. -/
theorem partialDeriv_star_graphOscillation_right (x y η : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ star (graphOscillation S x z η)) y i =
      Complex.I * (η i : ℂ) * star (graphOscillation S x y η) := by
  simp_rw [star_graphOscillation]
  have hr := ((innerSL ℝ η).hasFDerivAt (x := y)).sub_const (S x η)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp y hr
  have he := (hc.const_mul Complex.I).cexp
  have h := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) he.fderiv
  simpa [partialDeriv, EuclideanSpace.inner_single_right, real_inner_comm,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The nonlinear forward phase trade, with the actual mixed matrix.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`.
This is the pointwise identity to integrate by parts in the source position. -/
theorem graphOscillation_forward_trade
    (hx : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hη : ∀ i, DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η)
    (hhom : ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η)) (y : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ graphOscillation S z y η) x i =
      -∑ j, (mixedPhaseMatrix S x η i j : ℂ) *
        partialDeriv (fun z ↦ graphOscillation S x z η) y j := by
  rw [partialDeriv_graphOscillation_left hx,
    partialDeriv_eq_mixedPhaseMatrix_mulVec hx hη hhom]
  simp_rw [partialDeriv_graphOscillation_right]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul,
    mul_neg, Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The literal adjoint phase trade with the inverse of the actual mixed
matrix, including its minus sign and index order.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`.
This is a pointwise phase identity; passing to weak operator derivatives
additionally requires the compact-support integration-by-parts argument. -/
theorem graphOscillation_adjoint_trade
    (hx : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hη : ∀ i, DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η)
    (hhom : ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η))
    (hinv : IsUnit (mixedPhaseMatrix S x η).det) (y : Euclidean n) (i : Fin n) :
    Complex.I * (η i : ℂ) * star (graphOscillation S x y η) =
      -∑ j, ((mixedPhaseMatrix S x η)⁻¹ i j : ℂ) *
        partialDeriv (fun z ↦ star (graphOscillation S z y η)) x j := by
  have hv : (mixedPhaseMatrix S x η)⁻¹.mulVec
      (fun j ↦ partialDeriv (fun z ↦ S z η) x j) = fun j ↦ η j := by
    have he : (fun j ↦ partialDeriv (fun z ↦ S z η) x j) =
        (mixedPhaseMatrix S x η).mulVec (fun j ↦ η j) := by
      funext j
      exact partialDeriv_eq_mixedPhaseMatrix_mulVec hx hη hhom j
    rw [he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]
  have hi : (∑ j, (mixedPhaseMatrix S x η)⁻¹ i j *
      partialDeriv (fun z ↦ S z η) x j) = η i := congrFun hv i
  rw [← hi]
  simp_rw [partialDeriv_star_graphOscillation_left hx]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul,
    mul_neg, Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro j _
  ring

end JanetCartan.FourierIntegral
