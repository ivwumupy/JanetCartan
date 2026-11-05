module

public import JanetCartan.Analysis.Fourier.Periodic.Sobolev.DerivativeEnergy
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Cartesian derivative Sobolev norms on Euclidean domains

The norm in `app:ch_regular_base:eq:ball-extension-sobolev` is the square
root of the sum of the integrals of the squared Cartesian derivatives. We reuse
the project's multiindex enumeration and canonical coordinate list. The slack
coordinate counts each multiindex of order at most `m` exactly once.

The auxiliary Fréchet energy is kept separate: identifying it up to constants
with the Cartesian energy requires a proof, not a change of norm definition.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.BallExtension

variable {n : ℕ}

/-- Cartesian multiindex derivative, evaluated on the standard unit vectors in
the canonical order, for `app:ch_regular_base:eq:ball-extension-sobolev`.
Within derivatives also give intrinsic jets on the closed input ball. -/
def cartesianDerivativeWithin (α : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  iteratedFDerivWithin ℝ (sobolevDerivativeList α).length f s x
    (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList α).get j))

/-- The actual squared derivative Sobolev norm in
`app:ch_regular_base:eq:ball-extension-sobolev`, with Lebesgue measure and
each Cartesian multiindex appearing once. Integrability is proved separately. -/
def cartesianSobolevEnergy (s : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∑ α ∈ sobolevMultiindices n m,
    ∫ x in s, (cartesianDerivativeWithin (fun i ↦ α (some i)) f s x) ^ 2

/-- The derivative `H^m` norm of `app:ch_regular_base:eq:ball-extension-sobolev`.
Use `s = univ` for the whole-space norm and the open ball for the input norm. -/
def cartesianSobolevNorm (s : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  Real.sqrt (cartesianSobolevEnergy s m f)

/-- Auxiliary sum of squared operator norms of Fréchet jets for the estimates in
`app:ch_regular_base:eq:extension-collar-l2`. This is not the definition of the
manuscript's Cartesian norm. -/
def frechetSobolevEnergy (s : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), ∫ x in s, ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2

/-- Nonnegativity of the Cartesian energy in
`app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem cartesianSobolevEnergy_nonneg (s : Set (EuclideanSpace ℝ (Fin n)))
    (m : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    0 ≤ cartesianSobolevEnergy s m f := by
  exact Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))

/-- Nonnegativity of the derivative norm in
`app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem cartesianSobolevNorm_nonneg (s : Set (EuclideanSpace ℝ (Fin n)))
    (m : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    0 ≤ cartesianSobolevNorm s m f := Real.sqrt_nonneg _

/-- Squaring recovers the exact finite sum of squared derivative integrals in
`app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem cartesianSobolevNorm_sq (s : Set (EuclideanSpace ℝ (Fin n)))
    (m : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    cartesianSobolevNorm s m f ^ 2 = cartesianSobolevEnergy s m f :=
  Real.sq_sqrt (cartesianSobolevEnergy_nonneg s m f)

/-- Nonnegativity of the auxiliary Fréchet energy for
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem frechetSobolevEnergy_nonneg (s : Set (EuclideanSpace ℝ (Fin n)))
    (m : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    0 ≤ frechetSobolevEnergy s m f := by
  exact Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))

/-- Each Cartesian jet is a unit-vector evaluation of the corresponding Fréchet
jet, as used in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem norm_cartesianDerivativeWithin_le (α : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖cartesianDerivativeWithin α f s x‖ ≤
      ‖iteratedFDerivWithin ℝ (∑ i, α i) f s x‖ := by
  unfold cartesianDerivativeWithin
  have h := (iteratedFDerivWithin ℝ (sobolevDerivativeList α).length f s x).le_opNorm
    (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList α).get j))
  simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] at h
  exact h.trans_eq (congrArg (fun j ↦ ‖iteratedFDerivWithin ℝ j f s x‖)
    (sobolevDerivativeList_length α))

/-- Continuity of the Cartesian jets on a domain with unique derivatives, used
to prove finiteness of the norm in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem continuousOn_cartesianDerivativeWithin
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : UniqueDiffOn ℝ s)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f s)
    (α : Fin n → ℕ) : ContinuousOn (cartesianDerivativeWithin α f s) s :=
  (hf.continuousOn_iteratedFDerivWithin (by simp) hs).eval continuousOn_const

/-- On the whole space, Cartesian jets of a smooth function are continuous,
as required in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem continuous_cartesianDerivativeWithin_univ
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (α : Fin n → ℕ) : Continuous (cartesianDerivativeWithin α f univ) :=
  continuousOn_univ.mp (continuousOn_cartesianDerivativeWithin uniqueDiffOn_univ
    hf.contDiffOn α)

/-- Compact support is preserved by Cartesian differentiation, as used for the
whole-space norm in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem hasCompactSupport_cartesianDerivativeWithin_univ
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : HasCompactSupport f)
    (α : Fin n → ℕ) : HasCompactSupport (cartesianDerivativeWithin α f univ) := by
  unfold cartesianDerivativeWithin
  simp only [iteratedFDerivWithin_univ]
  exact
    (hf.iteratedFDeriv (𝕜 := ℝ) (sobolevDerivativeList α).length).comp_left
      (g := fun A ↦ A (fun j ↦
        EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList α).get j)))
      (by simp)

end JanetCartan.BallExtension
