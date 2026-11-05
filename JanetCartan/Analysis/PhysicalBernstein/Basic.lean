module

public import Mathlib.Analysis.Fourier.LpSpace
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Physical Euclidean band limitation

The global increments in paper-v2, `new:lem:bernstein(ii)` and
`main:eq:final-Cr`, are measured with Lebesgue L² on the same whole-space
representative. Mathlib's unit-period Fourier variable `ξ` represents the
physical covector `(2π) • ξ`. These definitions do not involve stage or accuracy.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.PhysicalBernstein

variable {n N : ℕ}

/-- Whole-space physical L² norm for `new:lem:bernstein(ii)`. Membership in L²
is supplied by the concrete Schwartz increment, not encoded by this total norm. -/
def physicalL2Norm (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)) : ℝ :=
  (eLpNorm u 2 volume).toReal

/-- Physical Fourier support in the closed ball of radius `Λ`, for the SAME
real global field, using its norm-preserving complex inclusion
(`new:lem:bernstein(ii)`). -/
def HasFourierSupport (Λ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)) : Prop :=
  ∀ ξ, Λ < ‖(2 * Real.pi) • ξ‖ →
    𝓕 (fun x ↦ euclideanComplexInclusion (u x)) ξ = 0

/-- Physical L² is nonnegative (`main:eq:final-Cr`). -/
theorem physicalL2Norm_nonneg
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)) :
    0 ≤ physicalL2Norm u := ENNReal.toReal_nonneg

/-- On Schwartz increments the physical L² norm is the actual Hilbert-space
norm, with no periodic normalization (`main:eq:final-Cr`). -/
theorem physicalL2Norm_eq_norm_toLp
    (u : SchwartzMap (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin N))) :
    physicalL2Norm u = ‖u.toLp 2 volume‖ := SchwartzMap.norm_toLp.symm

end JanetCartan.PhysicalBernstein
