module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.CoordinateInverse.Plateau
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.OscillatoryDiagonal

/-!
# The full PDO reduction remainder in the weighted inverse

Entrywise use of the existing exact two-position PDO diagonal reduction for
`app:ch_regular_base:eq:actual-right-inverse`. The remainder below is the actual
Taylor/divergence amplitude, not an unspecified inverse defect. The graph-normal
change of variables must supply `c` and its diagonal identification. The finite
calculus must supply the displayed source-integral bounds.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace JanetCartan.FourierIntegral.CoordinateInverse

variable {n : ℕ}

/-- The diagonal source cutoff drops out on the actual inner input. This is
an identity for the full two-position PDO, not a symbolic approximation.
Source: `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem diagonalAmplitude_inner_input
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (β : Euclidean n → ℝ) (u : 𝓢(Euclidean n, ℂ))
    (hβu : ∀ y, u y ≠ 0 → β y = 1) (x : Euclidean n) :
    Pseudodifferential.fullAmplitudeOperator (Pseudodifferential.diagonalAmplitude c β) u x =
      Pseudodifferential.sourceIndependentOperator (fun x ξ ↦ c x x ξ) u x := by
  rw [Pseudodifferential.fullAmplitudeOperator_diagonalAmplitude]
  have hmask : (fun y ↦ β y • u y) = (u : Euclidean n → ℂ) := by
    funext y
    by_cases h : u y = 0
    · simp [h]
    · simp [hβu y h]
  rw [hmask, Pseudodifferential.fullAmplitudeOperator_sourceIndependent]

/-- Exact scalar entry of the weighted cross-normal reduction, retaining the
full source-dependent Taylor remainder. The principal term is the actual
`χg(η(x,x,2πξ))²` and its source mask is removed by the inner input support.
Consumer: the `Rdiag` term in `localized_coordinate_inverse_ledger`.
Source: `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem weighted_diagonal_reduction
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (χg β : Euclidean n → ℝ) (u : 𝓢(Euclidean n, ℂ)) (x : Euclidean n)
    (hc : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β)
    (hβc : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hβu : ∀ y, u y ≠ 0 → β y = 1)
    (huc : HasCompactSupport (u : Euclidean n → ℂ))
    (hdiag : ∀ z ξ, c z z ξ = principalSymbol η χg z ξ)
    (hi : Integrable (Pseudodifferential.sourceAmplitudeTransform c u x))
    (hid : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.diagonalAmplitude c β) u x))
    (hir : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.diagonalRemainderAmplitude b c β) u x))
    (hiB : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.fullTaylorCoefficient c β) u x)) :
    Pseudodifferential.fullAmplitudeOperator c u x -
      Pseudodifferential.sourceIndependentOperator (principalSymbol η χg) u x =
        Pseudodifferential.fullAmplitudeOperator
          (Pseudodifferential.diagonalRemainderAmplitude b c β) u x := by
  rw [Pseudodifferential.fullAmplitudeOperator_eq_diagonal_add_remainder b c β u x
    hc hβ hβc u.continuous huc hi hid hir hiB, diagonalAmplitude_inner_input c β u hβu]
  simp_rw [hdiag]
  exact add_sub_cancel_left _ _

end JanetCartan.FourierIntegral.CoordinateInverse
