module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Kernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Physical-frequency normalization of the modified normal

The carrier in `app:ch_background:eq:bg-T` has no Fourier prefactor. Its full
normal therefore acquires `(2π)^n` when written in the cycles-per-unit convention
of the checked PDO estimate. Only the normal frequency is changed; the carrier
input measure `dz dη` is not replaced.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open NormalComparison

variable {n : ℕ}

/-- Exact conversion of the physical-frequency kernel to the PDO convention,
including its dimensional factor (`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedNormal_physical_eq_cycles (b : Euclidean n → ℂ) (w : Euclidean n) :
    (∫ k, oscillatoryFactor 1 (inner ℝ w k) * b k) =
      ∫ ξ, Complex.exp ((2 * Real.pi * inner ℝ w ξ : ℝ) * Complex.I) *
        (((2 * Real.pi) ^ n : ℂ) * b ((2 * Real.pi) • ξ)) := by
  let f : Euclidean n → ℂ := fun k ↦ oscillatoryFactor 1 (inner ℝ w k) * b k
  have hphase (ξ : Euclidean n) :
      oscillatoryFactor 1 (inner ℝ w ((2 * Real.pi) • ξ)) =
        Complex.exp ((2 * Real.pi * inner ℝ w ξ : ℝ) * Complex.I) := by
    simp only [oscillatoryFactor, inner_smul_right, one_mul]
    congr 1
    push_cast
    ring
  have hi (ξ : Euclidean n) :
      Complex.exp ((2 * Real.pi * inner ℝ w ξ : ℝ) * Complex.I) *
        (((2 * Real.pi) ^ n : ℂ) * b ((2 * Real.pi) • ξ)) =
          (2 * Real.pi) ^ n • f ((2 * Real.pi) • ξ) := by
    rw [show f ((2 * Real.pi) • ξ) =
      oscillatoryFactor 1 (inner ℝ w ((2 * Real.pi) • ξ)) * b ((2 * Real.pi) • ξ) from rfl,
      hphase, Complex.real_smul]
    push_cast
    ring
  simp_rw [hi]
  rw [integral_smul, Measure.integral_comp_smul_of_nonneg volume f (2 * Real.pi)
    (hR := by positivity), finrank_euclideanSpace_fin, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero n (by positivity : (2 * Real.pi : ℝ) ≠ 0)), one_smul]

end JanetCartan.ContinuumAdjoint.DerivativeKernels
