module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.Families
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.CarrierTransfer
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.InitialTransfer

/-!
# All-order physical derivatives of partial radian synthesis

For `app:ch_background:prop:bg-adjoint`, the actual Fourier-side derivative
words yield every physical mixed weak derivative before cutoffs. The one-step
initial and carrier transfer theorems discharge all distributional identities;
Plancherel and the shared physical Sobolev characterization give the finite
norm bound. The parent raw adjoint construction supplies joint smoothness and
L² membership of the actual words from the compact chart expansion and conic
L² estimates. No derivative family or modified-operator bound is an input.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential
variable {n s : ℕ}

/-- Every physical coordinate derivative is the partial inverse of its actual
Fourier-side letter, for `app:ch_background:prop:bg-adjoint`. This combines all
three carrier coordinates with all `n - 1` initial radian multipliers on the
original carrier measure, including the zero-dimensional transverse case. -/
theorem hasCarrierL2CoordinateDerivative_partialInverse_coordinate
    (i : Fin (3 + (n - 1))) {f : CarrierVariable n → ℂ}
    (hreg : ContDiff ℝ ∞ f) (h0 : MemLp f 2 (carrierMeasure n))
    (h1 : MemLp (applyInitialCarrierDerivative (physicalCoordinateDerivativeLetter i) f)
      2 (carrierMeasure n)) :
    HasCarrierL2CoordinateDerivative i (partialUnitaryInverse n (h0.toLp f))
      (partialUnitaryInverse n (h1.toLp
        (applyInitialCarrierDerivative (physicalCoordinateDerivativeLetter i) f))) := by
  revert h1
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> intro h1
  · simp only [physicalCoordinateDerivativeLetter_castAdd] at h1 ⊢
    exact hasCarrierL2CoordinateDerivative_partialInverse_carrier j hreg h0 h1
  · simp only [physicalCoordinateDerivativeLetter_natAdd] at h1 ⊢
    exact hasCarrierL2CoordinateDerivative_partialInverse_initial j f h0 h1

/-- The constructed partial inverse family consists of the actual mixed weak
derivatives at every finite order in `app:ch_background:prop:bg-adjoint`.
The induction preserves the ordered words; no commutation of letters is needed.
The primitive smoothness and word L² hypotheses are supplied by the parent
chart expansion and conic estimates. -/
theorem hasCarrierL2Derivatives_partialInverse (s : ℕ) (f : CarrierVariable n → ℂ)
    (hreg : ContDiff ℝ ∞ f)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    HasCarrierL2Derivatives s
      (partialUnitaryInverse n ((hL2 [] (Nat.zero_le s)).toLp f))
      (partialInverseDerivativeFamily s f hL2) := by
  induction s generalizing f with
  | zero => exact hasCarrierL2Derivatives_partialInverse_zero f hL2
  | succ s ih =>
    apply (hasCarrierL2Derivatives_succ_iff _ _).mpr
    refine ⟨partialInverseDerivativeFamily_empty f hL2, ?_⟩
    intro i
    simp only [partialInverseDerivativeFamily_some, partialInverseDerivativeFamily_empty]
    constructor
    · exact hasCarrierL2CoordinateDerivative_partialInverse_coordinate i hreg
        (hL2 [] (Nat.zero_le (s + 1)))
        (memLp_derivativeWords_coordinate f hL2 i [] (Nat.zero_le s))
    · exact ih _ (contDiff_applyInitialCarrierDerivative_joint hreg _) _

/-- Smoothness and L² membership of the actual words imply physical Sobolev
membership before cutoffs in `app:ch_background:prop:bg-adjoint`. -/
theorem memPhysicalSobolev_partialInverse (s : ℕ) (f : CarrierVariable n → ℂ)
    (hreg : ContDiff ℝ ∞ f)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    MemPhysicalSobolev s (partialUnitaryInverse n ((hL2 [] (Nat.zero_le s)).toLp f)) :=
  (hasCarrierL2Derivatives_partialInverse s f hreg hL2).memPhysicalSobolev

/-- The physical Sobolev norm is bounded by the finite sum of actual
Fourier-side word L² norms, with the shared explicit order constant, for
`app:ch_background:prop:bg-adjoint`. This is the Plancherel step consumed by the
raw adjoint estimate; the parent's conic estimates bound the summands. -/
theorem physicalSobolevNorm_partialInverse_le_derivativeWordSum
    (s : ℕ) (f : CarrierVariable n → ℂ) (hreg : ContDiff ℝ ∞ f)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    physicalSobolevNorm s (partialUnitaryInverse n ((hL2 [] (Nat.zero_le s)).toLp f)) ≤
      (4 * Real.pi) ^ s * ∑ w : CarrierDerivativeIndex n s,
        (eLpNorm (applyInitialCarrierDerivativeList (physicalDerivativeWord w) f)
          2 (carrierMeasure n)).toReal := by
  simpa only [carrierL2DerivativeNormSum_partialInverseDerivativeFamily] using
    (hasCarrierL2Derivatives_partialInverse s f hreg hL2).physicalSobolevNorm_le

end JanetCartan.ContinuumAdjoint.DerivativeKernels
