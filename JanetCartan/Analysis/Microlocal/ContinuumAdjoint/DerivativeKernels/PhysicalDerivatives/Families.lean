module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.Basic

/-!
# Partial inverse transforms of the actual derivative words

For `app:ch_background:prop:bg-adjoint`, construct the finite family from the
actual words, using only their L² membership on the original carrier measure.
Plancherel identifies its norm sum exactly. `PhysicalDerivatives.AllOrders`
proves positive-order distributional compatibility using the one-step initial
and carrier Fourier transfer theorems. This leaf constructs the classes and
proves the order-zero case independently of those transfer theorems.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential

variable {n s : ℕ}

/-- The actual partial inverse of each actual derivative word for
`app:ch_background:prop:bg-adjoint`. L² membership is the primitive input to
be supplied by the finite expansion and conic L² estimates. -/
def partialInverseDerivativeFamily (s : ℕ) (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    CarrierL2DerivativeFamily n s :=
  fun w ↦ partialUnitaryInverse n
    ((hL2 (physicalDerivativeWord w) (physicalDerivativeWord_length_le w)).toLp
      (applyInitialCarrierDerivativeList (physicalDerivativeWord w) f))

/-- The empty entry is exactly the partial inverse of the original function,
for `app:ch_background:prop:bg-adjoint`. -/
theorem partialInverseDerivativeFamily_empty (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    partialInverseDerivativeFamily s f hL2 (.empty (3 + (n - 1)) s) =
      partialUnitaryInverse n ((hL2 [] (Nat.zero_le s)).toLp f) := by
  simp only [partialInverseDerivativeFamily, physicalDerivativeWord_empty,
    applyInitialCarrierDerivativeList]

/-- L² membership of words through order `s+1` gives membership through `s`
after one coordinate derivative. This is the induction input for the physical
transfer in `app:ch_background:prop:bg-adjoint`. -/
theorem memLp_derivativeWords_coordinate (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s + 1 →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n))
    (i : Fin (3 + (n - 1))) (ds : List (InitialCarrierDerivative n)) (hs : ds.length ≤ s) :
    MemLp (applyInitialCarrierDerivativeList ds
      (applyInitialCarrierDerivative (physicalCoordinateDerivativeLetter i) f))
      2 (carrierMeasure n) := by
  simpa only [applyInitialCarrierDerivativeList_append, applyInitialCarrierDerivativeList] using
    hL2 (ds ++ [physicalCoordinateDerivativeLetter i])
      (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hs 1)

/-- The actual partial inverse classes follow the same branch recursion as
`HasCarrierL2Derivatives`. No distributional compatibility is assumed or
asserted here (`app:ch_background:prop:bg-adjoint`). -/
theorem partialInverseDerivativeFamily_some (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s + 1 →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n))
    (i : Fin (3 + (n - 1))) (w : CarrierDerivativeIndex n s) :
    partialInverseDerivativeFamily (s + 1) f hL2 (some (i, w)) =
      partialInverseDerivativeFamily s
        (applyInitialCarrierDerivative (physicalCoordinateDerivativeLetter i) f)
        (memLp_derivativeWords_coordinate f hL2 i) w := by
  simp only [partialInverseDerivativeFamily, apply_physicalDerivativeWord_some]

/-- Each family entry has precisely the L² norm of its Fourier-side word,
with the original carrier measure and radian normalization
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_partialInverseDerivativeFamily (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n))
    (w : CarrierDerivativeIndex n s) :
    ‖partialInverseDerivativeFamily s f hL2 w‖ =
      (eLpNorm (applyInitialCarrierDerivativeList (physicalDerivativeWord w) f)
        2 (carrierMeasure n)).toReal := by
  rw [partialInverseDerivativeFamily, partialUnitaryInverse_norm, Lp.norm_toLp]

/-- Plancherel identifies the complete finite sum required by the physical
Sobolev estimate in `app:ch_background:prop:bg-adjoint`. No frequency cutoff or
replacement carrier measure occurs. -/
theorem carrierL2DerivativeNormSum_partialInverseDerivativeFamily
    (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    carrierL2DerivativeNormSum (partialInverseDerivativeFamily s f hL2) =
      ∑ w : CarrierDerivativeIndex n s,
        (eLpNorm (applyInitialCarrierDerivativeList (physicalDerivativeWord w) f)
          2 (carrierMeasure n)).toReal := by
  simp only [carrierL2DerivativeNormSum, norm_partialInverseDerivativeFamily]

/-- The order-zero construction already satisfies the physical derivative
predicate in `app:ch_background:prop:bg-adjoint`. Positive orders additionally
need distributional transfer through the partial inverse transform. -/
theorem hasCarrierL2Derivatives_partialInverse_zero (f : CarrierVariable n → ℂ)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ 0 →
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n)) :
    HasCarrierL2Derivatives 0
      (partialUnitaryInverse n ((hL2 [] (Nat.zero_le 0)).toLp f))
      (partialInverseDerivativeFamily 0 f hL2) := by
  apply (hasCarrierL2Derivatives_zero_iff _ _).mpr
  exact partialInverseDerivativeFamily_empty f hL2

/-- The raw physical estimate at order zero, as the base case for
`app:ch_background:prop:bg-adjoint`. -/
theorem physicalSobolevNorm_partialInverse_zero_le (f : CarrierVariable n → ℂ)
    (hf : MemLp f 2 (carrierMeasure n)) :
    physicalSobolevNorm 0 (partialUnitaryInverse n (hf.toLp f)) ≤
      (eLpNorm f 2 (carrierMeasure n)).toReal := by
  simp

end JanetCartan.ContinuumAdjoint.DerivativeKernels
