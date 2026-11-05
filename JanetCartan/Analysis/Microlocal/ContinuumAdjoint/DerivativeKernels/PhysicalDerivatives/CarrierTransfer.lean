module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.CarrierTransfer.WeakInput
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.CarrierTransfer.PartialCommutation

/-!
# Carrier derivatives for partial inverse Fourier transfer

For `app:ch_background:prop:bg-adjoint`, joint smoothness and the two primitive
L² bounds give the actual input weak derivative. The partial inverse Fourier
map preserves this identity in all three carrier coordinates, with the literal
carrier measure and exact radian normalization, before any physical cutoff.
This supplies the carrier step of the all-order physical derivative assembly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- Transfer each scalar or vector carrier derivative through the actual
partial radian inverse Fourier map, before physical cutoffs, for
`app:ch_background:prop:bg-adjoint`. Joint smoothness and the two stated L²
bounds supply the weak input identity and all test integrability; preservation
under the partial transform is proved by Fourier factorization and Fubini.
This is the carrier step used in the all-order physical derivative assembly. -/
theorem hasCarrierL2CoordinateDerivative_partialInverse_carrier
    (i : Fin 3) {f : CarrierVariable n → ℂ} (hreg : ContDiff ℝ ∞ f)
    (h0 : MemLp f 2 (carrierMeasure n))
    (h1 : MemLp (applyInitialCarrierDerivative (.carrier (physicalCarrierDirection i)) f)
      2 (carrierMeasure n)) :
    HasCarrierL2CoordinateDerivative (Fin.castAdd (n - 1) i)
      (partialUnitaryInverse n (h0.toLp f))
      (partialUnitaryInverse n
        (h1.toLp (applyInitialCarrierDerivative (.carrier (physicalCarrierDirection i)) f))) := by
  exact hasCarrierL2CoordinateDerivative_partialUnitaryInverse_of_carrierDerivative i _ _
    (hasCarrierL2CoordinateDerivative_toLp_carrier i hreg h0 h1)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
