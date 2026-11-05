module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport.PhaseCalculus

/-!
# Literal conjugated carrier kernel

The starting integral of `app:ch_background:prop:bg-adjoint`, on the original
torus measurement space and with the original Lebesgue carrier variables. The
identities are pointwise; they do not assert boundedness of the integral.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow NormalComparison

variable {n N : ℕ}

/-- Scalar contraction of the full measured amplitude with the complex datum,
including extension by zero outside the output chart
(`app:ch_background:prop:bg-adjoint`). -/
def measuredAdjointAmplitude (d : CarrierData n N)
    (v : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) (x : Torus n) : ℂ :=
  d.outputChart.indicator
    (fun y ↦ inner ℂ (euclideanComplexInclusion (carrierAmplitude d y u)) (v y)) x

/-- The literal adjoint conjugates the phase but not the output datum. This fixes
the sign in `app:ch_background:eq:bg-derivative-trade`. -/
theorem inner_carrierKernel_eq (d : CarrierData n N)
    (v : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) (x : Torus n) :
    inner ℂ (carrierKernel d x u) (v x) =
      oscillatoryFactor (-1) (carrierPhase d x u) * measuredAdjointAmplitude d v u x := by
  classical
  by_cases hx : x ∈ d.outputChart
  · simp [carrierKernel, measuredAdjointAmplitude, hx, inner_smul_left,
      oscillatoryFactor, ← Complex.exp_conj]
  · simp [carrierKernel, measuredAdjointAmplitude, hx]

/-- Exact conjugated-phase formula for the literal `carrierAdjointIntegral` in
`app:ch_background:prop:bg-adjoint`. The measurement integral stays on the torus;
transferring it to a Euclidean chart is a separate obligation. -/
theorem carrierAdjointIntegral_eq (d : CarrierData n N)
    (v : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) :
    carrierAdjointIntegral d v u =
      ∫ x, oscillatoryFactor (-1) (carrierPhase d x u) * measuredAdjointAmplitude d v u x := by
  unfold carrierAdjointIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (inner_carrierKernel_eq d v u)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
