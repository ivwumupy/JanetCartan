module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Literal joint phase and transfer coefficient for elapsed graphs

The fixed-elapsed-time calculation in `paper-v2.tex`,
`app:ch_response:lem:energy-carrier-jets`, used to prove the original
`paper.tex`, `app:ch_response:eq:direct-envelope-profile`.
The integration variables are the source position and normalized covector
together. The output position and carrier parameters are differentiated at
fixed elapsed time, frequency and operator. These definitions do not use the
fixed-transverse retarded kernels.

The critical point and the inverse gap must be supplied by the same-primary-phase
matching and the small-time two-time Hamilton geometry. No transfer estimate or
integration-by-parts identity is included in the input data.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.DirectEvolution

open MeasureTheory

variable {n : ℕ} {P E : Type*}

/-- The joint integration variable `w = (z, θ)` in the stationary calculation
preceding `new:eq:carrier-ibp`. The Hilbert product fixes the meaning of the
gradient and inverse transpose, without changing either physical coordinate. -/
abbrev CarrierVariables (n : ℕ) := WithLp 2 (Euclidean n × Euclidean n)

/-- The normalized demodulated phase at fixed elapsed time, from
`app:ch_response:lem:energy-carrier-jets`. In the direct application `Θ` is
literally `EvolutionIntegral.elapsedPhase Ψ r`. -/
def carrierPhase (Θ : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → P → ℝ) (q : Euclidean n × P)
    (w : CarrierVariables n) : ℝ :=
  Θ q.1 w.snd - inner ℝ w.fst w.snd + φ w.fst q.2 - φ q.1 q.2

/-- Specialization to the published elapsed-time phase, retaining the original
carrier on both physical positions (`new:eq:carrier-ibp`). -/
def elapsedCarrierPhase {d : ℕ}
    (Ψ : RegularSector.Characteristic.EvolutionIntegral.TwoTimePhase d)
    (r : ℝ) (φ : Euclidean (d + 1) → P → ℝ) :
    (Euclidean (d + 1) × P) → CarrierVariables (d + 1) → ℝ :=
  carrierPhase (RegularSector.Characteristic.EvolutionIntegral.elapsedPhase Ψ r) φ

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One output/parameter derivative, at fixed integration variable, in
`new:eq:carrier-ibp`. The direction may have both output and parameter parts. -/
def externalDerivative (f : E → CarrierVariables n → ℝ) (e q : E)
    (w : CarrierVariables n) : ℝ :=
  fderiv ℝ (fun p ↦ f p w) q e

/-- The literal segment-averaged `w`-Hessian from the stationary calculation
preceding `new:eq:carrier-ibp`. The entire segment must remain in the same
convex supported box as the critical point. -/
def averagedPhaseHessian (f : E → CarrierVariables n → ℝ)
    (w₀ : E → CarrierVariables n) (q : E) (w : CarrierVariables n) :
    CarrierVariables n →L[ℝ] CarrierVariables n :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient (f q)) (w₀ q + t • (w - w₀ q))

/-- The literal average of `∇w ∂e f` from the stationary calculation preceding
`new:eq:carrier-ibp`. Derivatives of the moving critical point are not dropped:
they enter subsequent derivatives of this complete function. -/
def averagedExternalGradient (f : E → CarrierVariables n → ℝ)
    (w₀ : E → CarrierVariables n) (e q : E) (w : CarrierVariables n) :
    CarrierVariables n :=
  ∫ t in (0 : ℝ)..1,
    gradient (externalDerivative f e q) (w₀ q + t • (w - w₀ q))

/-- The actual coefficient `A_e = H̄⁻ᵀ ∫ ∇w ∂e f` in `new:eq:carrier-ibp`.
Its identity and bounds require invertibility of this same averaged Hessian;
the definition contains no frequency or assumed transferred amplitude. -/
def transferCoefficient (f : E → CarrierVariables n → ℝ)
    (w₀ : E → CarrierVariables n) (e q : E) (w : CarrierVariables n) :
    CarrierVariables n :=
  (Ring.inverse (averagedPhaseHessian f w₀ q w)).adjoint
    (averagedExternalGradient f w₀ e q w)

end JanetCartan.ResponseTransfer.DirectEvolution
