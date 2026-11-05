module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Differential
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact oscillation transfer at fixed elapsed time

The pointwise identity before `paper-v2.tex`, `new:eq:carrier-ibp`, and the
literal carrier removal in the original `app:ch_response:eq:direct-envelope-profile`.
The coefficient is the constructed inverse-transpose segment average.
Integration by parts and the regularized/strong operator identifications are
separate obligations; no integral estimate is asserted here.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E P : Type*}

/-- The normalized joint oscillation in `new:eq:carrier-ibp`, at the same
fixed frequency and elapsed time throughout parameter differentiation. -/
def oscillation (f : E → CarrierVariables n → ℝ) (ρ : ℝ) (q : E)
    (w : CarrierVariables n) : ℂ :=
  Complex.exp (Complex.I * ((ρ * f q w : ℝ) : ℂ))

/-- Literal equality with the original graph oscillation and the same carrier
on both positions. The scaling identity is supplied by degree-one homogeneity
of the actual elapsed phase on the annulus. This is a kernel identity only;
it does not identify different bounded realizations.
Source: `app:ch_response:lem:energy-carrier-jets`, frequency localization. -/
theorem demodulated_graphOscillation_eq
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (ρ : ℝ) (q : Euclidean n × P) (w : CarrierVariables n)
    (hΘ : Θ q.1 (ρ • w.snd) = ρ * Θ q.1 w.snd) :
    carrier (-ρ) (fun x ↦ φ x q.2) q.1 *
        FourierIntegral.graphOscillation Θ q.1 w.fst (ρ • w.snd) *
        carrier ρ (fun z ↦ φ z q.2) w.fst =
      oscillation (carrierPhase Θ φ) ρ q w := by
  simp only [carrier, FourierIntegral.graphOscillation, oscillation, carrierPhase,
    hΘ, inner_smul_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fderiv_exp_phase {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : X → ℝ} {x : X} (hg : DifferentiableAt ℝ g x) (ρ : ℝ) (v : X) :
    fderiv ℝ (fun y ↦ Complex.exp (Complex.I * ((ρ * g y : ℝ) : ℂ))) x v =
      Complex.exp (Complex.I * ((ρ * g x : ℝ) : ℂ)) *
        (Complex.I * (ρ : ℂ) * (fderiv ℝ g x v : ℂ)) := by
  have hd := (((Complex.ofRealCLM.hasFDerivAt.comp x
    (hg.hasFDerivAt.const_mul ρ)).const_mul Complex.I).cexp).fderiv
  have he := congrArg (fun L : X →L[ℝ] ℂ ↦ L v) hd
  simpa [Function.comp_def, mul_assoc] using he

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An output/parameter derivative of the actual oscillation is exactly its
integration-variable derivative along the constructed coefficient. There is
no frequency factor in the transfer direction, for either sign of `ρ`.
This proves the pointwise step of `new:eq:carrier-ibp` from primitive geometry,
without assuming a phase trade or an integration-by-parts identity. -/
theorem fderiv_oscillation_external_eq_integration
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {q : E} (hq : q ∈ U) (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : gradient (f q) (w₀ q) = 0)
    (hvalue : (fun p ↦ f p (w₀ p)) =ᶠ[𝓝 q] (fun _ ↦ 0))
    {w : CarrierVariables n} (h₀ : w₀ q ∈ D) (hw : w ∈ D)
    (hinv : IsUnit (averagedPhaseHessian f w₀ q w)) (ρ : ℝ) (e : E) :
    fderiv ℝ (fun p ↦ oscillation f ρ p w) q e =
      fderiv ℝ (oscillation f ρ q) w (transferCoefficient f w₀ e q w) := by
  have hj : ContDiffAt ℝ ∞ (Function.uncurry f) (q, w) :=
    hf.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hw⟩)
  have he : DifferentiableAt ℝ (fun p ↦ f p w) q :=
    (hj.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hw' : DifferentiableAt ℝ (f q) w :=
    (hj.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have htrade := externalDerivative_eq_inner_transferCoefficient hU hD hcD hf hq
    hw₀ hcritical hvalue h₀ hw hinv e
  rw [real_inner_comm] at htrade
  change externalDerivative f e q w =
    inner ℝ ((InnerProductSpace.toDual ℝ (CarrierVariables n)).symm (fderiv ℝ (f q) w))
      (transferCoefficient f w₀ e q w) at htrade
  rw [InnerProductSpace.toDual_symm_apply] at htrade
  unfold externalDerivative at htrade
  unfold oscillation
  rw [fderiv_exp_phase he, fderiv_exp_phase hw', htrade]

end JanetCartan.ResponseTransfer.DirectEvolution
