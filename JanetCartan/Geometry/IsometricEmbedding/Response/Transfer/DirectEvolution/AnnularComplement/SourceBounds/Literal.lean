module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.ElapsedIdentity

/-!
# Literal vector source kernels of the annular complement

These are the inner source integrals in `elapsedGraph_annularComplement_kernel`
and `adjointElapsedGraph_annularComplement_kernel`, including the physical
Fourier constant. The full amplitude is specialized to `elapsedAmplitude`;
both physical masks, beta, and the normalized selector stay in their original
positions. The output is in the existing complex Euclidean space used by the
vector Sobolev calculus. Source: `app:ch_response:lem:energy-carrier-jets`.

The physical and demodulated families are different literal functions. Their
order-zero norms agree, but differentiating the latter must retain every
derivative of its output carrier.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The forward vector source amplitude of the unchanged full graph,
including its normalized annular complement and original envelope. -/
def forwardAnnularSourceAmplitude (A : FullAmplitude n r) (π : E → ℂ)
    (lam : ℝ) (a : E → F) (x ξ z : E) : F :=
  WithLp.toLp 2 ((annularComplementAmplitude π lam A x z ξ).mulVec (a z).ofLp)

/-- The literal adjoint source amplitude, with exchanged physical positions
and conjugate transpose of the complete original amplitude. -/
def adjointAnnularSourceAmplitude (A : FullAmplitude n r) (π : E → ℂ)
    (lam : ℝ) (a : E → F) (x ξ z : E) : F :=
  WithLp.toLp 2 ((annularComplementAmplitude π lam A z x ξ).conjTranspose.mulVec
    (a z).ofLp)

/-- The normalized physical forward source kernel. Consumed by the annular
frequency-integral/Sobolev deduction in `app:ch_response:lem:energy-carrier-jets`. -/
def forwardAnnularSourceKernel (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) : F :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
    phaseOscillation (forwardCarrierSourcePhase Θ φ lam x ξ) z •
      forwardAnnularSourceAmplitude A π lam a x ξ z

/-- The normalized physical source kernel for the literal adjoint. -/
def adjointAnnularSourceKernel (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) : F :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
    phaseOscillation (adjointCarrierSourcePhase Θ φ lam x ξ) z •
      adjointAnnularSourceAmplitude A π lam a x ξ z

/-- The actual forward demodulator is part of the function being
differentiated; it is not frozen under parameter or output differentiation. -/
def demodulatedForwardAnnularSourceKernel (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) : F :=
  carrier (-lam) φ x • forwardAnnularSourceKernel Θ A π φ lam a x ξ

/-- The same output demodulator for the literal adjoint source integral. -/
def demodulatedAdjointAnnularSourceKernel (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) : F :=
  carrier (-lam) φ x • adjointAnnularSourceKernel Θ A π φ lam a x ξ

/-- The forward definition is exactly the original inner integral, with the
canonical vector norm bridge outside the integral. No integrability premise is
needed for this continuous linear equivalence. -/
theorem forwardAnnularSourceKernel_eq_literal
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    forwardAnnularSourceKernel Θ A π φ lam a x ξ =
      WithLp.toLp 2 (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        phaseOscillation (forwardCarrierSourcePhase Θ φ lam x ξ) z •
          (annularComplementAmplitude π lam A x z ξ).mulVec (a z).ofLp) := by
  unfold forwardAnnularSourceKernel forwardAnnularSourceAmplitude
  rw [WithLp.toLp_smul]
  congr 1
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => ℂ)).symm.integral_comp_comm _

/-- Exact vector bridge for the reversed source kernel; the matrix remains
conjugate-transposed in the original positions. -/
theorem adjointAnnularSourceKernel_eq_literal
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    adjointAnnularSourceKernel Θ A π φ lam a x ξ =
      WithLp.toLp 2 (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        phaseOscillation (adjointCarrierSourcePhase Θ φ lam x ξ) z •
          (annularComplementAmplitude π lam A z x ξ).conjTranspose.mulVec
            (a z).ofLp) := by
  unfold adjointAnnularSourceKernel adjointAnnularSourceAmplitude
  rw [WithLp.toLp_smul]
  congr 1
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => ℂ)).symm.integral_comp_comm _

/-- Frequency integration recovers the SAME forward graph on its original
carrier source. The statement uses the total Bochner integrals, so it also
identifies any subsequently proved absolutely integrable realization. -/
theorem integral_forwardAnnularSourceKernel
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x : E) :
    (∫ ξ, forwardAnnularSourceKernel Θ A π φ lam a x ξ) =
      WithLp.toLp 2 (graphOperator Θ (annularComplementAmplitude π lam A)
        (fun z => carrier lam φ z • (a z).ofLp) x) := by
  simp_rw [forwardAnnularSourceKernel_eq_literal]
  rw [show (∫ ξ : E, WithLp.toLp 2 (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
      phaseOscillation (forwardCarrierSourcePhase Θ φ lam x ξ) z •
        (annularComplementAmplitude π lam A x z ξ).mulVec (a z).ofLp)) =
      WithLp.toLp 2 (∫ ξ : E, ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        phaseOscillation (forwardCarrierSourcePhase Θ φ lam x ξ) z •
          (annularComplementAmplitude π lam A x z ξ).mulVec (a z).ofLp) from
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => ℂ)).symm.integral_comp_comm _]
  congr 1
  rw [integral_smul]
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [phaseOscillation_forwardCarrierSourcePhase, Matrix.mulVec_smul, smul_smul]

/-- The corresponding exact recovery of the literal adjoint graph. This
preserves the conjugate transpose and the order of both physical positions. -/
theorem integral_adjointAnnularSourceKernel
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x : E) :
    (∫ ξ, adjointAnnularSourceKernel Θ A π φ lam a x ξ) =
      WithLp.toLp 2 (reverseGraphOperator Θ
        (fun z x ξ => (annularComplementAmplitude π lam A z x ξ).conjTranspose)
        (fun z => carrier lam φ z • (a z).ofLp) x) := by
  simp_rw [adjointAnnularSourceKernel_eq_literal]
  rw [show (∫ ξ : E, WithLp.toLp 2 (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
      phaseOscillation (adjointCarrierSourcePhase Θ φ lam x ξ) z •
        (annularComplementAmplitude π lam A z x ξ).conjTranspose.mulVec (a z).ofLp)) =
      WithLp.toLp 2 (∫ ξ : E, ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        phaseOscillation (adjointCarrierSourcePhase Θ φ lam x ξ) z •
          (annularComplementAmplitude π lam A z x ξ).conjTranspose.mulVec (a z).ofLp) from
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => ℂ)).symm.integral_comp_comm _]
  congr 1
  rw [integral_smul]
  unfold reverseGraphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [phaseOscillation_adjointCarrierSourcePhase, Matrix.mulVec_smul, smul_smul]

/-- Unfolding the actual elapsed amplitude displays both masks and beta in
the physical forward kernel of `app:ch_response:lem:energy-carrier-jets`. -/
theorem forwardAnnularSourceKernel_elapsed {d : ℕ}
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : Euclidean (d + 1) → F) (x ξ : Euclidean (d + 1)) :
    forwardAnnularSourceKernel (elapsedPhase Ψ t)
      (elapsedAmplitude b χout χsource β t) π φ lam a x ξ =
      WithLp.toLp 2 (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ z,
        phaseOscillation (forwardCarrierSourcePhase (elapsedPhase Ψ t) φ lam x ξ) z •
          (((1 - π (lam⁻¹ • ξ)) * (χout x * χsource z * β ξ)) •
            b (x 0) (x 0 - t) (spatialPart x) (spatialPart ξ)).mulVec (a z).ofLp) := by
  rw [forwardAnnularSourceKernel_eq_literal]
  simp only [annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude, smul_smul]

/-- The actual elapsed adjoint kernel retains conjugation of the masks and
beta as well as the transport matrix. -/
theorem adjointAnnularSourceKernel_elapsed {d : ℕ}
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : Euclidean (d + 1) → F) (x ξ : Euclidean (d + 1)) :
    adjointAnnularSourceKernel (elapsedPhase Ψ t)
      (elapsedAmplitude b χout χsource β t) π φ lam a x ξ =
      WithLp.toLp 2 (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ z,
        phaseOscillation (adjointCarrierSourcePhase (elapsedPhase Ψ t) φ lam x ξ) z •
          (star ((1 - π (lam⁻¹ • ξ)) * (χout z * χsource x * β ξ)) •
            (b (z 0) (z 0 - t) (spatialPart z) (spatialPart ξ)).conjTranspose).mulVec
              (a z).ofLp) := by
  rw [adjointAnnularSourceKernel_eq_literal]
  simp only [annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude,
    smul_smul, Matrix.conjTranspose_smul]

/-- Demodulation preserves only the order-zero kernel norm. This identity
does not discard its derivatives at positive external orders. -/
theorem norm_demodulatedForwardAnnularSourceKernel
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    ‖demodulatedForwardAnnularSourceKernel Θ A π φ lam a x ξ‖ =
      ‖forwardAnnularSourceKernel Θ A π φ lam a x ξ‖ := by
  simp [demodulatedForwardAnnularSourceKernel, norm_smul, carrier, Complex.norm_exp]

/-- Order-zero norm preservation for the literal adjoint demodulator. -/
theorem norm_demodulatedAdjointAnnularSourceKernel
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    ‖demodulatedAdjointAnnularSourceKernel Θ A π φ lam a x ξ‖ =
      ‖adjointAnnularSourceKernel Θ A π φ lam a x ξ‖ := by
  simp [demodulatedAdjointAnnularSourceKernel, norm_smul, carrier, Complex.norm_exp]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
