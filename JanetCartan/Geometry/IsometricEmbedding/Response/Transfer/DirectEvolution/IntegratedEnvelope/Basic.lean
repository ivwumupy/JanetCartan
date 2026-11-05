module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Measurability
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration

/-!
# The actual integrated annular envelope

The envelope is the datum-wise integral of the SAME annular elapsed operators.
Carrier multiplication commutes with this integral as a linear isometry. Thus
the definition is exactly the original `elapsedGraphIntegral`, with its original
beta multiplied by the stated annular cutoff; neither physical mask is moved.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral AnnularSobolev
open JanetCartan.ResponseTransfer.Complement
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d r

/-- The annular part of the elapsed-time envelope, with both physical masks,
beta and the fixed carrier retained (`app:ch_response:eq:direct-envelope-profile`). -/
def annularEnvelopeIntegral (Δ : ℝ) (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) : H :=
  ∫ t in Icc 0 Δ, annularEnvelopeOperator Ψ a χout χsource β π t lam φ hφ u

/-- The datum-wise integral of the literal annular adjoints. The bounded
integral constructor identifies this with its Hilbert adjoint; no amplitude
factor is reordered (`app:ch_response:eq:direct-envelope-profile`). -/
def annularEnvelopeAdjointIntegral (Δ : ℝ) (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) : H :=
  ∫ t in Icc 0 Δ, (annularEnvelopeOperator Ψ a χout χsource β π t lam φ hφ).adjoint u

/-- The annular multiplier stays next to the original beta in the SAME
elapsed amplitude. No mask is commuted through the graph.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem annularElapsedAmplitude_eq_elapsedAmplitude (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (t lam : ℝ) :
    annularElapsedAmplitude a χout χsource β π t lam =
      elapsedAmplitude a χout χsource (fun ξ ↦ π (lam⁻¹ • ξ) * β ξ) t := by
  funext x y ξ
  simp only [annularElapsedAmplitude, frequencyCutFullAmplitude, elapsedAmplitude, smul_smul]
  congr 1
  ring

/-- Exact equality with carrier conjugation of the original physical
`elapsedGraphIntegral`, not a fixed-transverse retarded integral. The identity
holds for the actual Bochner integrals, including their integrability convention.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem annularEnvelopeIntegral_eq_elapsedGraphIntegral
    (Δ : ℝ) (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    annularEnvelopeIntegral Δ Ψ a χout χsource β π lam φ hφ u =
      carrierMultiplication (-lam) φ hφ
        (elapsedGraphIntegral Δ Ψ a χout χsource (fun ξ ↦ π (lam⁻¹ • ξ) * β ξ)
          (carrierMultiplication lam φ hφ u)) := by
  simp only [annularEnvelopeIntegral, annularEnvelopeOperator, demodulatedL2Operator,
    ContinuousLinearMap.comp_apply, annularElapsedAmplitude_eq_elapsedAmplitude]
  exact (carrierMultiplication (-lam) φ hφ).integral_comp_comm'
    (AddMonoidHomClass.isometry_of_norm _
      (norm_carrierMultiplication_apply (-lam) φ hφ)).antilipschitzWith _

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope
