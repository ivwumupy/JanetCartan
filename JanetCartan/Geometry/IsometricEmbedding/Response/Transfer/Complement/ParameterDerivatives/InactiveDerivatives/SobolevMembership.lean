module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.Regularity
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Tests
/-!
# Sobolev membership of the actual normalized source jets

Use the proved smooth compact support on the same Euclidean L² space.
This discharges membership, independently of the quantitative profile still
needed by `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential FourierIntegral
variable {p d r : ℕ}
local notation "E" => Euclidean d
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Every real Sobolev membership of the normalized actual derivative follows
from its proved smooth compact support. No differentiated-envelope membership
is an assumption (`app:ch_response:thm:response-literal-transfer`). The
quantitative uniform profile remains a separate finite Leibniz estimate. -/
theorem memVectorFourierSobolev_parameterCarrierJet_of_original
    {V : Set P} {U K : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) (s : ℝ) :
    MemVectorFourierSobolev s
      ((memLp_parameterCarrierJet_of_original hV hU hK hKU ρ hφ hf hs k v hc).toLp
        (parameterCarrierJet ρ φ f k v c)) := by
  let u : graphTestSpace d r := ⟨parameterCarrierJet ρ φ f k v c,
    contDiff_parameterCarrierJet_of_original hV hU hK hKU ρ hφ hf hs k v hc,
    hasCompactSupport_parameterCarrierJet_of_original hV hK ρ φ f hs k v hc⟩
  exact graphTest_memVectorFourierSobolev s u

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
