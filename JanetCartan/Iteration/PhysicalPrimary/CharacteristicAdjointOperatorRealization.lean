module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointKernelSobolev
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.InactiveOperatorRealization
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.PdoReassembly

/-!
# The inactive kernel is the original literal adjoint graph

The inactive full-frequency construction uses selector zero. Its cut graph is
literally the zero operator, so the kernel realization identifies the SAME
uncut graph and original source, rather than a replacement complementary
operator. This is the algebraic bridge to elapsed integration and the selected
bounded solver action (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Filter Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds ResponseTransfer
open ResponseTransfer.Complement ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.AnnularComplement
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The complete inactive kernel output is exactly the original literal adjoint
graph demodulated against the original source phase. This consumes the exact
strong-limit identity of `inactive_adjoint_elapsed_kernel_sobolev` and does
not posit a full-graph norm estimate (`new:eq:carrier-ibp`). -/
theorem inactive_kernel_eq_demodulated_adjoint_graph
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r) (χout χsource β : E → ℂ)
    (t lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (a : E → F) (u R : H) (hu : u =ᵐ[volume] a)
    (hR : ∃ w : H, w =ᵐ[volume] (fun x ↦ carrier lam φ x • a x) ∧
      R =ᵐ[volume] fun x ↦ carrier (-lam) φ x •
        ((annularGraphOrientation true (fullGraphOperator (elapsedPhase Ψ t)
            (elapsedAmplitude b χout χsource β t)) w -
          annularGraphOrientation true (fullGraphOperator (elapsedPhase Ψ t)
            (frequencyCutFullAmplitude (fun ξ : E ↦ (0 : E → ℂ) (lam⁻¹ • ξ))
              (elapsedAmplitude b χout χsource β t))) w) x)) :
    R = demodulatedL2Operator lam φ hφ (elapsedGraph Ψ b χout χsource β t).adjoint u := by
  have he := remainder_eq_demodulated_difference_of_ae
    (annularGraphOrientation true (fullGraphOperator (elapsedPhase Ψ t)
      (elapsedAmplitude b χout χsource β t)))
    (annularGraphOrientation true (fullGraphOperator (elapsedPhase Ψ t)
      (frequencyCutFullAmplitude (fun ξ : E ↦ (0 : E → ℂ) (lam⁻¹ • ξ))
        (elapsedAmplitude b χout χsource β t))))
    lam φ hφ a u R hu hR
  simpa only [annularGraphOrientation,ite_true,
    full_graph_zero_frequency_cut,demodulatedL2Operator,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,sub_zero,elapsedGraph] using he

end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
