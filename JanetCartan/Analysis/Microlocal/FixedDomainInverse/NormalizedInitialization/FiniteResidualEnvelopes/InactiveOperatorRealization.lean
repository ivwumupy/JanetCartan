module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.InactiveKernelSobolev
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.PdoReassembly

/-!
# The inactive kernel is the original forward graph

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
namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds ResponseTransfer
open ResponseTransfer.Complement ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.AnnularComplement
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- A zero amplitude has the zero canonical graph operator: its zero test
realization and density identify the actual choice definition. Consumer:
removing the zero selector in the inactive full-kernel estimate
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem full_graph_zero_amplitude (Θ : E → E → ℝ) :
    fullGraphOperator (r := r) Θ 0 = 0 := by
  apply fullGraphOperator_eq_of_realizes
  intro u
  have hzero : graphTestOutput Θ (0 : FullAmplitude (d+1) r) u = 0 := by
    funext x
    simp [graphTestOutput,graphOperator]
  rw [hzero]
  simpa only [zero_apply] using (Lp.coeFn_zero F 2 (volume : Measure E))

/-- Frequency selector zero kills the complete full amplitude, including
both original physical masks (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem full_graph_zero_frequency_cut (Θ : E → E → ℝ) (A : FullAmplitude (d+1) r)
    (lam : ℝ) :
    fullGraphOperator Θ (frequencyCutFullAmplitude (fun ξ : E ↦ (0 : E → ℂ) (lam⁻¹ • ξ)) A) = 0 := by
  have he : frequencyCutFullAmplitude (fun ξ : E ↦ (0 : E → ℂ) (lam⁻¹ • ξ)) A = 0 := by
    funext x y ξ
    simp only [frequencyCutFullAmplitude,Pi.zero_apply,zero_smul]
  rw [he,full_graph_zero_amplitude]

/-- The complete inactive kernel output is exactly the original forward
graph demodulated against the original source phase. This consumes the exact
strong-limit identity of `inactive_forward_elapsed_kernel_sobolev` and does
not posit a full-graph norm estimate (`new:eq:carrier-ibp`). -/
theorem inactive_kernel_eq_demodulated_forward_graph
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r) (χout χsource β : E → ℂ)
    (t lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (a : E → F) (u R : H) (hu : u =ᵐ[volume] a)
    (hR : ∃ w : H, w =ᵐ[volume] (fun x ↦ carrier lam φ x • a x) ∧
      R =ᵐ[volume] fun x ↦ carrier (-lam) φ x •
        ((annularGraphOrientation false (fullGraphOperator (elapsedPhase Ψ t)
            (elapsedAmplitude b χout χsource β t)) w -
          annularGraphOrientation false (fullGraphOperator (elapsedPhase Ψ t)
            (frequencyCutFullAmplitude (fun ξ : E ↦ (0 : E → ℂ) (lam⁻¹ • ξ))
              (elapsedAmplitude b χout χsource β t))) w) x)) :
    R = demodulatedL2Operator lam φ hφ (elapsedGraph Ψ b χout χsource β t) u := by
  have he := remainder_eq_demodulated_difference_of_ae
    (annularGraphOrientation false (fullGraphOperator (elapsedPhase Ψ t)
      (elapsedAmplitude b χout χsource β t)))
    (annularGraphOrientation false (fullGraphOperator (elapsedPhase Ψ t)
      (frequencyCutFullAmplitude (fun ξ : E ↦ (0 : E → ℂ) (lam⁻¹ • ξ))
        (elapsedAmplitude b χout χsource β t))))
    lam φ hφ a u R hu hR
  simpa only [annularGraphOrientation,Bool.false_eq_true,ite_false,
    full_graph_zero_frequency_cut,demodulatedL2Operator,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,sub_zero,elapsedGraph] using he

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
