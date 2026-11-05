module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CompactKernels

/-!
# Conditional Cartesian Sobolev extensions of the graph shell action

The exact pointwise hypotheses below are bounds on classical output jets of
the concrete cutoff matrix kernel entries. Their producer is
`jc-graph-factor-kernel-estimates`, followed by the fixed cutoff product rule
and coordinate transfer in the parent factor-localization assembly. They assume
neither convergence nor an operator estimate. The existing retarded kernel API
constructs the extensions and identifies every completed jet. The fixed matrix
factor is retained on Hilbert direct sums.

`SummedSupport` supplies the independent physical support deduction required to
remove the fixed output cutoff in the summed test action. The parent must supply
a cutoff equal to one there and instantiate the jet estimates for its own
bounded-frequency pieces and all source shoulders (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral Retarded.KernelSobolev AmplitudeBound
open JanetCartan.RetardedSobolev.Spaces
variable {n r d m : ℕ}
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Use one primitive input/amplitude carrier for every pair of frequency
shells. This is a choice of common compact sets, not an additional support
premise (`app:ch_regular:eq:chain-tail`). -/
def RegularizedCarriers.commonBases
    {A : FullAmplitude n r} {mi : LocalizerSymbol n}
    {χA χo : ℕ → Euclidean n → ℝ}
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k)) (j k : ℕ) :
    RegularizedCarriers A mi (χA j) (χo k) :=
  { c 0 0 with
    compact_graphCutoff := (c j k).compact_graphCutoff
    compact_outputCutoff := (c j k).compact_outputCutoff }

section Extension
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
  (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
  (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ) (ψ : Euclidean n → ℝ)
  (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
  (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
  (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
    A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
  (hg : ∀ j, ContDiff ℝ ∞ (χA j)) (hc : ∀ k, ContDiff ℝ ∞ (χo k))
  (hg0 : ∀ j, (0 : Euclidean n) ∉ tsupport (χA j))
  (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
  (μ ν : Measure ((Fin d → ℝ) × ℝ))
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

local notation "K" => (fun (p : ℕ × ℕ) (a b : Fin r) => supportedJointKernelEntry J
  backward S A mi mo (χA (Prod.fst p)) (χo (Prod.snd p)) ψ (RegularizedCarriers.commonBases c (Prod.fst p) (Prod.snd p))
  hS hA hi ho (hg (Prod.fst p)) (hc (Prod.snd p)) (hg0 (Prod.fst p)) hψ hsψ a b)
local notation "sI" => (fun y : (Fin d → ℝ) × ℝ => J (Prod.snd y, Prod.fst y)) ⁻¹' RegularizedCarriers.inputBase (c 0 0)
local notation "sO" => J ⁻¹' tsupport ψ

/-- A concrete matrix channel extends uniquely to the Cartesian Sobolev
completion and every completed jet is the integral of the summed actual jets.
The pointwise bound is the precise remaining estimate-producer obligation,
including fixed cutoff derivatives (`app:ch_regular:eq:chain-tail`). -/
theorem exists_jointKernelEntry_shell_extension
    (C : ℕ × ℕ → ℝ) (hC : ∀ p, 0 ≤ C p) (hs : Summable C) (a b : Fin r)
    (hb : ∀ j k (i : JetIndex d m) p (y : (Fin d → ℝ) × ℝ),
      ‖jet i (fun x => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo
        (χA j) (χo k) (J x) (J (y.2, y.1)) a b) p‖ ≤ C (j,k)) :
    ∃ T : Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖T‖ ≤ (∑' p, C p) * compactSupportFactor μ ν sI (Prod.swap ⁻¹' sO) ∧
      (∀ f, HasSum (fun p => ofTest m ν (kernelIntegralLinear (K p a b) μ f))
        (T (ofTest 0 μ f))) ∧
      (∀ (f : Test d) (i : JetIndex d m), MemLp
        (fun p => ∫ y, (∑' j, kernelJet (K j a b) i p y) * f.val (y.2, y.1) ∂μ) 2 ν) ∧
      (∀ f (i : JetIndex d m), (T (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p => ∫ y, (∑' j, kernelJet (K j a b) i p y) * f.val (y.2, y.1) ∂μ) ∧
      ∀ T' : Sobolev 0 μ →L[ℂ] Sobolev m ν,
        (∀ f, HasSum (fun p => ofTest m ν (kernelIntegralLinear (K p a b) μ f))
          (T' (ofTest 0 μ f))) → T' = T := by
  obtain ⟨T, hnorm, htest, hmem, hjet⟩ := exists_commonSupport_shell_extensions
    (fun p => K p a b) μ ν sI sO (fun _ => rfl) (fun _ => rfl) C hC hs
    (fun p => hb p.1 p.2)
  exact ⟨T, hnorm, htest, hmem, hjet,
    fun T' htest' => shell_extension_unique (fun p => K p a b) μ ν T' T htest' htest⟩

/-- All matrix channels assemble on the existing Hilbert direct sums, retaining
the explicit fixed factor `r*r` in the norm. Each channel is identified with
its summed integral jets; matrix application is the literal finite channel sum
by `AmplitudeBound.matrixOperator_apply` (`app:ch_regular:eq:chain-tail`). -/
theorem exists_jointKernel_matrix_shell_extension
    (C : ℕ × ℕ → ℝ) (hC : ∀ p, 0 ≤ C p) (hs : Summable C)
    (hb : ∀ j k (a b : Fin r) (i : JetIndex d m) p (y : (Fin d → ℝ) × ℝ),
      ‖jet i (fun x => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo
        (χA j) (χo k) (J x) (J (y.2, y.1)) a b) p‖ ≤ C (j,k)) :
    ∃ T : Fin r → Fin r → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖matrixOperator T‖ ≤ (r : ℝ) * r *
        ((∑' p, C p) * compactSupportFactor μ ν sI (Prod.swap ⁻¹' sO)) ∧
      (∀ a b f, HasSum (fun p => ofTest m ν (kernelIntegralLinear (K p a b) μ f))
        (T a b (ofTest 0 μ f))) ∧
      ∀ a b f (i : JetIndex d m), (T a b (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p => ∫ y, (∑' j, kernelJet (K j a b) i p y) * f.val (y.2, y.1) ∂μ := by
  choose T hn ht _ hj _ using fun a b => exists_jointKernelEntry_shell_extension
    J backward S A mi mo χA χo ψ c hS hA hi ho hg hc hg0 hψ hsψ μ ν
    C hC hs a b (fun j k => hb j k a b)
  exact ⟨T, by simpa using norm_matrixOperator_le_of_entry_bound T _ hn, ht, hj⟩

end Extension
end JanetCartan.FiniteChain.Graph.KernelLimits
