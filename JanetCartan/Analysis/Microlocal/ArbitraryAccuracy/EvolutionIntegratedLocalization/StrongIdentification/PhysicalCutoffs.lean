module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.Summation

/-!
# The published physical cutoff sums have the elapsed shell limit

The primitive masks construct common carriers. This specializes the finite
identities and summation to `PhysicalShells.graphCutoff` (including its low
branch) and `PhysicalShells.outputCutoff` (including its zeroth piece).
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph RegularSector.Characteristic.EvolutionIntegral
open KernelLimits PhysicalShells
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The literal compositions with the published independent physical cutoff
sums converge to the summed `elapsedPhysicalShellKernel`. The original masks
produce the common base carriers; their order is unchanged in the adjoint.
The only quantitative hypothesis is the pointwise summable elapsed-shell
majorant, whose producers are `ShellSummation` and `UniformDecay`. This proves
the physical test limit needed to connect the shell construction to the L²
limit, not an assumed operator tail estimate (`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem tendsto_physicalElapsedShell_test_compositions
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (Ki Kη : Set E) (hKi : IsCompact Ki) (hKη : IsCompact Kη)
    (hiSupport : ∀ y η, (y, η) ∉ Ki ×ˢ Kη → mi (y, η) = 0)
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
      mi mo (graphCutoff j) (outputCutoff k) x y‖ ≤ C (j, k))
    (f : E → Fin q → ℂ) (hf : Continuous f) (hfi : Integrable f) (x : E) :
    Tendsto (fun s : Finset ℕ × Finset ℕ ↦ ∫ r in Icc 0 Δ,
      leftLocalizer ρ (fun p ↦ (∑ k ∈ s.2, outputCutoff k (ρ • p.2)) * (1 - mo p))
        ((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
          (fun u z ξ ↦ ((∑ j ∈ s.1, graphCutoff j ξ) : ℂ) •
            orientedElapsedAmplitude backward b χout χsource β r u z ξ)
          (rightLocalizer ρ mi f)) x) atTop
      (𝓝 (∫ y, (∑' p : ℕ × ℕ, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (graphCutoff p.1) (outputCutoff p.2) x y).mulVec (f y))) := by
  have hz (r : ℝ) (u z ξ : E) (hu : (u, z) ∉ tsupport χout ×ˢ tsupport χsource) :
      orientedElapsedAmplitude backward b χout χsource β r u z ξ = 0 := by
    have hz' : elapsedAmplitude b χout χsource β r u z ξ = 0 := by
      apply elapsedAmplitude_eq_zero_of_mask
      by_cases ho : u ∈ tsupport χout
      · exact Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport (fun hs ↦ hu ⟨ho, hs⟩)))
      · exact Or.inl (image_eq_zero_of_notMem_tsupport ho)
    cases backward <;> simp [orientedElapsedAmplitude, hz']
  let c := fun r j k ↦ physicalInputCarriers
    (cutoffPairCarriers (orientedElapsedAmplitude backward b χout χsource β r) mi
      (tsupport χout ×ˢ tsupport χsource) Ki Kη (hocs.prod hscs) hKi hKη (hz r) hiSupport j k) hρ
  have hcommon (r : ℝ) (j k : ℕ) : (c r j k).jointCarrier = (c 0 j k).jointCarrier := rfl
  have hlim := tendsto_elapsedPhysicalShellKernel_test_cutoffs backward ρ Δ Ψ b χout χsource β
    mi mo graphCutoff outputCutoff hS hA hi ho
    (fun j ↦ (contDiff_graphCutoff j).continuous) (fun k ↦ (contDiff_outputCutoff k).continuous)
    c hcommon C hs hb f hfi x
  apply hlim.congr'
  apply Eventually.of_forall
  intro s
  simpa only [Complex.ofReal_sum] using
    elapsedPhysicalShellKernel_test_eq_composition backward ρ Δ Ψ b χout χsource β mi mo
    (fun ξ ↦ ∑ j ∈ s.1, graphCutoff j ξ) (fun ζ ↦ ∑ k ∈ s.2, outputCutoff k ζ)
    hS hA hi ho
    (continuous_finsetSum _ (fun j _ ↦ (contDiff_graphCutoff j).continuous))
    (continuous_finsetSum _ (fun k _ ↦ (contDiff_outputCutoff k).continuous))
    (fun r ↦ RegularizedCarriers.finsetCutoffs (c r) s.1 s.2)
    (fun _ ↦ rfl) (fun _ ↦ rfl) f hf x hρ

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
