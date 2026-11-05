module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellSummation.Interchange
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.KernelSplitting
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PhysicalTransfer

/-!
# Exact high/low splitting of the literal elapsed kernels

The two branches used in `app:ch_regular:eq:chain-tail` add to the original
physical graph cutoff. Primitive compact regularity supplies the elapsed
integrability and output smoothness needed to split both kernels and jets.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph PhysicalShells PhysicalShells.Noncomparable
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256

variable (backward : Bool) {ρ : ℝ} (hρ : 0 < ρ) (Δ : ℝ)
  (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
  (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
  (j k : ℕ) (θ : ℝ → ℂ) (y : Euclidean (d + 1))
  (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
  (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
  (hb : ∀ r ∈ Icc 0 Δ, Continuous
    (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1) ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
  (hi : Continuous mi) (ho : ContDiff ℝ ∞ mo)
  (c : ∀ r ∈ Icc 0 Δ,
    KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      mi (graphCutoff j) (outputCutoff k))
  (hF : ContDiff ℝ ∞
    (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) 0 y))
  (ha : ∀ low, ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
    θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
      (graphBranchCutoff low j) (outputCutoff k) 0 y p))
  (K : Bool → Set (ℝ × JointVariables (Euclidean (d + 1)))) (hK : ∀ low, IsCompact (K low))
  (hs : ∀ low, tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
    θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
      (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K low)

include hρ hθ hΨ hb hi ho c hF ha hK hs in
private theorem elapsed_branch_regularity (low : Bool) :
    ContDiff ℝ ∞ (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo (graphBranchCutoff low j) (outputCutoff k) t y) ∧
    ∀ x, IntegrableOn (fun r ↦ KernelLimits.regularizedJointKernel backward
      (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) x y) (Icc 0 Δ) := by
  let cb (r : ℝ) (hr : r ∈ Icc 0 Δ) :
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphBranchCutoff low j) (outputCutoff k) :=
    { c r hr with compact_graphCutoff := hasCompactSupport_graphBranchCutoff low j }
  exact elapsedPhysicalShellKernel_regularity backward hρ Δ Ψ b χout χsource β mi mo
    (graphBranchCutoff low j) (outputCutoff k) θ y hθ hΨ hb hi ho
    (contDiff_graphBranchCutoff low j).continuous (contDiff_outputCutoff k).continuous
    cb hF (ha low) (hK low) (hs low)

include hρ hθ hΨ hb hi ho c hF ha hK hs in
/-- The bounded elapsed integral with the original `graphCutoff` is the
sum of its literal expanding and contracting physical kernels. This follows
from primitive integrability and the existing physical cutoff identity;
no splitting identity is an input (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem elapsedPhysicalShellKernel_graphCutoff_split (x : Euclidean (d + 1)) :
    elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
      (graphCutoff j) (outputCutoff k) x y =
    elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
      (graphBranchCutoff false j) (outputCutoff k) x y +
    elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
      (graphBranchCutoff true j) (outputCutoff k) x y := by
  have hi' : Continuous (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦
      mi (p.1, ρ⁻¹ • p.2)) :=
    hi.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))
  have ho' : Continuous (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦
      mo (p.1, ρ⁻¹ • p.2)) :=
    ho.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))
  have hh := (elapsed_branch_regularity backward hρ Δ Ψ b χout χsource β mi mo j k
    θ y hθ hΨ hb hi ho c hF ha K hK hs false).2 x
  have hl := (elapsed_branch_regularity backward hρ Δ Ψ b χout χsource β mi mo j k
    θ y hθ hΨ hb hi ho c hF ha K hK hs true).2 x
  unfold elapsedPhysicalShellKernel
  rw [← integral_add hh hl]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  exact regularizedJointKernel_graphCutoff_split backward (elapsedPhase Ψ r)
    (orientedElapsedAmplitude backward b χout χsource β r) _ _ j k
    (hΨ r hr) (hb r hr) hi' ho' (physicalInputCarriers (c r hr) hρ.ne') x y

include hρ hθ hΨ hb hi ho c hF ha hK hs in
/-- All evaluated output jets of the original elapsed `graphCutoff` split
exactly into the two physical branches. Smoothness is proved from the same
primitive compact data, retaining the bounded output ball and the full
`1-mo` factor (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_elapsedPhysicalShellKernel_graphCutoff_split
    (m : ℕ) (x : Euclidean (d + 1)) (v : Fin m → Euclidean (d + 1)) :
    iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo (graphCutoff j) (outputCutoff k) t y) x v =
    iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo (graphBranchCutoff false j) (outputCutoff k) t y) x v +
    iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo (graphBranchCutoff true j) (outputCutoff k) t y) x v := by
  have he : (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
      (graphCutoff j) (outputCutoff k) t y) =
      (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (graphBranchCutoff false j) (outputCutoff k) t y) +
      (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (graphBranchCutoff true j) (outputCutoff k) t y) := by
    funext t
    exact elapsedPhysicalShellKernel_graphCutoff_split backward hρ Δ Ψ b
      χout χsource β mi mo j k θ y hθ hΨ hb hi ho c hF ha K hK hs t
  have hh := (elapsed_branch_regularity backward hρ Δ Ψ b χout χsource β mi mo j k
    θ y hθ hΨ hb hi ho c hF ha K hK hs false).1
  have hl := (elapsed_branch_regularity backward hρ Δ Ψ b χout χsource β mi mo j k
    θ y hθ hΨ hb hi ho c hF ha K hK hs true).1
  rw [he, iteratedFDeriv_add (hh.of_le (by simp)) (hl.of_le (by simp))]
  rfl

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
