module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.GlobalMajorant
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedShells
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.ElapsedKernels

/-!
# Global supported shell domination before operator identification

Expose the already constructed primitive majorant so both the strong
identification and the quantitative Sobolev assembly consume the same proof.
No integrated operator bound is required (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells LowBounds.FrequencyCutoff
open PhysicalShells.Noncomparable
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false


/-- Construct global summable domination from supported primitive amplitude
grades and the identified separated per-time kernel bound. The same two-time
extension is removed from all physical shells. This is the domination input
to the unregularized Sobolev assembly; it retains the noncompact identity tail
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedPhysicalShellKernel_global_majorant_of_supported_grades
    {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : Continuous mi) (ho : ContDiff ℝ ∞ mo)
    (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (his : HasCompactSupport mi) 
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hA : ∀ backward, Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (ha : ∀ backward y low j k, ContDiff ℝ ∞ (fun p : ℝ × JointVariables E ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p))
    (hcompact : ∀ backward y low j k, HasCompactSupport (fun p : ℝ × JointVariables E ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p))
    {J W : Set (SymbolBudgets.TwoTimePoint d)}
    (hJ : IsClosed J) (hW : IsOpen W) (hJW : J ⊆ W)
    (hPhase : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    (hPhaseSupport : ∀ r ∈ Icc 0 Δ, ∀ u z ξ, elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
      ((u 0, u 0 - r, spatialPart u), spatialPart ξ) ∈ J)
    (s c C b₀ : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (D : KernelEstimates.AmplitudeProfiles) {K : Set (JointVariables E)} (hK : IsCompact K)
    (hgrades : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, KernelEstimates.HasAmplitudeGrades D ρ (ρ ^ s) L
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y K)
    (hs : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, tsupport (jointAmplitude ρ
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ K)
    {Dsep : ℝ} (hDsep : 0 ≤ Dsep) (bLoss : ℕ)
    (hper : ∀ backward low j k, Noncomparable.SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j)
        (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ x y,
        ‖KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
          (orientedElapsedAmplitude backward b χout χsource β r)
          (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
            (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
          Dsep * ρ ^ (d + 1) * L ^ bLoss * Noncomparable.pairWeight low (d + 1) j k) :
    ∀ backward, ∃ M : ℕ × ℕ → ℝ, Summable M ∧
      ∀ j k x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (graphCutoff j) (outputCutoff k) x y‖ ≤ M (j, k) := by
  intro backward
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hext : ∃ Ψ' : TwoTimePhase d, ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ') ∧
      ∀ p ∈ J, SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 p] SymbolBudgets.jointPhase Ψ :=
    exists_supported_twoTimePhase_extension (d := d) Ψ (J := J) (W := W) hJ hW hJW hPhase
  let Ψ' : TwoTimePhase d := Classical.choose hext
  have hsm : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ') := (Classical.choose_spec hext).1
  have hgerm : ∀ p ∈ J, SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 p] SymbolBudgets.jointPhase Ψ :=
    (Classical.choose_spec hext).2
  have he (r : ℝ) (hr : r ∈ Icc 0 Δ) (u z ξ : E)
      (hamp : elapsedAmplitude b χout χsource β r u z ξ ≠ 0) :
      Ψ' (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ) =
        Ψ (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ) :=
    (hgerm _ (hPhaseSupport r hr u z ξ hamp)).eq_of_nhds
  have hcont : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ' p.1.1 p.1.2 p.2.1 p.2.2) :=
    hsm.continuous.comp ((continuous_fst.fst.prodMk
      (continuous_fst.snd.prodMk continuous_snd.fst)).prodMk continuous_snd.snd)
  have hSr (r : ℝ) : Continuous (Function.uncurry (elapsedPhase Ψ' r)) :=
    (KernelIdentification.continuous_elapsedPhase Ψ' hcont).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hAr (backward : Bool) (r : ℝ) : Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2) :=
    (hA backward).comp (continuous_const.prodMk continuous_id)
  let carriers (backward : Bool) (j k : ℕ) (r : ℝ) :
      RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphCutoff j) (outputCutoff k) := {
    amplitudeBase := tsupport χout ×ˢ tsupport χsource
    inputBase := Prod.fst '' tsupport mi
    inputFrequency := Prod.snd '' tsupport mi
    compact_amplitudeBase := hocs.prod hscs
    compact_inputBase := his.image continuous_fst
    compact_inputFrequency := his.image continuous_snd
    compact_graphCutoff := hasCompactSupport_graphCutoff j
    compact_outputCutoff := hasCompactSupport_outputCutoff k
    amplitude_zero := by
      intro u z ξ hz
      have hbzero : elapsedAmplitude b χout χsource β r u z ξ = 0 := by
        by_cases hu : u ∈ tsupport χout
        · have hzs : z ∉ tsupport χsource := fun hh ↦ hz ⟨hu, hh⟩
          exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
            (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport hzs)))
        · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
            (Or.inl (image_eq_zero_of_notMem_tsupport hu))
      cases backward <;> simp only [orientedElapsedAmplitude, Bool.false_eq_true,
        ite_false, ite_true, hbzero, Matrix.conjTranspose_zero]
    input_zero := by
      intro y η h
      exact image_eq_zero_of_notMem_tsupport
        (fun hh ↦ h ⟨⟨(y, η), hh, rfl⟩, ⟨(y, η), hh, rfl⟩⟩) }
  have hp : ∀ low j k, Noncomparable.SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
      (graphLower low j) (graphUpper low j)
      (outputLower k) (outputUpper k) →
    ∀ r ∈ Icc 0 Δ, ∀ x y,
      ‖KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ' r)
        (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
        Dsep * ρ ^ (d + 1) * L ^ bLoss * Noncomparable.pairWeight low (d + 1) j k := by
    intro low j k hsep r hr x y
    rw [physicalElapsedKernel_twoTimePhase_congr backward ρ r Ψ Ψ' b
      χout χsource β mi mo _ _ x y (he r hr)]
    exact hper backward low j k hsep r hr x y
  obtain ⟨M, hnonneg, hsum, hbnd⟩ := exists_elapsedPhysicalShellKernel_global_majorant
    backward hρ hL s Δ Ψ' b χout χsource β mi mo θ hθ (fun r _ ↦ hSr r)
    (fun r _ ↦ hAr backward r) hi ho horange
    (fun j k r _ ↦ carriers backward j k r)
    (fun y ↦ contDiff_jointElapsedPhase backward _ 0 y
      (contDiff_normalizedTwoTimePhase_joint ρ Ψ' hsm)) (ha backward) (hcompact backward)
    c C b₀ ha₀ D hK (hgrades backward) (hs backward) hDsep bLoss hp
  refine ⟨M, hsum, ?_⟩
  intro j k x y
  rw [← elapsedPhysicalShellKernel_twoTimePhase_congr backward ρ Δ Ψ Ψ' b
    χout χsource β mi mo (graphCutoff j) (outputCutoff k) he]
  exact hbnd j k x y

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
