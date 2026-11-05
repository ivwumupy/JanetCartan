module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedPhase
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellKernels

/-!
# Supported phase replacement for the actual physical shell family

One two-time extension preserves the original physical kernels before and
after bounded elapsed integration, in both orientations. Consequently all
output jets and all shell majorants concern the original operator even when
the conic phase is not smooth at zero. This uses the existing extension
constructor and no new Fourier-integral calculus (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The normalized phase of a smooth two-time extension is smooth jointly.
This verifies the smoothness input of the elapsed-shell estimates without
asserting smoothness at zero for the original conic phase
(`app:ch_regular:eq:high-phase`). -/
theorem contDiff_normalizedTwoTimePhase_joint
    (ρ : ℝ) (Ψ : TwoTimePhase d)
    (hΨ : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ)) :
    ContDiff ℝ ∞ (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ)) := by
  exact (hΨ.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ))).const_smul ρ⁻¹

/-- Agreement on the literal full-amplitude support preserves each physical
regularized kernel, with both original localizers and the same adjoint order.
The time is fixed only for this algebraic identity; the extension remains
jointly smooth in both times (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem physicalElapsedKernel_twoTimePhase_congr
    (backward : Bool) (ρ r : ℝ) (Ψ Ψ' : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : E → ℝ) (x y : E)
    (he : ∀ u z ξ, elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
      Ψ' (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ) =
        Ψ (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ)) :
    KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ' r)
      (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y =
    KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
      (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y := by
  unfold KernelLimits.regularizedJointKernel
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro p
  by_cases hz : elapsedAmplitude b χout χsource β r p.1.1 p.1.2 p.2.1 = 0
  · cases backward <;>
      simp [KernelLimits.regularizedJointIntegrand, KernelLimits.regularizedJointAmplitude,
        orientedElapsedAmplitude, hz]
  · have hp := he p.1.1 p.1.2 p.2.1 hz
    have hf : jointPhase backward (elapsedPhase Ψ' r) x y p =
        jointPhase backward (elapsedPhase Ψ r) x y p := by
      cases backward <;> dsimp only [jointPhase, forwardPhase, reversePhase, elapsedPhase] <;> rw [hp]
    simp only [KernelLimits.regularizedJointIntegrand, hf]

/-- The same supported replacement preserves the bounded elapsed kernel and
every output derivative. The interval includes both genuine endpoints; no
limit, kernel estimate or operator identification is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem elapsedPhysicalShellKernel_twoTimePhase_congr
    (backward : Bool) (ρ Δ : ℝ) (Ψ Ψ' : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : E → ℝ)
    (he : ∀ r ∈ Icc 0 Δ, ∀ u z ξ, elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
      Ψ' (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ) =
        Ψ (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ)) :
    elapsedPhysicalShellKernel backward ρ Δ Ψ' b χout χsource β mi mo χA χo =
      elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo χA χo := by
  funext x y
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  exact physicalElapsedKernel_twoTimePhase_congr backward ρ r Ψ Ψ' b χout χsource β
    mi mo χA χo x y (he r hr)

/-- Construct one supported two-time phase for the entire bounded elapsed
family. The exact carrier condition refers to the original masked symbol,
so the original low-frequency pieces and source shoulders are retained.
Its germs preserve all elapsed and boundary derivatives. The construction
simultaneously identifies every physical regularization and output jet in
both orientations; neither scales nor accuracy enter its choice.

The carrier is supplied by the actual buffered conic chart. This theorem
instantiates `exists_supported_twoTimePhase_extension`, rather than assuming
an extension or a kernel identity (`app:ch_regular:lem:finite-chain`). -/
theorem exists_supported_elapsedPhysicalShellKernel_phase
    (Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ)
    {J W : Set (SymbolBudgets.TwoTimePoint d)}
    (hJ : IsClosed J) (hW : IsOpen W) (hJW : J ⊆ W)
    (hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    (hs : ∀ r ∈ Icc 0 Δ, ∀ u z ξ, elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
      ((u 0, u 0 - r, spatialPart u), spatialPart ξ) ∈ J) :
    ∃ Ψ' : TwoTimePhase d,
      ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ') ∧
      (∀ p ∈ J, SymbolBudgets.jointPhase Ψ' =ᶠ[nhds p] SymbolBudgets.jointPhase Ψ) ∧
      (∀ ρ backward x y, ContDiff ℝ ∞
        (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ') x y)) ∧
      (∀ (backward : Bool) (ρ r : ℝ), r ∈ Icc 0 Δ → ∀ (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ) (x y : E),
        KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ' r)
          (orientedElapsedAmplitude backward b χout χsource β r)
          (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y =
        KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
          (orientedElapsedAmplitude backward b χout χsource β r)
          (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y) ∧
      ∀ backward ρ mi mo χA χo,
        elapsedPhysicalShellKernel backward ρ Δ Ψ' b χout χsource β mi mo χA χo =
          elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo χA χo := by
  obtain ⟨Ψ', hsm, hgerm⟩ := exists_supported_twoTimePhase_extension Ψ hJ hW hJW hΨ
  have he (r : ℝ) (hr : r ∈ Icc 0 Δ) (u z ξ : E)
      (ha : elapsedAmplitude b χout χsource β r u z ξ ≠ 0) :
      Ψ' (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ) =
        Ψ (u 0) (u 0 - r) (spatialPart u) (spatialPart ξ) :=
    (hgerm _ (hs r hr u z ξ ha)).eq_of_nhds
  refine ⟨Ψ', hsm, hgerm, ?_, ?_, ?_⟩
  · exact fun ρ backward x y ↦ contDiff_jointElapsedPhase backward _ x y
      (contDiff_normalizedTwoTimePhase_joint ρ Ψ' hsm)
  · exact fun backward ρ r hr mi mo χA χo x y ↦ physicalElapsedKernel_twoTimePhase_congr
      backward ρ r Ψ Ψ' b χout χsource β mi mo χA χo x y (he r hr)
  · exact fun backward ρ mi mo χA χo ↦ elapsedPhysicalShellKernel_twoTimePhase_congr
      backward ρ Δ Ψ Ψ' b χout χsource β mi mo χA χo he

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
