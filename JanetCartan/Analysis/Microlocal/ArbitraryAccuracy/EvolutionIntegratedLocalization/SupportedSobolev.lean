module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SobolevExtension
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedShells

/-!
# Sobolev realization using one supported two-time phase extension

The original conic phase need not be smooth at zero. One extension in both
time variables supplies the joint regularity used by the Cartesian kernels,
and exact equality removes it from every shell jet and physical test action.
Consumer: the same-operator Fourier estimate (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells CartesianJets
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization.SobolevRealization Pseudodifferential
open FiniteChain.Retarded.KernelSobolev RetardedSobolev.Spaces
variable {d q m : ℕ}
local notation "E" => Euclidean (d + 1)
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false

/-- Joint elapsed regularity follows from the same two-time smooth extension
used in the half-space estimates, by a fixed linear slice of the full joint
phase (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem contDiff_elapsedPhase_joint_of_twoTimePhase
    (Ψ : TwoTimePhase d) (hΨ : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ)) :
    ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2) := by
  have hc := (contDiff_jointElapsedPhase false Ψ 0 0 hΨ).comp
    (f := fun p : ℝ × (E × E) ↦ (p.1, ((p.2.1, 0), p.2.2, 0, 0)))
    (contDiff_fst.prodMk ((contDiff_snd.fst.prodMk contDiff_const).prodMk
      (contDiff_snd.snd.prodMk (contDiff_const.prodMk contDiff_const))))
  simpa only [Function.comp_def, jointElapsedPhase, jointPhase, Bool.false_eq_true,
    ite_false, forwardPhase, inner_zero_right, inner_zero_left, sub_zero, add_zero] using hc

/-- Construct and remove the supported phase extension in the Fourier
Sobolev realization of the literal elapsed shells. The only pointwise
quantitative inputs are the original shell-jet majorants already produced
by `KernelMajorants` and `GlobalMajorant`. Neither smoothness at the original
zero covector nor an extended-phase operator is assumed or exported
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedShell_fourier_realization_of_supported_jet_majorants
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (backward : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    (his : HasCompactSupport mi)
    (hA : ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    {Jphase W : Set (SymbolBudgets.TwoTimePoint d)}
    (hJphase : IsClosed Jphase) (hW : IsOpen W) (hJW : Jphase ⊆ W)
    (hPhase : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    (hPhaseSupport : ∀ r ∈ Icc 0 Δ, ∀ u z ξ,
      elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
        ((u 0, u 0 - r, spatialPart u), spatialPart ξ) ∈ Jphase)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ l ≤ m, ∀ p, 0 ≤ B l p) (hs : ∀ l ≤ m, Summable (B l))
    (hb : ∀ p x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m, ∀ v : Fin l → E,
      (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ l (fun z ↦ elapsedPhysicalShellKernel backward
        ρ Δ Ψ b χout χsource β mi mo (graphCutoff p.1) (outputCutoff p.2) z y) x v‖ ≤ B l p)
    (C₀ : ℕ × ℕ → ℝ) (hs₀ : Summable C₀)
    (hb₀ : ∀ p x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
      mi mo (graphCutoff p.1) (outputCutoff p.2) x y‖ ≤ C₀ p)
    (e : ℝ) (bLoss N : ℕ) (D : ℕ → ℝ) (hD : ∀ l ≤ m, 0 ≤ D l)
    (hgrades : ∀ l ≤ m, (∑' p, B l p) ≤ D l * ρ ^ ((l : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N) :
    ∃ T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
      (∀ u, MemVectorFourierSobolev (m : ℝ) (T u) ∧
        vectorFourierSobolevNorm (m : ℝ) (T u) ≤
          (fourierComparisonConstant J m * ((q : ℝ) * q) *
            jetMajorant J (cutoffDerivativeProfile hψ hsψ) D m *
            compactSupportFactor volume volume
              ((fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' (Prod.fst '' tsupport mi))
              (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))) *
                ρ ^ ((m : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N * ‖u‖) ∧
      ∀ (f : Fin q → Test d) (a : Fin q),
        finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a =ᵐ[volume]
          fun x ↦ (ψ x : ℂ) * (∫ y, (∑' p : ℕ × ℕ, elapsedPhysicalShellKernel backward
            ρ Δ Ψ b χout χsource β mi mo (graphCutoff p.1) (outputCutoff p.2) x y).mulVec
              (physicalTestField J f y)) a := by
  obtain ⟨Ψ', hsm, _, _, _, he⟩ := exists_supported_elapsedPhysicalShellKernel_phase Δ Ψ b
    χout χsource β hJphase hW hJW hPhase hPhaseSupport
  have hreg := contDiff_elapsedPhase_joint_of_twoTimePhase Ψ' hsm
  have hb' : ∀ p x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m, ∀ v : Fin l → E,
      (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ l (fun z ↦ elapsedPhysicalShellKernel backward
        ρ Δ Ψ' b χout χsource β mi mo (graphCutoff p.1) (outputCutoff p.2) z y) x v‖ ≤ B l p := by
    simp_rw [he]
    exact hb
  have hb₀' : ∀ p x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ' b χout χsource β
      mi mo (graphCutoff p.1) (outputCutoff p.2) x y‖ ≤ C₀ p := by
    simp_rw [he]
    exact hb₀
  have result := exists_elapsedShell_fourier_realization_of_jet_majorants J backward
    (zero_lt_one.trans_le hρ).ne' Δ Ψ' b χout χsource β mi mo hout hsource his
    (fun _ _ _ _ ↦ hreg.contDiffAt) hA hi ho ψ hψ hsψ hJ hreg.continuous
    B hB hs hb' C₀ hs₀ hb₀' hρ hL e bLoss N D hD hgrades
  simp_rw [he] at result
  exact result

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
