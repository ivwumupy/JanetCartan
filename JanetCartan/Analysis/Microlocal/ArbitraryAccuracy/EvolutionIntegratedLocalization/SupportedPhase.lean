module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactKernels
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.Basic

/-!
# One supported two-time phase extension for the elapsed integral

The half-space argument in `app:ch_regular:eq:chain-tail` differentiates
elapsed time. Independent extensions at each elapsed time do not suffice.
Here one smooth extension is constructed in the original TWO time variables.
It preserves all joint elapsed phase germs on the buffered supported chart,
including the elapsed derivative and the boundary tangential derivatives.
The actual bounded compact-frequency kernel is unchanged. No global
homogeneity or regularity at the spatial zero covector is required.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false

/-- A single globally smooth extension of the original two-time phase
preserves its germ on a closed buffered chart, including a noncompact
frequency tail if present. Consumer: the joint half-space kernel estimate
(`app:ch_regular_base:eq:fixed-time-representation`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_supported_twoTimePhase_extension
    (Ψ : TwoTimePhase d) {J W : Set (SymbolBudgets.TwoTimePoint d)}
    (hJ : IsClosed J) (hW : IsOpen W) (hJW : J ⊆ W)
    (hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W) :
    ∃ Ψ' : TwoTimePhase d, ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ') ∧
      ∀ p ∈ J, SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 p] SymbolBudgets.jointPhase Ψ := by
  obtain ⟨U, hU, hJU, hUW⟩ := normal_exists_closure_subset hJ hW hJW
  obtain ⟨V, hV, hUV, hVW⟩ := normal_exists_closure_subset isClosed_closure hW hUW
  obtain ⟨χ, hχ, _, hsχ, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  refine ⟨fun t s u η ↦ χ ((t, s, u), η) * Ψ t s u η, ?_, ?_⟩
  · apply Localization.contDiff_of_contDiffOn_support_neighborhood hW
    · exact hχ.contDiffOn.mul hΨ
    · exact tsupport_mul_subset_left.trans (by simpa only [tsupport, hsχ] using hVW)
  · intro p hp
    filter_upwards [hU.mem_nhds (hJU hp)] with z hz
    change χ z * SymbolBudgets.jointPhase Ψ z = SymbolBudgets.jointPhase Ψ z
    rw [(hχone z).mp (subset_closure hz), one_mul]

/-- A two-time phase germ pulls back to the full joint elapsed phase germ,
with elapsed time differentiated together with all bases and covectors.
This is stronger than separate agreement at fixed elapsed times
(`app:ch_regular:eq:joint-stationary`). -/
theorem jointElapsedPhase_eventuallyEq_of_twoTimePhase
    (backward : Bool) (Ψ Ψ' : TwoTimePhase d) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (he : SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 (elapsedJointCoordinates p)]
      SymbolBudgets.jointPhase Ψ) :
    jointElapsedPhase backward Ψ' x y =ᶠ[𝓝 p] jointElapsedPhase backward Ψ x y := by
  have hh := he.comp_tendsto (elapsedJointCoordinates.continuous.tendsto p)
  filter_upwards [hh] with w hw
  change Ψ' (w.2.1.1 0) (w.2.1.1 0 - w.1) (spatialPart w.2.1.1)
      (spatialPart w.2.2.1) =
    Ψ (w.2.1.1 0) (w.2.1.1 0 - w.1) (spatialPart w.2.1.1)
      (spatialPart w.2.2.1) at hw
  cases backward <;> dsimp only [jointElapsedPhase, jointPhase, forwardPhase, reversePhase,
    elapsedPhase] <;> rw [hw]

/-- Every full-gradient jet, in particular the missing elapsed derivative,
is unchanged by the supported two-time extension. This transfers the
primitive phase grades and the interior stationary equations
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_jointElapsedPhase_gradient_eq_of_twoTimePhase_germ
    (backward : Bool) (Ψ Ψ' : TwoTimePhase d) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (he : SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 (elapsedJointCoordinates p)]
      SymbolBudgets.jointPhase Ψ) (j : ℕ) :
    iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward Ψ' x y)) p =
      iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward Ψ x y)) p :=
  (((jointElapsedPhase_eventuallyEq_of_twoTimePhase backward Ψ Ψ' x y p he).fderiv
    (𝕜 := ℝ)).iteratedFDeriv ℝ j).eq_of_nhds

/-- The boundary tangential derivative is preserved by the same extension.
The statement also applies to every fixed elapsed slice in the collar
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_jointElapsedPhase_slice_eq_of_twoTimePhase_germ
    (backward : Bool) (Ψ Ψ' : TwoTimePhase d) (x y : Euclidean (d + 1))
    (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (he : SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 (elapsedJointCoordinates (r, p))]
      SymbolBudgets.jointPhase Ψ) :
    fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ' x y (r, w)) p =
      fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p := by
  have hh := (jointElapsedPhase_eventuallyEq_of_twoTimePhase backward Ψ Ψ' x y (r, p) he).comp_tendsto
    ((continuous_const.prodMk continuous_id).tendsto p)
  exact hh.fderiv_eq

/-- A compact supported joint carrier supplies its own closed two-time
carrier. One extension works for every external base and both orientations;
all its joint germs agree with the original. The actual chart producer must
place this carrier inside its open smoothness domain
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_jointElapsedPhase_extension_on_compact_carrier
    (Ψ : TwoTimePhase d) {W : Set (SymbolBudgets.TwoTimePoint d)} (hW : IsOpen W)
    (hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (hmap : MapsTo elapsedJointCoordinates K W) :
    ∃ Ψ' : TwoTimePhase d, ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ') ∧
      ∀ (backward : Bool) (x y : Euclidean (d + 1)),
        ContDiff ℝ ∞ (jointElapsedPhase backward Ψ' x y) ∧
        ∀ p ∈ K, jointElapsedPhase backward Ψ' x y =ᶠ[𝓝 p]
          jointElapsedPhase backward Ψ x y := by
  obtain ⟨Ψ', hs, he⟩ := exists_supported_twoTimePhase_extension Ψ
    (hK.image elapsedJointCoordinates.continuous).isClosed hW
    (by rintro _ ⟨p, hp, rfl⟩; exact hmap hp) hΨ
  exact ⟨Ψ', hs, fun backward x y ↦
    ⟨contDiff_jointElapsedPhase backward Ψ' x y hs,
      fun p hp ↦ jointElapsedPhase_eventuallyEq_of_twoTimePhase backward Ψ Ψ' x y p
        (he _ ⟨p, hp, rfl⟩)⟩⟩

/-- Supported two-time replacement preserves the actual bounded
compact-frequency elapsed kernel, not merely a formal phase. The hypothesis
is equality of the original phase on the actual full amplitude support;
the extension theorem supplies it from the supported chart. All masks and
the literal adjoint amplitude stay in their original order
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem integral_regularizedElapsedKernel_twoTimePhase_congr
    (backward : Bool) (ρ Δ : ℝ) (Ψ Ψ' : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (he : ∀ r ∈ Icc 0 Δ, ∀ p : JointVariables (Euclidean (d + 1)),
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 (ρ • p.2.1) ≠ 0 →
        SymbolBudgets.jointPhase Ψ' (elapsedJointCoordinates (r, p)) =
          SymbolBudgets.jointPhase Ψ (elapsedJointCoordinates (r, p))) :
    (∫ r in Icc 0 Δ, KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ' r)
      (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo x y) =
    ∫ r in Icc 0 Δ, KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
      (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo x y := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  unfold KernelEstimates.regularizedJointKernel
  apply congrArg (fun M : Matrix (Fin q) (Fin q) ℂ ↦
    (KernelEstimates.jointNormalization (d + 1) * ρ ^ (3 * (d + 1))) • M)
  apply integral_congr_ae
  apply ae_of_all
  intro p
  by_cases hz : orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 (ρ • p.2.1) = 0
  · simp only [jointAmplitude, hz, smul_zero]
  · have hp := he r hr p hz
    change Ψ' (p.1.1 0) (p.1.1 0 - r) (spatialPart p.1.1) (spatialPart p.2.1) =
      Ψ (p.1.1 0) (p.1.1 0 - r) (spatialPart p.1.1) (spatialPart p.2.1) at hp
    have hf : jointPhase backward (elapsedPhase Ψ' r) x y p =
        jointPhase backward (elapsedPhase Ψ r) x y p := by
      cases backward <;> dsimp only [jointPhase, forwardPhase, reversePhase, elapsedPhase] <;> rw [hp]
    simp only [Localization.phaseOscillation, Pi.smul_apply, smul_eq_mul, hf]

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
