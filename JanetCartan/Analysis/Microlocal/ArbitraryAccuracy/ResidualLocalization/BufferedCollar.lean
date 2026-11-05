module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.GradientGaps
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.UniformCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedPhase

/-!
# Buffered geometric inputs for the direct residual integral

The closed input shoulders, full diagonal plateau and oriented zero-energy
image plateau exclude the actual stationary points. The compact-family
producer then constructs one collar, both gaps and all collar derivative
bounds. The auxiliary supported phase has the same two-time germs; no
fixed-elapsed arbitrary-energy separation follows or is asserted.
Consumer: `exists_uniform_elapsedGraphIntegral_fourier_bound_of_joint_grades`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph EvolutionIntegratedLocalization JanetCartan.Localization

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E

/-- Construct the uniform collar from the buffered physical chart geometry,
for either literal orientation. The supported phase and its germ identities
are produced by `exists_supported_twoTimePhase_extension`; the masks and
their plateaus belong to the protected-mask construction. Compactness may be
obtained from `isCompact_elapsedFiniteFamilyCarrier`. The only continuity
inputs concern the first derivatives of the same auxiliary phase on that
compact total family. No gradient gap or successful kernel estimate is an
input (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_buffered_supportedPhase_collar_data
    {X ι κ : Type*} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κ ℝ V) (backward : Bool)
    (h : X → RootState (Euclidean d) → ℝ)
    (Φ : X → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : X → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (Ψ : X → TwoTimePhase d) (x y : X → E)
    (mi mo : X → LocalizerSymbol (d + 1)) (R : X → Set (E × E))
    {K : Set (X × V)} (hK : IsCompact K)
    (hΨ : ∀ t, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ t)))
    (hC : ∀ t, (C t : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (Φ t))
    (hdiag : ∀ t, tsupport (mi t) ⊆ interior {p | mo t p = 1})
    (hflow : ∀ t ∈ K, 0 < t.2.1 → ∀ a ∈ tsupport (mi t.1), ∀ b ∈ R t.1,
      zeroEnergyFlowRelation backward (h t.1) (Φ t.1) t.2.1 a b →
        b ∈ interior {p | mo t.1 p = 1})
    (hin : ∀ t ∈ K, (y t.1, t.2.2.2.2.1) ∈ tsupport (mi t.1))
    (hout : ∀ t ∈ K, (x t.1, t.2.2.2.2.2) ∈ tsupport (fun p ↦ 1 - mo t.1 p))
    (hR : ∀ t ∈ K, (x t.1, t.2.2.2.2.2) ∈ R t.1)
    (hqB : ∀ t ∈ K, elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1 ∈ (C t.1).target)
    (hi : ∀ t ∈ K,
      Φ t.1 (((C t.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2, 0) =
        ((C t.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2)
    (hphaseB : ∀ t ∈ K, HasFDerivAt (twoTimePhase (C t.1))
      (twoTimePhaseDifferential (h t.1) (Φ t.1) (C t.1)
        (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
    (hqI : ∀ t ∈ K, 0 < t.2.1 →
      elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1 ∈ (C t.1).target)
    (hclock : ∀ t ∈ K, 0 < t.2.1 →
      (twoTimeState (Φ t.1) ((C t.1).symm
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))).1 = t.2.2.1.1 0)
    (hphaseI : ∀ t ∈ K, 0 < t.2.1 → HasFDerivAt (twoTimePhase (C t.1))
      (twoTimePhaseDifferential (h t.1) (Φ t.1) (C t.1)
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
    (hGermB : ∀ t ∈ K, SymbolBudgets.jointPhase (Ψ t.1) =ᶠ[𝓝
      (elapsedJointCoordinates (0, t.2.2))] SymbolBudgets.jointPhase (chartPhase (C t.1)))
    (hGermI : ∀ t ∈ K, 0 < t.2.1 → SymbolBudgets.jointPhase (Ψ t.1) =ᶠ[𝓝
      (elapsedJointCoordinates t.2)] SymbolBudgets.jointPhase (chartPhase (C t.1)))
    (hcontB : ∀ t ∈ K, ContinuousAt (fun tr : (X × V) × ℝ ↦
      fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ tr.1.1) (x tr.1.1) (y tr.1.1)
        (tr.2, w)) tr.1.2.2) (t, 0))
    (hcontI : ContinuousOn (fun t : X × V ↦
      fderiv ℝ (jointElapsedPhase backward (Ψ t.1) (x t.1) (y t.1)) t.2) K) :
    ∃ (χ : V → ℂ) (UT UI : X → Set V) (ε δT δI G : ℝ) (H : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ t, IsOpen (UT t)) ∧ (∀ t, IsOpen (UI t)) ∧
      0 < ε ∧ 0 < δT ∧ 0 < δI ∧
      (∀ p, |p.1| < ε → χ p = 1) ∧
      (∀ t, {p | (t, p) ∈ K} ∩ tsupport χ ⊆ UT t) ∧
      (∀ t, ({p | (t, p) ∈ K} ∩ tsupport (1 - χ)) ∩ {p | 0 < p.1} ⊆ UI t) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT t →
        δT ≤ phaseGradientSquare eT
          (fun w ↦ jointElapsedPhase backward (Ψ t) (x t) (y t) (r, w)) p) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT t →
        ‖fderiv ℝ (jointElapsedPhase backward (Ψ t) (x t) (y t)) (r, p)‖ ≤ G) ∧
      (∀ t p, p ∈ UI t ∩ {p | 0 < p.1} →
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward (Ψ t) (x t) (y t)) p) ∧
      (∀ t p, p ∈ UI t ∩ {p | 0 < p.1} →
        ‖fderiv ℝ (jointElapsedPhase backward (Ψ t) (x t) (y t)) p‖ ≤ G) ∧
      (∀ j, 0 ≤ H j) ∧
      (∀ p ∈ Prod.snd '' K, ∀ j, ‖iteratedFDeriv ℝ j χ p‖ ≤ H j) := by
  apply exists_compactFamily_jointElapsedPhase_collar_data eT eI backward Ψ x y hK
    (fun t ↦ contDiff_jointElapsedPhase backward (Ψ t) (x t) (y t) (hΨ t)) hcontB hcontI
  · intro t ht
    rw [fderiv_jointElapsedPhase_slice_eq_of_twoTimePhase_germ backward
      (chartPhase (C t.1)) (Ψ t.1) (x t.1) (y t.1) 0 t.2.2 (hGermB t ht)]
    exact fderiv_jointElapsedPhase_boundary_ne_zero_of_buffer (hC t.1) backward
      (hdiag t.1) (x t.1) (y t.1) t.2.2 (hqB t ht) (hi t ht)
      (hphaseB t ht) (hin t ht) (hout t ht)
  · intro t ht hr
    rw [(jointElapsedPhase_eventuallyEq_of_twoTimePhase backward
      (chartPhase (C t.1)) (Ψ t.1) (x t.1) (y t.1) t.2 (hGermI t ht hr)).fderiv_eq]
    exact fderiv_jointElapsedPhase_ne_zero_of_buffer (hC t.1) backward t.2.1
      (hflow t ht hr) (x t.1) (y t.1) t.2.2 (hqI t ht hr) (hclock t ht hr)
      (hphaseI t ht hr) (hin t ht) (hR t ht) (hout t ht)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
