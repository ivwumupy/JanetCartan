module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Phase.Profiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.CommonMasks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades

/-!
# The selected quantitative auxiliary phase for the complete residual

Construct the auxiliary from the actual local phase and supply the literal
`hprimitivePhase`, `hauxPhaseGrades`, supported germs and physical phase
agreement of `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
The endpoint output, chart input and selected multiplier are unchanged; the
last already contains the doubled threshold. Only the original coefficient
profile and precise geometric inclusions remain inputs. The parent assembles
these inclusions from the retained certificates and
`ProtectedMasks.exists_uniform_conic_nested_localization_data`.

Source: `app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_regular:eq:high-phase`, and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open RegularSector.FiniteAlgebraic
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "V" => ℝ × JointVariables E

/-- Supply the quantitative phase inputs of `CompleteFactor` on the SAME
retained local charts. The auxiliary is constructed, globally smooth and
quantitatively controlled, with no assumption about a retained extension.

`hC`, `hbuffer` and `hphase` are outputs of
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`.
`hKphase`, `hpos`, `hmap` and `hjet` are compact normalized carrier geometry
from the retained certificates and protected nested localizers. `hUp` is the
physical conic chart inclusion, and `hphysical` is the actual mask-carrier
inclusion supplied by `exists_selected_elapsed_physical_carriers` (with its
retained angular normalization). These geometric inputs are explicit so this
deduction can be assembled independently of their construction.

The returned joint germs also apply without the nonnegative-time restriction
needed by `CompleteFactor`. The physical agreement holds for every amplitude
under the literal endpoint output, chart input and doubled-threshold multiplier.
Source: `app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`. -/
theorem exists_selected_completeFactor_phase_inputs
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (Kphase : f.centers → Set (SymbolBudgets.TwoTimePoint d))
    (hKphase : ∀ p, IsCompact (Kphase p))
    (hpos : ∀ p, ∀ w ∈ Kphase p, 0 < (f.chart p).radialSection w.2)
    (hmap : ∀ p,
      let e := coordinateSplit (f.chart p).index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      MapsTo (normalize (f.chart p).radialSection ∘ budgetCoordinates) (Kphase p)
        (closedBall (z.1, z) (f.chart p).targetRadius))
    (Kjet : f.centers → Set V) (ψ : f.centers → E → ℝ)
    (mi mo : f.centers → LocalizerSymbol (d+1))
    (hjet : ∀ p, ∀ u ∈ tsupport (ψ p), ∀ y ∈ Prod.fst '' tsupport (mi p),
      MapsTo elapsedJointCoordinates (elapsedOutputJetCarrier (Kjet p) (mi p) (mo p) u y)
        (Kphase p))
    (Up : f.centers → Set (SymbolBudgets.TwoTimePoint d))
    (hUp : ∀ p, ∀ w ∈ Up p,
      let e := coordinateSplit (f.chart p).index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      budgetCoordinates w ∈ domain (f.chart p).radialSection
        (closedBall (z.1, z) (f.chart p).targetRadius) ∧ (1/2 : ℝ) < ‖w.2‖)
    (output : E → ℝ) (threshold Δ : ℝ)
    (hphysical : ∀ p, ∀ r ∈ Icc 0 Δ,
      ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      ∀ w ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p),
        SymbolBudgets.elapsedPoint r (w, ξ) ∈ Up p)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ P₀ Pbase : ℕ → ℝ, (∀ j, 0 ≤ P₀ j) ∧ (∀ j, 0 ≤ Pbase j) ∧
      ∀ (Rstar : ℕ), 3 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      ∀ C : f.centers → OpenPartialHomeomorph T T,
      (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target) →
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        closedBall (z.1, z) (f.chart p).targetRadius ⊆ (C p).target) →
      (∀ p m,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        cNorm (closedBall (z.1, z) (f.chart p).targetRadius) m (twoTimePhase (C p)) ≤
          (f.chart p).phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
      let Ψoriginal := fun p ↦ curriedExtend (f.chart p).radialSection (twoTimePhase (C p))
      ∃ Ψ : f.centers → TwoTimePhase d,
        (∀ p, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ p))) ∧
        (∀ p, ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (Ψ p)) (Up p)) ∧
        (∀ p, ∀ η v, (v, η) ∈ Up p → ∀ k, 1 ≤ k →
          ‖iteratedFDeriv ℝ (k+1) (fun w : ℝ × ℝ × Euclidean d ↦
            Ψ p w.1 w.2.1 w.2.2 η) v‖ ≤ ‖η‖ * Pbase k * L ^ k) ∧
        (∀ p, ∀ w ∈ Kphase p, SymbolBudgets.jointPhase (Ψ p) =ᶠ[𝓝 w]
          SymbolBudgets.jointPhase (Ψoriginal p)) ∧
        (∀ p, ∀ w ∈ Up p, SymbolBudgets.jointPhase (Ψ p) =ᶠ[𝓝 w]
          SymbolBudgets.jointPhase (Ψoriginal p)) ∧
        (∀ ρ : ℝ, 1 ≤ ρ → ∀ p, ∀ u ∈ tsupport (ψ p), ∀ y ∈ Prod.fst '' tsupport (mi p),
          ∀ w ∈ elapsedOutputJetCarrier (Kjet p) (mi p) (mo p) u y,
            SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ p)) =ᶠ[𝓝
              (elapsedJointCoordinates w)] SymbolBudgets.jointPhase (Ψoriginal p)) ∧
        (∀ ρ : ℝ, 1 ≤ ρ → ∀ p, ∀ u ∈ tsupport (ψ p), ∀ y ∈ Prod.fst '' tsupport (mi p),
          ∀ w ∈ elapsedOutputJetCarrier (Kjet p) (mi p) (mo p) u y, ∀ j,
            ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
              (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ p)))) (elapsedJointCoordinates w)‖ ≤
                P₀ j * L ^ j) ∧
        ∀ p (b : TwoTimeAmplitude d q), ∀ r ∈ Icc 0 Δ, ∀ u z ξ,
          elapsedAmplitude b (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) r u z ξ ≠ 0 →
          elapsedPhase (Ψ p) r u ξ = elapsedPhase (Ψoriginal p) r u ξ := by
  obtain ⟨P₀, Pbase, hP₀, hPbase, hprofiles⟩ :=
    exists_selected_smooth_auxiliaryPhase_profiles f Kphase hKphase hpos hmap A hA
  refine ⟨P₀, Pbase, hP₀, hPbase, ?_⟩
  intro Rstar hRstar L hL Q hQ C hC hbuffer hphase Ψoriginal
  obtain ⟨Ψ, hΨ, he, hn, hgrade, hbase⟩ :=
    hprofiles Rstar hRstar L hL Q hQ C hC hbuffer hphase
  have heUp p w (hw : w ∈ Up p) :
      SymbolBudgets.jointPhase (Ψ p) =ᶠ[𝓝 w] SymbolBudgets.jointPhase (Ψoriginal p) :=
    he p w (hUp p w hw).1 (Or.inr (hUp p w hw).2)
  refine ⟨Ψ, hΨ, fun p ↦ (hΨ p).contDiffOn, ?_, ?_, heUp, ?_, ?_, ?_⟩
  · intro p η v hv k _hk
    exact hbase p η v (hUp p (v, η) hv).1 (hUp p (v, η) hv).2 k
  · intro p w hw
    exact he p w ⟨hpos p w hw, hmap p hw⟩ (Or.inl hw)
  · intro ρ hρ p u hu y hy w hw
    exact hn ρ hρ p _ (hjet p u hu y hy hw)
  · intro ρ hρ p u hu y hy w hw j
    exact (hgrade ρ hρ p _ (hjet p u hu y hy hw) j).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le j 1)) (hP₀ j))
  · intro p b r hr u z ξ hnonzero
    have ho : endpointOutputMask f p output u ≠ 0 := by
      intro hz
      exact hnonzero (elapsedAmplitude_eq_zero_of_mask b _ _ _ r u z ξ (Or.inl hz))
    have hi : chartInputMask f p z ≠ 0 := by
      intro hz
      exact hnonzero (elapsedAmplitude_eq_zero_of_mask b _ _ _ r u z ξ (Or.inr (Or.inl hz)))
    have hβ : selectedEndpointMultiplier f p threshold ξ ≠ 0 := by
      intro hz
      exact hnonzero (elapsedAmplitude_eq_zero_of_mask b _ _ _ r u z ξ (Or.inr (Or.inr hz)))
    have hw := hphysical p r hr ξ (subset_tsupport _ hβ) (u, z)
      ⟨subset_tsupport _ ho, subset_tsupport _ hi⟩
    have heq := (heUp p _ hw).eq_of_nhds
    simp only [SymbolBudgets.elapsedPoint_eq, SymbolBudgets.jointPhase] at heq
    change (u 0 - r) * ξ 0 + _ = (u 0 - r) * ξ 0 + _
    exact congrArg (fun a ↦ (u 0 - r) * ξ 0 + a) heq

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
