module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhaseCarriers

/-!
# Quantitative phase inputs on the retained elapsed carriers

Both normalized and physical phase grades use one constructed smooth auxiliary.
Its supported germs instantiate the noncomparable geometry. The actual local
phase and its retained quantitative certificates are the only analytic inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
open FiniteChain.Graph.PhysicalShells
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)

/-- Assemble the constructed auxiliary phase and all its quantitative and
noncomparable inputs to `CompleteFactor`. The exact comparable carrier is
supplied by `exists_selected_completeFactor_amplitude_inputs`; the cutoffs
are produced by `exists_selected_buffered_elapsed_cutoffs`. All remaining
analytic hypotheses are retained local phase certificates from
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`.

The normalized carrier inclusion and the supported physical germs are proved
here. In particular the covector comparison is instantiated on this same
auxiliary. The physical domains also contain the full amplitude evaluations,
and lie inside the domain of `exists_selected_physicalResidual_profile`.
Sources: `app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_selected_elapsed_phase_inputs
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ a₀ b₀ : ℝ, 0 < a₀ →
      ∀ Kg : f.centers → Set (JointVariables E), (∀ p, IsCompact (Kg p)) →
      (∀ p, Kg p = Comparable.comparableJointCarrier c C a₀ b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a₀ b₀)) →
      ∀ θ : f.centers → ℝ → ℂ, (∀ p, HasCompactSupport (θ p)) →
      (∀ p, tsupport (θ p) ⊆ ball 0
        (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)) →
      ∃ P₀ Pbase : ℕ → ℝ, (∀ j, 0 ≤ P₀ j) ∧ (∀ j, 0 ≤ Pbase j) ∧
      ∃ Vphase : f.centers → Set (E × E),
      ∃ Ua : f.centers → Set (SymbolBudgets.TwoTimePoint d),
      ∃ Kphysical : f.centers → Bool → ℕ → Set (E × E),
        (∀ p, IsOpen (Vphase p)) ∧ (∀ p, IsOpen (Ua p)) ∧
        (∀ p low j, IsCompact (Kphysical p low j)) ∧
        (∀ p low j, Kphysical p low j ⊆ Vphase p) ∧
        (∀ p,
          let e := coordinateSplit (f.chart p).index
          let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
          Ua p ⊆ bufferedBase z (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius) ×ˢ
            angularCone (f.chart p).radialSection z.2.2
              (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)) ∧
        (∀ p, ∀ w ∈ Ua p, (1/2 : ℝ) < ‖w.2‖) ∧
        (∀ p, ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4),
          ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
          ∀ w ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p),
            SymbolBudgets.elapsedPoint r (w, ξ) ∈ Ua p) ∧
        (∀ p (b : TwoTimeAmplitude d q) ρ, ρ ≠ 0 →
          ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), ∀ low j,
          ∀ ξ ∈ normalizedGraphCarrier ρ low j,
          ∀ w ∈ tsupport (fun w : E × E ↦ elapsedAmplitude b
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) r w.1 w.2 (ρ • ξ)),
            (w.1, ρ • ξ) ∈ Kphysical p low j ∧ SymbolBudgets.elapsedPoint r (w, ρ • ξ) ∈ Ua p) ∧
        ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
        ∀ Q : E → Fin (d+1) → MetricTensor (d+1),
        (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar)) →
        ∀ (h : f.centers → Z → ℝ) (Φ : f.centers → Z × ℝ → Z)
          (Cchart : f.centers → OpenPartialHomeomorph T T),
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cchart p)) (Cchart p).target) →
        (∀ p,
          let e := coordinateSplit (f.chart p).index
          let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
          closedBall (z.1, z) (f.chart p).targetRadius ⊆ (Cchart p).target) →
        (∀ p, ∀ v ∈ (Cchart p).target, HasFDerivAt (twoTimePhase (Cchart p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cchart p) v) v) →
        (∀ p,
          let e := coordinateSplit (f.chart p).index
          let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
          ∀ v ∈ closedBall (z.1, z) (f.chart p).targetRadius,
            ‖twoTimePhaseMixed (Cchart p) v - 1‖ ≤ 1/2) →
        (∀ p m,
          let e := coordinateSplit (f.chart p).index
          let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
          cNorm (closedBall (z.1, z) (f.chart p).targetRadius) m (twoTimePhase (Cchart p)) ≤
            (f.chart p).phaseCost m * (1+cNorm (closedBall x RQ) (m+1) Q)) →
        let Ψoriginal := fun p ↦ curriedExtend (f.chart p).radialSection (twoTimePhase (Cchart p))
        ∃ Ψ : f.centers → TwoTimePhase d, ∃ g : f.centers → ℝ → E → E → E,
          (∀ p, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ p))) ∧
          (∀ p, ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (Ψ p)) (Ua p)) ∧
          (∀ p, ∀ η v, (v, η) ∈ Ua p → ∀ k, 1 ≤ k →
            ‖iteratedFDeriv ℝ (k+1) (fun w : ℝ × ℝ × Euclidean d ↦
              Ψ p w.1 w.2.1 w.2.2 η) v‖ ≤ ‖η‖ * Pbase k * L ^ k) ∧
          (∀ p, ∀ w ∈ Ua p, SymbolBudgets.jointPhase (Ψ p) =ᶠ[𝓝 w]
            SymbolBudgets.jointPhase (Ψoriginal p)) ∧
          (∀ ρ : ℝ, 1 ≤ ρ → ∀ p (mi mo : LocalizerSymbol (d+1)) u y,
            ∀ w ∈ elapsedOutputJetCarrier (tsupport (θ p) ×ˢ Kg p) mi mo u y,
              SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ p)) =ᶠ[𝓝
                (elapsedJointCoordinates w)] SymbolBudgets.jointPhase (Ψoriginal p)) ∧
          (∀ ρ : ℝ, 1 ≤ ρ → ∀ p (mi mo : LocalizerSymbol (d+1)) u y,
            ∀ w ∈ elapsedOutputJetCarrier (tsupport (θ p) ×ˢ Kg p) mi mo u y, ∀ j,
              ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
                (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ p)))) (elapsedJointCoordinates w)‖ ≤
                  P₀ j * L ^ j) ∧
          (∀ p (b : TwoTimeAmplitude d q), ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), ∀ u z ξ,
            elapsedAmplitude b (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) r u z ξ ≠ 0 →
            elapsedPhase (Ψ p) r u ξ = elapsedPhase (Ψoriginal p) r u ξ) ∧
          (∀ p, ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4),
            ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase (Ψ p) r)) (Vphase p)) ∧
          (∀ p, ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), ∀ u ξ, (u, ξ) ∈ Vphase p →
            fderiv ℝ (fun v ↦ elapsedPhase (Ψ p) r v ξ) u = innerSL ℝ (g p r u ξ)) ∧
          ∀ p, ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), ∀ u ξ, (u, ξ) ∈ Vphase p →
            c*‖ξ‖ ≤ ‖g p r u ξ‖ ∧ ‖g p r u ξ‖ ≤ C*‖ξ‖ := by
  classical
  obtain ⟨c, C, hc, hC, hcomparison⟩ := exists_selected_elapsed_covector_comparison f A hA
  refine ⟨c, C, hc, hC, ?_⟩
  intro output ho hoc hout threshold hthreshold a₀ b₀ ha₀ Kg hKg hglobal θ hθ hθbuffer
  obtain ⟨Kphase, hKphase, hpos, hmap, hjet⟩ := exists_selected_normalized_phase_carriers
    f hρb hsrcρ output hout threshold hthreshold c C a₀ b₀ ha₀ Kg hKg hglobal θ hθ hθbuffer
  obtain ⟨P₀, Pbase, hP₀, hPbase, hprofiles⟩ :=
    exists_selected_smooth_auxiliaryPhase_profiles f Kphase hKphase hpos hmap A hA
  have hgeom p := exists_selected_elapsed_physical_carriers (q := q)
    f p (hρb p) (hsrcρ p) output ho hoc hout
  choose Vphase Ua hVopen hUaopen hV hUa hcollar hphysicalMap hcar using hgeom
  choose Kphysical hKphysical hKV hphysical hcarrier using fun p ↦ hcar p threshold hthreshold
  have hdomain p w (hw : w ∈ Ua p) : budgetCoordinates w ∈
      domain (f.chart p).radialSection
        (closedBall (((coordinateSplit (f.chart p).index x).1),
          ((coordinateSplit (f.chart p).index x).1,
            ((coordinateSplit (f.chart p).index x).2, (coordinateSplit (f.chart p).index p.val.val).2)))
          (f.chart p).targetRadius) := by
    have hm := hUa p hw
    have hε := retainedRadius_bounds (f.chart p).targetRadius_pos (f.chart p).bufferRadius_pos
    refine ⟨hm.2.1, ?_⟩
    apply closedBall_subset_closedBall hε.2.1
    apply localPatch_bufferedBase_subset
      (((coordinateSplit (f.chart p).index x).1),
        ((coordinateSplit (f.chart p).index x).2, (coordinateSplit (f.chart p).index p.val.val).2))
      (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)
    exact ⟨hm.1, ball_subset_ball (by linarith [hε.1]) hm.2.2⟩
  refine ⟨P₀, Pbase, hP₀, hPbase, Vphase, Ua, Kphysical, hVopen, hUaopen,
    hKphysical, hKV, hUa, hcollar, hphysical, hcarrier, ?_⟩
  intro Rstar hRstar L hL Q hQ h Φ Cchart hs hbuffer hdiff hnear hphase Ψoriginal
  obtain ⟨Ψ, hΨ, he, hn, hgrade, hbase⟩ := hprofiles Rstar (by omega) L hL Q hQ Cchart hs hbuffer hphase
  have heUa p w (hw : w ∈ Ua p) : SymbolBudgets.jointPhase (Ψ p) =ᶠ[𝓝 w]
      SymbolBudgets.jointPhase (Ψoriginal p) := he p w (hdomain p w hw) (Or.inr (hcollar p w hw))
  have hg p := hcomparison Rstar hRstar L hL Q hQ p (hρb p) (hsrcρ p)
    (h p) (Φ p) (Cchart p) (hbuffer p) (hs p) (hdiff p) (hnear p) (hphase p)
    (Ψ p) (Vphase p) (Ua p) (hV p) (hUa p) (hphysicalMap p) (heUa p)
  choose g hregular hdiffg hcomp using hg
  refine ⟨Ψ, g, hΨ, fun p ↦ (hΨ p).contDiffOn, ?_, heUa, ?_, ?_, ?_,
    hregular, hdiffg, hcomp⟩
  · intro p η v hv k _hk
    exact hbase p η v (hdomain p (v, η) hv) (hcollar p (v, η) hv) k
  · intro ρ hρ p mi mo u y w hw
    exact hn ρ hρ p _ (hjet p mi mo u y hw)
  · intro ρ hρ p mi mo u y w hw j
    exact (hgrade ρ hρ p _ (hjet p mi mo u y hw) j).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le j 1)) (hP₀ j))
  · intro p b r hr u z ξ hnonzero
    have ho' : endpointOutputMask f p output u ≠ 0 := by
      intro hz
      exact hnonzero (elapsedAmplitude_eq_zero_of_mask b _ _ _ r u z ξ (Or.inl hz))
    have hi' : chartInputMask f p z ≠ 0 := by
      intro hz
      exact hnonzero (elapsedAmplitude_eq_zero_of_mask b _ _ _ r u z ξ (Or.inr (Or.inl hz)))
    have hβ : selectedEndpointMultiplier f p threshold ξ ≠ 0 := by
      intro hz
      exact hnonzero (elapsedAmplitude_eq_zero_of_mask b _ _ _ r u z ξ (Or.inr (Or.inr hz)))
    have hw := hphysical p r hr ξ (subset_tsupport _ hβ) (u, z)
      ⟨subset_tsupport _ ho', subset_tsupport _ hi'⟩
    have heq := (heUa p _ hw).eq_of_nhds
    simp only [SymbolBudgets.elapsedPoint_eq, SymbolBudgets.jointPhase] at heq
    change (u 0-r)*ξ 0 + _ = (u 0-r)*ξ 0 + _
    exact congrArg (fun a ↦ (u 0-r)*ξ 0+a) heq

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
