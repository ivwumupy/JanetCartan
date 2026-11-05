module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SupportedMaskProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets

/-!
# The three selected PDO profiles on the complete-residual carrier

Assemble the actual source, upper endpoint and differentiated algebraic
symbols into the `AmplitudeProfiles` consumed chartwise by `CompleteFactor`.
Keep the orders `0, -1, -1`, then prove their common order-zero domination.
The profiles and all offsets precede the coefficients, slow scale, source
frequency and accuracy. The two localizer profiles use the supplied common joint bound, before
the masks vary; the shell-cutoff profiles are filled by the consumer's
`comparableAmplitudeProfiles`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual ResidualLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open RegularSector.Characteristic.ConicPhase
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.FinitePdo.RetainedConstruction
open FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

/-- Apply the actual source, endpoint and full algebraic symbol producers
with the common proof-mask profile chosen before the varying masks and fields.
The same original coefficients, doubled threshold and literal orientations
are retained; both the natural orders and their common order-zero bounds are
proved. `selected_even_uniform_localizer_grades` supplies the exact mask input.
Consumer: uniform supported complete-residual leakage
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_threePDO_grades_of_joint_localizer_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hball : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) {a b : ℝ} (ha : 0 < a)
    (Hmask : ℕ → ℝ) (hHmask : ∀ j, 0 ≤ Hmask j) :
    let Kb := fun p ↦ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)
    let Kpdo := fun p ↦ comparableJointCarrier 1 1 a b
      ((Prod.fst '' Kb p) ×ˢ frequencyAnnulus
        (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      (Kb p) (frequencyAnnulus a b)
    ∃ Dpdo : Fin 3 → AmplitudeProfiles,
      (∀ j, (Dpdo j).symbolOffset = 0 ∧ (Dpdo j).inputMaskOffset = 0 ∧
        (Dpdo j).outputMaskOffset = 0 ∧ (Dpdo j).offset = 0) ∧
      ∀ (mi mo : f.centers → LocalizerSymbol (d+1)),
      (∀ p, ContDiff ℝ ∞ (mi p)) → (∀ p, ContDiff ℝ ∞ (mo p)) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mi p) z‖ ≤ Hmask j) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mo p) z‖ ≤ Hmask j) →
      (∀ L : ℝ, 1 ≤ L → ∀ p j y k (v : V),
        ‖iteratedFDeriv ℝ k (fun w : V ↦ (mi p (y, w.2.2.1) : ℂ)) v‖ ≤
          (Dpdo j).inputMask k * L ^ (k + (Dpdo j).inputMaskOffset)) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p j x ζ k,
        ‖iteratedFDeriv ℝ k (fun t ↦ mo p (t, ζ)) x‖ ≤
          (Dpdo j).outputMask k * L ^ (k + (Dpdo j).outputMaskOffset)) ∧
      ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ m, cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rstar)) →
        (∀ m, cNorm (closedBall x RQ) m B ≤ AQ m * L ^ (m-Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p 1))) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p backward,
      let cP := directPDOSymbols
        (fun y idx ↦ (coefficient (f.chart p).index Q y idx).map Complex.ofReal)
        (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) (W p 1)
        (conicBminus (f.chart p).radialSection (f.chart p).index Q
          (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
          (f.chart p).row (f.chart p).col)
        (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
          (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold)
      let Ap := fun j : Fin 3 ↦ orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p) (cP (![1, 2, 3] j))
      (∀ j,
        (∀ k v, v ∈ Kpdo p →
          ‖iteratedFDeriv ℝ k (fun w : V ↦ Ap j w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
            ρ ^ (![(0 : ℝ), -1, -1] j) * (Dpdo j).symbol k *
              L ^ (k + (Dpdo j).symbolOffset)) ∧
        (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb p, ∀ k,
          ‖iteratedFDeriv ℝ k (fun w : E × E ↦ Ap j w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low l)) ^ (![(0 : ℝ), -1, -1] j) * (Dpdo j).symbol k *
              L ^ (k + (Dpdo j).symbolOffset))) ∧
      (∀ j k v, v ∈ Kpdo p →
        ‖iteratedFDeriv ℝ k (fun w : V ↦ Ap j w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ ^ (0 : ℝ) * (Dpdo j).symbol k * L ^ (k + (Dpdo j).symbolOffset)) ∧
      (∀ j low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb p, ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦ Ap j w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low l)) ^ (0 : ℝ) * (Dpdo j).symbol k *
            L ^ (k + (Dpdo j).symbolOffset)) := by
  classical
  intro Kb Kpdo
  obtain ⟨Ds, hDs, hs⟩ := exists_selected_source_completeFactor_grades f threshold ht hft
    output ho hoc hout (b := b) ha
  obtain ⟨De, hDe, he⟩ := exists_selected_endpoint_completeFactor_grades f hΩ hball
    threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage cost hcost AQ hAQ (b := b) ha
  obtain ⟨Da, hDa, halg⟩ := exists_selected_algebraic_joint_grades f hΩ hRQ hball hc hdom
    threshold hft output ho hoc hout a b ha AQ hAQ
  let Dpdo : Fin 3 → AmplitudeProfiles := fun j ↦ {
    symbol := ![Ds, De, Da] j
    graphCutoff := fun _ ↦ 0
    outputCutoff := fun _ ↦ 0
    inputMask := Hmask
    outputMask := Hmask
    symbol_nonneg := by fin_cases j <;> assumption
    graphCutoff_nonneg := fun _ ↦ le_rfl
    outputCutoff_nonneg := fun _ ↦ le_rfl
    inputMask_nonneg := hHmask
    outputMask_nonneg := hHmask
    symbolOffset := 0
    graphCutoffOffset := 0
    outputCutoffOffset := 0
    inputMaskOffset := 0
    outputMaskOffset := 0 }
  refine ⟨Dpdo, fun _ ↦ ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  intro mi mo hi hom hmi hmo
  refine ⟨?_, ?_, ?_⟩
  · intro L hL p j y k v
    exact (selected_localizer_slices_le_joint_profile (mi p) (hi p) Hmask hHmask (hmi p) hL).1 k y v
  · intro L hL p j x ζ k
    exact (selected_localizer_slices_le_joint_profile (mo p) (hom p) Hmask hHmask (hmo p) hL).2.2.2 k x ζ
  intro Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp Φ C angular J W hW hWp p backward cP Ap
  have hcP : cP = ![selectedAlgebraicSymbol f p (2*threshold) Q B 0,
      selectedSourceSymbol f p (2*threshold), selectedEndpointSymbol f p threshold Q (W p 1),
      selectedAlgebraicSymbol f p (2*threshold) Q B 1] :=
    selected_directPDOSymbols_eq_four_selected_symbols f p threshold Q B (W p 1)
  have hsource := hs L ρ hL hρ p backward
  have hendpoint := he Rstar hR L ρ hL hρ Q B hQ hQp hBp Φ C angular hW hWp p backward
  have halgebraic := halg Rstar (by omega) L ρ hL hρ Q B hQ hB hQr hQp hBp p backward
  have hgrades : ∀ j,
      (∀ k v, v ∈ Kpdo p →
        ‖iteratedFDeriv ℝ k (fun w : V ↦ Ap j w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ ^ (![(0 : ℝ), -1, -1] j) * (Dpdo j).symbol k * L ^ (k + (Dpdo j).symbolOffset)) ∧
      (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb p, ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦ Ap j w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low l)) ^ (![(0 : ℝ), -1, -1] j) * (Dpdo j).symbol k *
            L ^ (k + (Dpdo j).symbolOffset)) := by
    intro j
    dsimp only [Ap]
    rw [hcP]
    fin_cases j
    · exact ⟨fun k v hv ↦ hsource.1 v hv k, hsource.2⟩
    · exact ⟨fun k v hv ↦ hendpoint.1 v hv k, hendpoint.2⟩
    · exact halgebraic
  have horder (j : Fin 3) : ![(0 : ℝ), -1, -1] j ≤ 0 := by fin_cases j <;> norm_num
  have hdominate (r : ℝ) (hr : 1 ≤ r) (j : Fin 3) (k : ℕ) :
      r ^ (![(0 : ℝ), -1, -1] j) * (Dpdo j).symbol k * L ^ (k + (Dpdo j).symbolOffset) ≤
        r ^ (0 : ℝ) * (Dpdo j).symbol k * L ^ (k + (Dpdo j).symbolOffset) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hr (horder j)) ((Dpdo j).symbol_nonneg k))
      (pow_nonneg (zero_le_one.trans hL) _)
  exact ⟨hgrades, fun j k v hv ↦ ((hgrades j).1 k v hv).trans (hdominate ρ hρ j k),
    fun j low l ξ hξ z hz k ↦ ((hgrades j).2 low l ξ hξ z hz k).trans
      (hdominate _ (le_max_left _ _) j k)⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
