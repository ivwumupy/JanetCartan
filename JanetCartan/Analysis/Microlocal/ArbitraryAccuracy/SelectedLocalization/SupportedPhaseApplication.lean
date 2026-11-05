module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhaseInputs
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualCollar

/-!
# Actual phase profiles and collars on the retained residual carrier

Both normalized and physical phase grades use one constructed smooth auxiliary.
Its supported germs instantiate the noncomparable geometry. The actual local
phase and its retained quantitative certificates are the only analytic inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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

open SelectedEvenProofMasks ProtectedMasks JanetCartan.Localization
open Characteristic.ConicAmplitude Characteristic.ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open FiniteChain.Graph.PhysicalShells.Noncomparable
local notation "Mat" => MetricTensor (d+1)
local notation "V" => ℝ × JointVariables E

/-- Apply the actual elapsed phase producer and the actual even residual collar
producer on the SAME retained charts. The compact carrier is the literal
`selectedRetainedResidualCarrier`; both normalized germs and all phase jets
are restricted from the original elapsed carrier. The same radial witnesses
also retain the actual amplitude and all output-jet support inclusions, so no
second existential choice of radii is needed. The auxiliary phase is chosen
once and retained through both physical orientations and every nested mask pair.
The collar constants precede the varying coefficients, their original phase
certificates, and all frequencies. The only phase hypotheses are the retained
construction certificates supplied by
`SelectedResidualInputs.exists_finite_selected_residual_primitive_inputs`.
Consumer: the phase/collar arguments of
`exists_selectedCompletePhysicalError_restriction_bound_of_supported_collars`
(`app:ch_regular:eq:high-phase`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_supported_elapsed_phase_inputs
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ a₀ b₀ : ℝ, 0 < a₀ →
      ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ θ : f.centers → ℝ → ℂ, (∀ p, HasCompactSupport (θ p)) →
      (∀ p, tsupport (θ p) ⊆ ball 0
        (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)) →
      let Kg := fun p ↦ selectedResidualComparableCarrier f p output threshold c C a₀ b₀
      let Kjet := fun p ↦ selectedRetainedResidualCarrier f p output threshold c C a₀ b₀
        (θ p) (ra p) (rb p) tlo thi
      (∀ p, IsCompact (Kg p)) ∧ (∀ p, IsCompact (Kjet p)) ∧
      (∀ p, Kjet p ⊆ tsupport (θ p) ×ˢ Kg p) ∧
      (∀ p (Q : E → Fin (d+1) → Mat) (B : E → Mat)
        (Φ : Z × ℝ → Z) (Cchart : OpenPartialHomeomorph T T) (angular : Euclidean d → ℝ),
      let lc := f.chart p
      let e := coordinateSplit lc.index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      let Fs := selectedBufferedAmplitude f p Q B Φ Cchart
      let W := fun j : Fin 3 ↦ collared lc.radialSection (if j=0 then 0 else 1) angular (Fs j)
      let Aoriginal := fun y i ↦ (coefficient lc.index Q y i).map Complex.ofReal
      let Boriginal := fun y ↦ (zeroth lc.index B y).map Complex.ofReal
      let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
      let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
      let b := directRetardedAmplitudes Ac Bc
        (selectedConicAmplitude f p Q B Φ Cchart angular 0)
        (selectedConicAmplitude f p Q B Φ Cchart angular 1) true
      let borig := directRetardedAmplitudes Aoriginal Boriginal
        (selectedConicAmplitude f p Q B Φ Cchart angular 0)
        (selectedConicAmplitude f p Q B Φ Cchart angular 1) true
      (∀ η ∈ tsupport angular, 0 < lc.radialSection η) →
      (∀ j, ContDiff ℝ ∞ (W j)) →
      (∀ v : T, lc.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W 1 (physicalSlice e v.2.1 v.2.2.2 y) k j)
            (e.symm (v.1, v.2.2.1))) →
      (∀ v ∈ Cchart.target, (Cchart.symm v).2.1 = v.2.1) →
      tsupport (Fs 2) ⊆ closedBall (z.1, z) (lc.bufferRadius/2) →
      tsupport (W 2) ⊆ ConicPhase.domain lc.radialSection
        (Cchart.target ∩ Cchart.symm ⁻¹' (ball z.1 (lc.maskRadius/2) ×ˢ
          (ball z.1 (lc.maskRadius/2) ×ˢ ball z.2 (lc.maskRadius/2)))) →
      (∀ r, elapsedAmplitude b (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointMultiplier f p threshold) r =
        elapsedAmplitude borig
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointMultiplier f p threshold) r) ∧
      ∀ (mi mo : LocalizerSymbol (d+1)) (Ki : Set E),
        tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a₀ b₀ →
        ∀ (backward : Bool) ρ, 1 ≤ ρ → ∀ low j k,
        IsComparablePair c C a₀ b₀ ρ low j k → ∀ y,
          tsupport (fun v : V ↦ (θ p) v.1 • jointElapsedAmplitude backward ρ b
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) mi (fun _ ↦ 0)
            (graphBranchCutoff low j) (outputCutoff k) 0 y v) ⊆ Kjet p ∧
          ∀ (Ψ Ψorig : TwoTimePhase d) x', ContDiff ℝ ∞ mo → ∀ m (v : Fin m → E),
            cutElapsedOutputJetAmplitude backward ρ Ψ b
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) (θ p) x' y m v =
            cutElapsedOutputJetAmplitude backward ρ Ψorig borig
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) (θ p) x' y m v ∧
            ∀ D, tsupport (iteratedFDeriv ℝ D (cutElapsedOutputJetAmplitude backward ρ Ψorig borig
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) (θ p) x' y m v)) ⊆
              elapsedOutputJetCarrier (Kjet p) mi mo x' y) ∧
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
        ∀ {ι κ : Type*} [Fintype ι] [Fintype κ],
        ∀ (eT : Module.Basis ι ℝ (JointVariables E))
          (eI : Module.Basis κ ℝ (ℝ × JointVariables E)),
        ∀ (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E)) (Γ : Set E)
          (N : ℕ) (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
          (hcRad : ∀ p k, 0 < cRad p k) (Urad : (p : f.centers) → Fin (n p) → Set Z)
          (buffer Rbase εcollar δT δI : ℝ) (Hmask Hcollar : ℕ → ℝ),
        0 < εcollar → 0 < δT → 0 < δI →
        ∀ χ : (ℝ × JointVariables E) → ℂ, ContDiff ℝ ∞ χ →
        (∀ v, |v.1| ≤ εcollar / 4 → χ v = 1) →
        tsupport χ ⊆ {v | |v.1| ≤ εcollar / 2} →
        (∀ j v, ‖iteratedFDeriv ℝ j χ v‖ ≤ Hcollar j) →
        ∀ ψ : f.centers → E → ℝ, (∀ p, HasCompactSupport (ψ p)) →
        ∃ (δT' δI' G : f.centers → ℝ),
          (∀ p, 0 < δT' p) ∧ (∀ p, 0 < δI' p) ∧
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
          (∀ p, ∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), ∀ u ξ, (u, ξ) ∈ Vphase p →
            c*‖ξ‖ ≤ ‖g p r u ξ‖ ∧ ‖g p r u ξ‖ ≤ C*‖ξ‖) ∧
          ∀ (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
            N (fun p ↦ ra p / thi) (fun p ↦ ra p / tlo) n cRad hcRad Urad
            buffer a₀ b₀ Rbase εcollar δT δI Hmask Q Φ Cchart) (k : Fin N),
          let masks := hEven.choose_spec.choose
          let mi := fun p ↦ canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k.castSucc)
          let mo := fun p ↦ canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k.succ)
          ∀ (ρ : ℝ), 1 ≤ ρ →
          ∃ UT UI : f.centers → Bool → E → E → Set (ℝ × JointVariables E),
            0 < εcollar / 4 ∧ ContDiff ℝ ∞ χ ∧
            (∀ v, |v.1| < εcollar / 4 → χ v = 1) ∧
            ∀ p backward, ∀ u ∈ tsupport (ψ p), ∀ y ∈ Prod.fst '' tsupport (mi p),
              let F := jointElapsedPhase backward (normalizedTwoTimePhase ρ (Ψ p)) u y
              let Kxy := elapsedOutputJetCarrier (Kjet p) (mi p) (mo p) u y
              IsOpen (UT p backward u y) ∧ IsOpen (UI p backward u y) ∧
              Kxy ∩ tsupport χ ⊆ UT p backward u y ∧
              (Kxy ∩ tsupport (1 - χ)) ∩ {v | 0 < v.1} ⊆ UI p backward u y ∧
              (∀ r, 0 ≤ r → ∀ v, (r, v) ∈ UT p backward u y →
                δT' p ≤ phaseGradientSquare eT (fun w ↦ F (r, w)) v ∧
                ‖fderiv ℝ F (r, v)‖ ≤ G p) ∧
              (∀ v ∈ UI p backward u y ∩ {v | 0 < v.1},
                δI' p ≤ phaseGradientSquare eI F v ∧ ‖fderiv ℝ F v‖ ≤ G p) ∧
              (∀ v ∈ Kxy, ∀ j, ‖iteratedFDeriv ℝ j χ v‖ ≤ Hcollar j) ∧
              (∀ v ∈ Kxy, ∀ j,
                ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
                  (normalizedTwoTimePhase ρ (Ψ p)))) (elapsedJointCoordinates v)‖ ≤ P₀ j * L ^ j)
 := by
  classical
  obtain ⟨c, C, hc, hC, hphases⟩ :=
    exists_selected_elapsed_phase_inputs (q := q) f hρb hsrcρ A hA
  refine ⟨c, C, hc, hC, ?_⟩
  intro a₀ b₀ ha₀
  obtain ⟨tlo, thi, hlo, hhi, hcarriers⟩ :=
    exists_selected_direct_residual_phase_carriers f hρb hsrcρ c C a₀ b₀ ha₀ ra rb hra hab
  refine ⟨tlo, thi, hlo, hhi, ?_⟩
  intro output ho hoc hout threshold ht θ hθ hθbuffer Kg Kjet
  have hcar p := hcarriers output ho hoc hout threshold ht (θ p) (hθ p)
  have hKg p : IsCompact (Kg p) := (hcar p).1 p
  have hKjet p : IsCompact (Kjet p) := (hcar p).2.2.1 p
  have hsub p : Kjet p ⊆ tsupport (θ p) ×ˢ Kg p := (hcar p).2.2.2.1 p
  refine ⟨hKg, hKjet, hsub, (fun p ↦ (hcar p).2.2.2.2.2 p), ?_⟩
  obtain ⟨P₀, Pbase, hP₀, hPbase, Vphase, Ua, Kphysical, hVphase, hUa,
    hKphysical, hKV, hUabuffer, hUapos, hphysicalMap, hcarrier, hphaseGrades⟩ :=
    hphases output ho hoc hout threshold ht a₀ b₀ ha₀ Kg hKg (fun _ ↦ rfl) θ hθ hθbuffer
  refine ⟨P₀, Pbase, hP₀, hPbase, Vphase, Ua, Kphysical, hVphase, hUa,
    hKphysical, hKV, hUabuffer, hUapos, hphysicalMap, hcarrier, ?_⟩
  intro ι κ _ _ eT eI χ₂ Ksource Vsource Γ N n cRad hcRad Urad
    buffer Rbase εcollar δT δI Hmask Hcollar hε hδT hδI χ hχ hχone hχsupp hχder ψ hψ
  have hcollar p := exists_selected_even_residual_collar_domains f p eT eI χ₂ Ksource Vsource Γ
    output N (fun p ↦ ra p / thi) (fun p ↦ ra p / tlo) n cRad hcRad Urad
    buffer a₀ b₀ Rbase εcollar δT δI Hmask hε hδT hδI χ Hcollar hχ hχone hχsupp hχder
    (ψ p) (hψ p) threshold c C ht hout (θ p) ra rb hlo (hra p) le_rfl le_rfl
    (hKjet p) P₀ hP₀
  choose δT' δI' G hδT' hδI' hcollars using hcollar
  refine ⟨δT', δI', G, hδT', hδI', ?_⟩
  intro Rstar hRstar L hL Q hQ h Φ Cchart hphase hbuffer hdiff hnear hphaseCost Ψoriginal
  obtain ⟨Ψ, g, hΨ, hΨon, hbase, hgerm, hnormalizedGerm, hnormalizedJets,
    hagree, hphysical, hg, hcomp⟩ :=
    hphaseGrades Rstar hRstar L hL Q hQ h Φ Cchart hphase hbuffer hdiff hnear hphaseCost
  refine ⟨Ψ, g, hΨ, hΨon, hbase, hgerm, hnormalizedGerm, hnormalizedJets,
    hagree, hphysical, hg, hcomp, ?_⟩
  intro hEven k masks mi mo ρ hρ
  have hjet p u y : elapsedOutputJetCarrier (Kjet p) (mi p) (mo p) u y ⊆
      elapsedOutputJetCarrier (tsupport (θ p) ×ˢ Kg p) (mi p) (mo p) u y :=
    fun _ hv ↦ ⟨hsub p hv.1, hv.2⟩
  have hdomains p := hcollars p Q Φ Cchart hEven k ρ L hρ hL (Ψ p) (hΨ p)
    (fun u _ y _ v hv _ ↦ hnormalizedGerm ρ hρ p (mi p) (mo p) u y v (hjet p u y hv))
    (fun u _ y _ v hv j ↦ hnormalizedJets ρ hρ p (mi p) (mo p) u y v (hjet p u y hv) j)
  choose UT UI hpositive hsmooth hone hdomains using hdomains
  refine ⟨UT, UI, by positivity, hχ, fun v hv ↦ hχone v hv.le, ?_⟩
  intro p backward u hu y hy F Kxy
  obtain ⟨hUT, hUI, hKT, hKI, hgapT, hgapI, hcut⟩ := hdomains p backward u hu y hy
  exact ⟨hUT, hUI, hKT, hKI, hgapT, hgapI, hcut,
    fun v hv j ↦ hnormalizedJets ρ hρ p (mi p) (mo p) u y v (hjet p u y hv) j⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
