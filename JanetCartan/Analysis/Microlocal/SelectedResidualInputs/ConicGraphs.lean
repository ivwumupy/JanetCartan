module

public import JanetCartan.Analysis.Microlocal.SelectedResidualInputs.SupportedPhase
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Measurability

/-!
# Original conic graph inputs on the selected common masks

Apply the existing graph producer and retain its actual regularizations and
common-mask uniqueness statement. The original conic phase is used throughout
both graph realizations and strong limits, with the full physical residual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedResidualInputs
open SelectedLocalization
open RegularSector RegularSector.FiniteResidual.SelectedChart RegularSector.FinitePdo
open Characteristic Characteristic.AmplitudeBounds Characteristic.ConicPhase
open Characteristic.ConicAmplitude Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FourierIntegral.LowBounds FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution
open FiniteEvolution.PhysicalCutoff
open JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- Put the selected common regularizations on the original conic phase and
prove their measurability, retaining the SAME operators, complete elapsed
interval and literal adjoints. All hypotheses are exact certificates of the
supplied-family protected direct constructor. This implication is consumed by
its actual residual-input application and then by
`exists_directResidual_integral_fourier_bound_of_primitive_grades`
(`app:ch_regular_base:eq:energy-complete-residual`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_common_conic_graph_regularizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold) (angular : Euclidean d → ℝ)
    (hang : ContDiff ℝ ∞ angular)
    (hplateau : ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*threshold)
      (physicalCoordinates (f.chart p).index ξ) : ℂ)),
      conicMask angular =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ))
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output)
    (houtputCompact : HasCompactSupport output)
    (houtputSupport : tsupport output ⊆ ball x f.physicalRadius) :
    let c := f.chart p
    let z : Z := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat)
      (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
    closedBall (z.1, z) c.targetRadius ⊆ C.target →
    ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
    (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
    (∀ v ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1/2) →
    (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase C) ≤
      c.phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
    (∀ v ∈ C.target, (C.symm v).2.1 = v.2.1) →
    ∀ Fs : Fin 3 → T → CMat,
    (∀ j, ContDiff ℝ ∞ (Fs j)) →
    let W := fun j : Fin 3 ↦ collared c.radialSection (if j = 0 then 0 else 1) angular (Fs j)
    (∀ j, ContDiff ℝ ∞ (W j)) →
    (∀ j, tsupport (W j) ⊆ ConicPhase.domain c.radialSection
      (C.target ∩ C.symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
        (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2))))) →
    (∀ v : T, c.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
      (fun k ↦ W 2 v k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit c.index) v.2.1 v.2.2.2 y) k j)
          ((coordinateSplit c.index).symm (v.1, v.2.2.1))) →
    ∀ G : T → ℝ, ContDiff ℝ ∞ G →
    (∀ v ∈ tsupport (W 0) ∪ tsupport (W 1), G =ᶠ[𝓝 v] ConicPhase.phase c.radialSection C) →
    (∀ v : T, c.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → W 2 v ≠ 0 →
      G =ᶠ[𝓝 v] ConicPhase.phase c.radialSection C) →
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*threshold) (physicalCoordinates c.index ξ) : ℂ)
    let ΨG := fun t s y η ↦ G (t, (s, (y, η)))
    let Ψ := curriedExtend c.radialSection (twoTimePhase C)
    let b := directRetardedAmplitudes (fun y i ↦ (coefficient c.index Q y i).map Complex.ofReal)
      (fun y ↦ (zeroth c.index B y).map Complex.ofReal)
      (curryCharacteristicMatrix (W 0)) (curryCharacteristicMatrix (W 1))
    (∀ j : Fin 2, ∀ t s y η, s ≤ z.1-c.maskRadius/2 →
      W (Fin.castLE (by decide) j) (t, (s, (y, η))) = 0) ∧
    ∃ D : Bool → ℝ, ∃ Treg : Bool → ℕ → ℝ → H →L[ℂ] H,
      (∀ k r, r ∈ Icc 0 (3*c.maskRadius/4) →
        ‖elapsedGraph Ψ (b k) (endpointOutputMask f p output) (chartInputMask f p) β r‖ ≤ D k) ∧
      (∀ k j r, r ∈ Icc 0 (3*c.maskRadius/4) → ‖Treg k j r‖ ≤ D k) ∧
      (∀ k j r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u : graphTestSpace (d+1) (d+1),
        Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j)
            (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β r)) u) ∧
      (∀ k j r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u : graphTestSpace (d+1) (d+1),
        (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (reverseGraphOperator (elapsedPhase Ψ r)
            (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
              (fun x y ξ ↦ (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β r x y ξ).conjTranspose))
            (fun x ↦ (u.val x).ofLp) y)) ∧
      (∀ k r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u, Tendsto (fun j ↦ Treg k j r u) atTop
        (𝓝 (elapsedGraph Ψ (b k) (endpointOutputMask f p output) (chartInputMask f p) β r u))) ∧
      (∀ k r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u, Tendsto (fun j ↦ (Treg k j r).adjoint u) atTop
        (𝓝 ((elapsedGraph Ψ (b k) (endpointOutputMask f p output) (chartInputMask f p) β r).adjoint u))) ∧
      (∀ k j u, AEStronglyMeasurable (fun t ↦ Treg k j t u)
        (volume.restrict (Icc 0 (3*c.maskRadius/4))) ∧
        AEStronglyMeasurable (fun t ↦ (Treg k j t).adjoint u)
          (volume.restrict (Icc 0 (3*c.maskRadius/4)))) ∧
      ∃ Op : Bool → H →L[ℂ] H,
        (∀ k, ‖Op k‖ ≤ (3*c.maskRadius/4) * D k) ∧
        (∀ k u, Op k u = elapsedGraphIntegral (3*c.maskRadius/4)
          (curriedExtend c.radialSection (twoTimePhase C)) (b k)
          (endpointOutputMask f p output) (chartInputMask f p) β u) ∧
        (∀ k u, (Op k).adjoint u = ∫ r in Icc 0 (3*c.maskRadius/4),
          (elapsedGraph (curriedExtend c.radialSection (twoTimePhase C)) (b k) (endpointOutputMask f p output) (chartInputMask f p) β r).adjoint u) ∧
        (∀ k (u : graphTestSpace (d+1) (d+1)), Op k (graphTestToLp u) =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (retardedPhysicalIntegral ΨG (b k) (endpointOutputMask f p output)
            (chartInputMask f p) β (chartPhysicalMasks_properties f p).2.1
            (z.1-c.maskRadius/2) u y)) ∧
        ∀ (k : Bool) (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
          (o : ℕ) (A : ℝ) (As : ℕ → ℝ) (retained : H →L[ℂ] H),
          RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4)
            (z.1-c.maskRadius/2) ΨG (b k) χout χsource β hs o A As retained →
        ∀ (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
          (∀ y, (output y : ℂ) * χout ((physicalCoordinates c.index).symm y) = (output y : ℂ)) →
          (∀ y, χsource ((physicalCoordinates c.index).symm y) *
            (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) →
          let e := physicalCoordinates c.index
          let Mo := sourceCutMultiplier (r := d+1) (output ∘ e)
            (houtput.continuous.comp e.continuous) (fun y ↦ hob (e y))
          let Mi := sourceCutMultiplier (r := d+1) (f.inputMask ∘ e)
            (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ hib (e y))
          Mo.comp (retained.comp Mi) = Op k ∧
            Mi.comp (retained.adjoint.comp Mo) = (Op k).adjoint := by
  classical
  intro c z Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs hFs W hWs hsupport
    hphysical G hGsmooth hG hGres β ΨG Ψ b
  obtain ⟨hzero, D, Treg, hlow, hbound, hreal, hrealAdj, hlim, hlimAdj,
    Op, hnorm, hintegral, hadjoint, htest, hsame⟩ :=
    exists_selected_common_graph_regularizations f p hρb hsrcρ threshold hthreshold angular
      hang hplateau output houtput houtputCompact houtputSupport Q B h Φ C hbuffer hsmooth
      hdiff hnear hphase hsourceTime Fs hFs hWs hsupport hphysical G hG hGres
  have hm := selected_common_regularizations_aestronglyMeasurable f p hρb hsrcρ threshold
    output houtput houtputCompact houtputSupport Q B W hWs hphysical G hGsmooth
    (3*c.maskRadius/4) Treg hreal hrealAdj
  have he := directRetardedAmplitudes_phase_eq_of_supported_germ
    (fun y i ↦ (coefficient c.index Q y i).map Complex.ofReal)
    (fun y ↦ (zeroth c.index B y).map Complex.ofReal) (W 0) (W 1)
    (ConicPhase.phase c.radialSection C) G hG
    (endpointOutputMask f p output) (chartInputMask f p) β
  have hgraph k t : elapsedGraph ΨG (b k) (endpointOutputMask f p output) (chartInputMask f p) β t =
      elapsedGraph Ψ (b k) (endpointOutputMask f p output) (chartInputMask f p) β t :=
    FourierIntegral.FullLowBounds.fullGraphOperator_phase_congr _ _ _ (he k t)
  have hforward k j t :
      graphTestOutput (elapsedPhase ΨG t) (frequencyCutFullAmplitude (complexPhysicalCutoff j)
        (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β t)) =
      graphTestOutput (elapsedPhase Ψ t) (frequencyCutFullAmplitude (complexPhysicalCutoff j)
        (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β t)) :=
    graphTestOutput_phase_congr _ _ _ (fun u v ξ h ↦ he k t u v ξ
      (fun hz ↦ h (by
        change elapsedAmplitude (b k) (endpointOutputMask f p output)
          (chartInputMask f p) β t _ _ _ = 0 at hz
        simp only [frequencyCutFullAmplitude, hz, smul_zero])))
  have hreverse k j t (u : E → Fin (d+1) → ℂ) :
      reverseGraphOperator (elapsedPhase ΨG t)
        (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
          (fun x y ξ ↦ (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β t x y ξ).conjTranspose)) u =
      reverseGraphOperator (elapsedPhase Ψ t)
        (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
          (fun x y ξ ↦ (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β t x y ξ).conjTranspose)) u :=
    FourierIntegral.reverseGraphOperator_phase_congr _ _ _ (fun x y ξ h ↦ he k t x y ξ
      (fun hz ↦ h (by
        change elapsedAmplitude (b k) (endpointOutputMask f p output)
          (chartInputMask f p) β t _ _ _ = 0 at hz
        simp only [frequencyCutFullAmplitude, hz, Matrix.conjTranspose_zero, smul_zero]))) u
  refine ⟨hzero, D, Treg, ?_, hbound, ?_, ?_, ?_, ?_, hm,
    Op, hnorm, hintegral, hadjoint, htest, hsame⟩
  · intro k t ht
    rw [← hgraph k t]
    exact hlow k t ht
  · intro k j t ht u
    rw [← hforward k j t]
    exact hreal k j t ht u
  · intro k j t ht u
    exact (hrealAdj k j t ht u).trans (Filter.Eventually.of_forall fun y ↦
      congrArg (fun v : E → Fin (d+1) → ℂ ↦ WithLp.toLp 2 (v y))
        (hreverse k j t (fun x ↦ (u.val x).ofLp)))
  · intro k t ht u
    rw [← hgraph k t]
    exact hlim k t ht u
  · intro k t ht u
    rw [← hgraph k t]
    exact hlimAdj k t ht u

end JanetCartan.ArbitraryAccuracy.SelectedResidualInputs
