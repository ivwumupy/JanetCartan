module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.EndpointInterface

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SelectedChart
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Masks

/-!
# Retained protection certificates for the finite direct construction

The same local root, masks and evolution are retained through this deduction.
Consumer: `exists_finite_direct_operator_bounds_with_protection_certificates`,
then `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open ActualCarriers Characteristic Characteristic.ResidualCoordinates
open Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.ConicAmplitude
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution RetainedConstruction
open Characteristic.AmplitudeBounds Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral.SymbolBudgets FourierIntegral LocalSobolev
open Characteristic.RetardedLocalization JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Construct the actual upper-endpoint PDO on the SAME finite family as the
algebraic terms. Every analytic input is discharged by the retained physical
evolution and its joint two-time amplitude budget. The output retains all
old phase, full-B, W₀/W₁/PW₁ and retarded conclusions together with the
endpoint certificate on their SAME witnesses. Source agreement and source
budgets use the same common masks. Constants precede Q, B and Sobolev order;
`sectorLowOrder` controls the fixed low requirement and the high reserve is
`2*(d+2)+11`. Final finite summation, full residual and real pairing belong to
the parent sector construction (`energy-complete-residual`,
`sector-theorem-residual`, `measured-adjoint`). -/
theorem exists_finite_physical_endpoint_pdos_with_protection_certificates_on_enlarged_bands
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {evolutionTime speedGap rootSize : f.centers → ℝ} {rootCost : f.centers → ℕ → ℝ}
    (hprotection : ∀ p, Characteristic.AlgebraicChart.LocalProtectionCertificate (f.chart p)
      (evolutionTime p) (speedGap p) (rootSize p) (rootCost p))
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hM : 0 ≤ M)
    (bandFloor bandCeiling : f.centers → ℝ) (hbandFloor : ∀ p, 0 < bandFloor p) :
    ∃ L : ℝ, 1 ≤ L ∧ f.radialThreshold ≤ L ∧ f.radialThreshold ≤ 2 * L ∧
    ∃ (angular : f.centers → Euclidean d → ℝ)
      (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        (∀ η, angular p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (angular p) ∧
        tsupport (angular p) ⊆ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius / 2) ∧
        (∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)) ∧
      (∀ p, ContDiff ℝ ∞ (χout p) ∧ HasCompactSupport (χout p) ∧
        HasCompactSupport (χsource p) ∧
        tsupport (χsource p) ⊆ (physicalCoordinates (f.chart p).index) ⁻¹' Ω ∧
        (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
          interior {y | χsource p y = 1} ∧
        (∀ y ∈ tsupport (χout p), (f.chart p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1))) ∧
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p, tsupport output ⊆ (physicalCoordinates (f.chart p).index).symm ⁻¹'
        interior {y | χout p y = 1}) ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) *
        χout p ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ)) ∧
      (∀ ζ : E, (∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ζ +
        FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1) ∧
      (∀ p y, endpointOutputMask f p output y * FiniteAlgebraic.chartOutputMask f p y =
        endpointOutputMask f p output y) ∧
      (∀ p y, endpointOutputMask f p output y * χout p y = endpointOutputMask f p output y) ∧
      (∀ p y, χsource p y * FiniteAlgebraic.chartInputMask f p y =
        FiniteAlgebraic.chartInputMask f p y) ∧
      (∀ p : f.centers, ∀ L' ≥ L,
        ∃ R > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
          FourierIntegral.GraphNormalAmplitudeBounds
            (Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
              (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
              (selectedSourceSymbol f p (2*L'))) R (C (2*(d+2))) ∧
          ∀ m ξ is, is.length ≤ m → ∀ z,
            ‖AmplitudeBound.matrixAmplitudeCoordinateDerivList is
              (Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
                (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
                (selectedSourceSymbol f p (2*L')) ξ) z‖ ≤ C m) ∧
      (∀ L' ≥ L, ∀ y ∈ closedBall x (4*f.physicalRadius), ∀ ζ : E,
        (∑ p, selectedSourceSymbol f p (2*L')
          ((physicalCoordinates (f.chart p).index).symm y)
          ((physicalCoordinates (f.chart p).index).symm ζ)) +
          (dilatedConicMask (fun η ↦ 1-∑ p, f.angularMask p η) (2*L') ζ : ℂ) •
            (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) +
          (FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
            ((2*L')⁻¹ • ζ) : ℂ) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) = 1) ∧
      ∀ p : f.centers,
        let Aref := A₀
        let evolutionTime := evolutionTime p
        let speedGap := speedGap p
        let rootSize := rootSize p
        let rootCost := rootCost p
        let angular := angular p
        let χout := χout p
        let χsource := χsource p
        let hs := hs p

    let lc := f.chart p
    let β := selectedEndpointMultiplier f p
    let e := coordinateSplit lc.index
    let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
    let ℓ := lc.radialSection
    ∀ L' ≥ L,
      (∀ ζ ∈ tsupport (β L'),
        conicMask angular =ᶠ[𝓝 (spatialPart ζ)] (fun _ ↦ 1)) ∧
      (selectedSourceSymbol f p (2*L') = fun y ζ ↦
        (conicSourceSymbol ℓ (conicMask angular) lc.sourceMask y (spatialPart ζ) * β L' ζ) •
          (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) ∧
    ∃ ra > (0 : ℝ), ∃ rb > ra,
      ra ≤ bandFloor p ∧ bandCeiling p ≤ rb ∧
      DiagonalFrequencyCoverage ℓ z.2.2 (lc.bufferRadius/2) ra rb (β L') ∧
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
    ∃ Rbox > (0 : ℝ), ∃ Dpdo Dgain Gain : ℕ → ℝ,
      (∀ m, 1 ≤ Dpdo m) ∧ (∀ m, 1 ≤ Dgain m) ∧ (∀ n, 0 ≤ Gain n) ∧
    ∃ A₀ > (0 : ℝ), ∃ A₁ > (0 : ℝ), ∃ A Bnd : ℕ → ℝ,
      (∀ s, 0 < A s) ∧ (∀ s, 0 < Bnd s) ∧
    ∃ H1 > (0 : ℝ),
    ∀ Q : E → Fin (d+1) → Mat, ContDiffOn ℝ ∞ Q Ω →
      MapsTo Q Ω (closedBall Aref lc.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
      let h := fieldRoot e Q lc.root
      let U := fieldDomain e Ω ℓ z.2.2 lc.coefficientRadius
      ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
        SelectedProtectionData lc evolutionTime speedGap rootSize rootCost Q Φ C ∧
        ContDiffOn ℝ ∞ h U ∧
        (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
        closedBall z lc.rootRadius ⊆ U ∧
        (∀ w ∈ closedBall z lc.rootRadius, (rootPencil e Q h w).det = 0 ∧
          lc.minorGap ≤ |(rootPencil e Q h w).adjugate lc.row lc.col| ∧
          lc.transportGap ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) lc.row lc.col|) ∧
        (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) lc.sourceRadius ∧
        ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) lc.targetRadius ⊆ C.target ∧
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
        (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
        (∀ q ∈ C.target,
          (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
          (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
        (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
          (twoTimeState Φ (C.symm q)).1 = q.1) ∧
        (∀ w ∈ ball z lc.sourceRadius, (w.1, w) ∈ C.target ∧
          C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
        (∀ q ∈ closedBall (z.1, z) lc.targetRadius, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
        (∀ m, cNorm (closedBall (z.1, z) lc.targetRadius) m (twoTimePhase C) ≤
          lc.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
        ball (z.1, z) lc.outerRadius ⊆ C.target ∧
        MapsTo C (closedBall (z.1, z) lc.maskRadius) (closedBall (z.1, z) (lc.bufferRadius / 2)) ∧
        ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
          let V := C.target ∩ C.symm ⁻¹' (ball z.1 (lc.maskRadius / 2) ×ˢ
            (ball z.1 (lc.maskRadius / 2) ×ˢ ball z.2 (lc.maskRadius / 2)))
          let Fs := fun j ↦ bufferedMatrix V lc.timeMask (pencilAmplitudeFamily lc.index Q B h Φ C lc.row lc.col lc.sourceMask j)
          let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
          let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
          ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
            (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
            (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
              tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
            (∀ p : T, lc.timeMask =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
              collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
            (∀ y : E, lc.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
              WKB.firstOrderApply
                (fun x idx ↦ ((coefficient lc.index Q x idx).map Complex.ofReal).mulVecLin)
                (fun x ↦ ((zeroth lc.index B x).map Complex.ofReal).mulVecLin)
                (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                  (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                  (fun k ↦ twoTimePhysicalApply (fun x idx ↦ (coefficient lc.index Q x idx).map Complex.ofReal)
                    (fun x ↦ (zeroth lc.index B x).map Complex.ofReal) W₁
                      (y 0) s (spatialPart y) η k j)) ∧
            (∀ y : E, lc.timeMask (y 0) = 1 → ∀ η,
              (coefficient lc.index Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                conicSourceSymbol ℓ (FiniteMasks.conicMask angular) lc.sourceMask y η •
                  projector lc.index Q h lc.row lc.col y ((ℓ η)⁻¹ • η)) ∧
          (∃ Solver Residual : SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
            RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*lc.maskRadius/4)
              (z.1-lc.maskRadius/2) (fun t s y η ↦ G (t, (s, (y, η))))
              (W₀ + W₁) χout χsource
              (β L')
              hs 0 A₀ A Solver ∧
            RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*lc.maskRadius/4)
              (z.1-lc.maskRadius/2) (fun t s y η ↦ G (t, (s, (y, η))))
              (curryCharacteristicMatrix (collared ℓ 1 angular (Fs 2))) χout χsource
              (β L')
              hs 1 A₁ Bnd Residual ∧
            RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*lc.maskRadius/4)
              (z.1-lc.maskRadius/2) (fun t s y η ↦ G (t, (s, (y, η))))
              (twoTimePhysicalApply (fun y idx ↦ (coefficient lc.index Q y idx).map Complex.ofReal)
                (fun y ↦ (zeroth lc.index B y).map Complex.ofReal) W₁)
              χout χsource
              (β L')
              hs 1 A₁ Bnd Residual ∧
            ∀ (U Vout : Set E) (hU : MeasurableSet U), MeasurableSet Vout →
              (∀ f : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
                MemRestrictionSobolev Vout 1 (localRetardedOperator hU Vout Residual f) ∧
                restrictionSobolevNorm Vout 1 (localRetardedOperator hU Vout Residual f) ≤
                  (H1 * Bnd 1 * (2 + 2 * M)) * ‖f‖) ∧
              (∀ g : LocalL2 Vout (EuclideanSpace ℂ (Fin (d+1))),
                MemRestrictionSobolev U 1 ((localRetardedOperator hU Vout Residual).adjoint g) ∧
                restrictionSobolevNorm U 1 ((localRetardedOperator hU Vout Residual).adjoint g) ≤
                  (H1 * Bnd 1 * (2 + 2 * M)) * ‖g‖)) ∧
          (∀ q : T, lc.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
            (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
              WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                (fun y k ↦ collared ℓ 1 angular (Fs 1)
                  (physicalSlice e q.2.1 q.2.2.2 y) k j)
                (e.symm (q.1, q.2.2.1))) ∧
          (∀ j : Fin 3,
            let f := pencilAmplitudeFamily lc.index Q B h Φ C lc.row lc.col lc.sourceMask j
            let F := bufferedMatrix V lc.timeMask f
            let o := if j = 0 then 0 else 1
            let W := collared ℓ o angular F
            ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
            tsupport F ⊆ closedBall (z.1, z) (lc.bufferRadius / 2) ∧ ContDiff ℝ ∞ W ∧
            tsupport W ⊆ ConicPhase.domain ℓ V ∧
            (∀ q : T, q.2.1 ≤ z.1 - lc.maskRadius → W q = 0) ∧
            (∀ q ∈ V, lc.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
            ∀ m,
              BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (lc.bufferRadius / 2) ra rb) m
                (curryCharacteristicMatrix W) ∧
              twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (lc.bufferRadius / 2) ra rb) m
                (curryCharacteristicMatrix W) ≤
                D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                  cNorm (closedBall x RQ) (m + 9) B)) ∧
          EndpointPdoEstimates lc.index (closedBall x RQ) Q B
            (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
            (selectedEndpointSymbol f p L' Q W₁) Rbox M Dpdo Dgain Gain := by
  obtain ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, hevolution⟩ :=
    exists_finite_physical_evolution_data_with_protection_certificates_on_enlarged_bands
      hΩ f hprotection hradii hM bandFloor bandCeiling hbandFloor
  refine ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p ↦ endpointOutputMask_mul_chartOutputMask f p hos
  · exact fun p ↦ endpointOutputMask_mul_retained_output f p output (χout p) (houtputMul p)
  · exact fun p ↦ retained_source_mul_chartInputMask f p (χsource p) (hsourceMul p)
  · exact fun p L' _ ↦ exists_endpoint_source_pdo_budgets f p L' ho hoc hos
  · exact fun L' hLL y hy ζ ↦ selectedSourceSymbols_complete_partition_enlarged f
      (hLf.trans hLL) hy ζ
  · intro p
    exact selectedChartEndpointAt_with_protection_of_retained_on_enlarged_band hΩ hKΩ f p hM (hradii p).1 (hradii p).2
      hLf ho hoc hos (hevolution p)

/-- Recover the original finite endpoint conclusion from its enlarged-band
construction on the same witnesses (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_finite_physical_endpoint_pdos_with_protection_certificates
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {evolutionTime speedGap rootSize : f.centers → ℝ} {rootCost : f.centers → ℕ → ℝ}
    (hprotection : ∀ p, Characteristic.AlgebraicChart.LocalProtectionCertificate (f.chart p)
      (evolutionTime p) (speedGap p) (rootSize p) (rootCost p))
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hM : 0 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ f.radialThreshold ≤ L ∧ f.radialThreshold ≤ 2 * L ∧
    ∃ (angular : f.centers → Euclidean d → ℝ)
      (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        (∀ η, angular p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (angular p) ∧
        tsupport (angular p) ⊆ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius / 2) ∧
        (∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)) ∧
      (∀ p, ContDiff ℝ ∞ (χout p) ∧ HasCompactSupport (χout p) ∧
        HasCompactSupport (χsource p) ∧
        tsupport (χsource p) ⊆ (physicalCoordinates (f.chart p).index) ⁻¹' Ω ∧
        (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
          interior {y | χsource p y = 1} ∧
        (∀ y ∈ tsupport (χout p), (f.chart p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1))) ∧
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p, tsupport output ⊆ (physicalCoordinates (f.chart p).index).symm ⁻¹'
        interior {y | χout p y = 1}) ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) *
        χout p ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ)) ∧
      (∀ ζ : E, (∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ζ +
        FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1) ∧
      (∀ p y, endpointOutputMask f p output y * FiniteAlgebraic.chartOutputMask f p y =
        endpointOutputMask f p output y) ∧
      (∀ p y, endpointOutputMask f p output y * χout p y = endpointOutputMask f p output y) ∧
      (∀ p y, χsource p y * FiniteAlgebraic.chartInputMask f p y =
        FiniteAlgebraic.chartInputMask f p y) ∧
      (∀ p : f.centers, ∀ L' ≥ L,
        ∃ R > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
          FourierIntegral.GraphNormalAmplitudeBounds
            (Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
              (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
              (selectedSourceSymbol f p (2*L'))) R (C (2*(d+2))) ∧
          ∀ m ξ is, is.length ≤ m → ∀ z,
            ‖AmplitudeBound.matrixAmplitudeCoordinateDerivList is
              (Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
                (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
                (selectedSourceSymbol f p (2*L')) ξ) z‖ ≤ C m) ∧
      (∀ L' ≥ L, ∀ y ∈ closedBall x (4*f.physicalRadius), ∀ ζ : E,
        (∑ p, selectedSourceSymbol f p (2*L')
          ((physicalCoordinates (f.chart p).index).symm y)
          ((physicalCoordinates (f.chart p).index).symm ζ)) +
          (dilatedConicMask (fun η ↦ 1-∑ p, f.angularMask p η) (2*L') ζ : ℂ) •
            (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) +
          (FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
            ((2*L')⁻¹ • ζ) : ℂ) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) = 1) ∧
      ∀ p : f.centers, SelectedChartEndpointAtWithProtection f p
        (evolutionTime p) (speedGap p) (rootSize p) (rootCost p)
        L (angular p) (χout p) (χsource p) (hs p) output := by
  obtain ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, houtputChart, houtputRetained, hsourceRetained, hsourceBudget,
    hsourcePartition, hevolution⟩ :=
    exists_finite_physical_endpoint_pdos_with_protection_certificates_on_enlarged_bands
      hΩ hKΩ f hprotection hradii hM (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
  refine ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, houtputChart, houtputRetained, hsourceRetained, hsourceBudget,
    hsourcePartition, ?_⟩
  intro p L' hLL
  obtain ⟨hp, hsource, ra, hra, rb, hrab, _, _, hcoverage, hremaining⟩ :=
    hevolution p L' hLL
  exact ⟨hp, hsource, ra, hra, rb, hrab, hcoverage, hremaining⟩

end JanetCartan.RegularSector.FinitePdo
