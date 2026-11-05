module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates

/-!
# The same selected phase and amplitudes with their proved endpoint PDO

Retain every conclusion of the selected evolution producer and append the
actual endpoint certificate inside its SAME phase and amplitude existentials.
All PDO constants are selected before Q, B and Sobolev order. The producer
below enriches one application of the retained construction; it never chooses
another phase or amplitude. Source: `energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.AmplitudeBounds
open Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LocalSobolev
open Characteristic.RetardedLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
open FiniteEvolution RetainedConstruction
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Constructed selected-chart output with source agreement and the endpoint
PDO budgets and signed estimates on its literal W₁. This is an output of
`exists_finite_physical_endpoint_pdos`, not a premise of that constructor.
All original phase, W₀/W₁/PW₁ and retarded conclusions are retained on the
same witnesses (`energy-complete-residual`, `measured-adjoint`). -/
def SelectedChartEndpointAt
    (f : ActualMaskFamily Ω x RQ Aref K M) (p : f.centers)
    (L : ℝ) (angular : Euclidean d → ℝ) (χout χsource : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (output : E → ℝ) : Prop :=
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
            (selectedEndpointSymbol f p L' Q W₁) Rbox M Dpdo Dgain Gain

/-- Enrich the retained producer using its SAME band, phase and amplitudes.
The original joint seminorm supplies both diagonal time derivatives. The
fixed `sectorLowOrder` discharges every endpoint low-order requirement
before varying coefficients or accuracy (`energy-complete-residual`). -/
theorem selectedChartEndpointAt_of_retained
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ Aref K M) (p : f.centers) (hM : 0 ≤ M)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {L : ℝ} (hL : f.radialThreshold ≤ L)
    {angular : Euclidean d → ℝ} {χout χsource : E → ℂ}
    {hs : ContDiff ℝ ∞ χsource} {output : E → ℝ}
    (ho : ContDiff ℝ ∞ output) (hc : HasCompactSupport output)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (hevolution : SelectedChartEvolutionAtWithDiagonal (f.chart p)
      (selectedEndpointMultiplier f p) L angular χout χsource hs) :
    SelectedChartEndpointAt f p L angular χout χsource hs output := by
  intro L' hLL
  obtain ⟨hplateau, ra, hra, rb, hrab, hcoverage, D, hD,
    A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, H1, hH1, hevoQ⟩ := hevolution L' hLL
  obtain ⟨Rbox, hRbox, Dpdo, Dgain, Gain, hDpdo, hDgain, hGain, hendpoint⟩ :=
    exists_selected_endpoint_constants hΩ hKΩ f p hM hρb hsrcρ
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        ((f.radialThreshold_ge_one.trans hL).trans hLL)) hcoverage D hD ho hc hsupp
  refine ⟨hplateau, selectedSourceSymbol_eq_retainedSourceSymbol f p
    hevolution.toSelectedChartEvolutionAt hLL (hL.trans hLL),
    ra, hra, rb, hrab, hcoverage, D, hD, Rbox, hRbox, Dpdo, Dgain, Gain,
    hDpdo, hDgain, hGain, A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, H1, hH1, ?_⟩
  intro Q hQ hQrange hQlow h U
  obtain ⟨Φ, C, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, hevoB⟩ :=
    hevoQ Q hQ hQrange hQlow
  refine ⟨Φ, C, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, ?_⟩
  intro B hB hBlow V Fs W₀ W₁
  obtain ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead, hoperators, hphysical, hW⟩ :=
    hevoB B hB hBlow
  refine ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead, hoperators, hphysical, hW, ?_⟩
  exact hendpoint Q hQ hQlow B hBlow h Φ C V angular
    (by simpa only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] using (hW 1).2.2.2.2.1)
    (by simpa only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] using
      (hW 1).2.2.2.2.2.2.2.2)

/-- Forget only the new source and PDO conclusions. This projection keeps
all original selected evolution witnesses and estimates
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem SelectedChartEndpointAt.toSelectedChartEvolutionAtWithDiagonal
    {f : ActualMaskFamily Ω x RQ Aref K M} {p : f.centers} {L : ℝ}
    {angular : Euclidean d → ℝ} {χout χsource : E → ℂ}
    {hs : ContDiff ℝ ∞ χsource} {output : E → ℝ}
    (hevolution : SelectedChartEndpointAt f p L angular χout χsource hs output) :
    SelectedChartEvolutionAtWithDiagonal (f.chart p) (selectedEndpointMultiplier f p)
      L angular χout χsource hs := by
  intro L' hLL
  obtain ⟨hplateau, _, ra, hra, rb, hrab, hcoverage, D, hD,
    _, _, _, _, _, _, _, _, A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, H1, hH1, hevoQ⟩ :=
    hevolution L' hLL
  refine ⟨hplateau, ra, hra, rb, hrab, hcoverage, D, hD,
    A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, H1, hH1, ?_⟩
  intro Q hQ hQrange hQlow
  obtain ⟨Φ, C, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, hevoB⟩ :=
    hevoQ Q hQ hQrange hQlow
  refine ⟨Φ, C, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, ?_⟩
  intro B hB hBlow
  obtain ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead, hoperators, hphysical, hW, _⟩ :=
    hevoB B hB hBlow
  exact ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead, hoperators, hphysical, hW⟩

end JanetCartan.RegularSector.FinitePdo
