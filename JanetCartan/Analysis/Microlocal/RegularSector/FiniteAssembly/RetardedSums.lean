module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Amplitudes
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CommonMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Threshold

/-!
# Actual finite retarded sums with the common physical masks

Instantiate the endpoint construction on the retained family before varying
coefficients. Its same phase, W₀/W₁/PW₁, upper endpoint and both retarded
operators are retained. Sum the actual operators in physical coordinates and
apply the common masks. This constructs the evolution part of the solver and
residual; the algebraic contributions and complete PDE identity remain to be
assembled (`energy-complete-residual`, `sector-theorem-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicAmplitude Characteristic.AmplitudeBounds Characteristic.RootFamily
open Characteristic.ConicPhase Characteristic.UniformAmplitudes Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral FiniteMasks FiniteMasks.ActualFamily
open FinitePdo FiniteEvolution FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.RetardedLocalization LocalSobolev
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TPoint" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Construct the finite evolution solver and `PW₁` residual on the actual
selected family. The fixed common masks and every bound constant precede Q,
B and the requested Sobolev order. No phase, amplitude or operator estimate
is a premise. The retained upper endpoint is on the SAME W₁ and masks.
The source threshold is recorded as `2*L` on the same family. This theorem
constructs two terms of the direct formula; it does not assert the complete
sector equation (`fixed-time-representation`, `energy-complete-residual`). -/
theorem exists_finite_common_retarded_sums
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ Aref K M)
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4) (hM : 0 ≤ M) :
    ∃ L : ℝ, ∃ hL : f.radialThreshold ≤ L,
    ∃ (angular : f.centers → Euclidean d → ℝ) (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) * χout p ((physicalCoordinates (f.chart p).index).symm y) =
        (output y : ℂ)) ∧
      (∀ p, SelectedChartEndpointAt f p L (angular p) (χout p) (χsource p) (hs p) output) ∧
      (∀ p, selectedSourceSymbol (withEnlargedThreshold f L hL) p
        (withEnlargedThreshold f L hL).radialThreshold = selectedSourceSymbol f p (2*L)) ∧
    ∃ (base : Fin 2 → f.centers → ℝ) (cost : Fin 2 → f.centers → ℕ → ℝ)
      (maskCost : ℕ → ℝ) (Rbox : f.centers → ℝ)
      (Dpdo Dgain Gain : f.centers → ℕ → ℝ)
      (ra rb : f.centers → ℝ) (amplitudeCost : f.centers → ℕ → ℝ),
      (∀ o p, 0 < base o p) ∧ (∀ o p s, 0 < cost o p s) ∧
      (∀ s, 1 ≤ maskCost s) ∧ (∀ p, 0 < Rbox p) ∧
      (∀ p s, 1 ≤ Dpdo p s) ∧ (∀ p s, 1 ≤ Dgain p s) ∧ (∀ p s, 0 ≤ Gain p s) ∧
      (∀ p, 0 < ra p) ∧ (∀ p, ra p < rb p) ∧ (∀ p m, 0 < amplitudeCost p m) ∧
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) ∧
      (∀ p, FinitePdo.RetainedConstruction.DiagonalFrequencyCoverage
        (f.chart p).radialSection (coordinateSplit (f.chart p).index p.val.val).2
        ((f.chart p).bufferRadius/2) (ra p) (rb p) (selectedEndpointMultiplier f p L)) ∧
    ∃ localCost : ℝ, 0 < localCost ∧
    ∀ Q : E → Fin (d+1) → Mat, ContDiffOn ℝ ∞ Q Ω →
      MapsTo Q Ω (closedBall Aref f.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
    ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω →
      cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
    ∃ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph TPoint TPoint)
      (G : f.centers → TPoint → ℝ) (Op : Fin 2 → f.centers → H →L[ℂ] H),
      (∀ p,
        let c := f.chart p
        let e := coordinateSplit c.index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        let h := fieldRoot e Q c.root
        let U := fieldDomain e Ω c.radialSection z.2.2 c.coefficientRadius
        let V := (C p).target ∩ (C p).symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
          (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2)))
        let Fs := selectedBufferedAmplitude f p Q B (Φ p) (C p)
        let W := selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
        ContDiffOn ℝ ∞ h U ∧
        (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t*h w) ∧
        closedBall z c.rootRadius ⊆ U ∧
        (∀ w ∈ closedBall z c.rootRadius, (rootPencil e Q h w).det = 0 ∧
          c.minorGap ≤ |(rootPencil e Q h w).adjugate c.row c.col| ∧
          c.transportGap ≤ |minorTransportCoefficient (rootPencil e Q h w)
            (rootTimeCoefficient e Q w) c.row c.col|) ∧
        ((C p) : TPoint → TPoint) = twoTimeProjection (Φ p) ∧
        (C p).source = ball (z.1, z) c.sourceRadius ∧
        ContDiffOn ℝ ∞ (C p).symm (C p).target ∧
        closedBall (z.1, z) c.targetRadius ⊆ (C p).target ∧
        ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target ∧
        (∀ q ∈ (C p).target, HasFDerivAt (twoTimePhase (C p))
          (twoTimePhaseDifferential h (Φ p) (C p) q) q) ∧
        (∀ q ∈ (C p).target,
          ((C p).symm q).1 = q.1 ∧ ((C p).symm q).2.1 = q.2.1 ∧
          ((C p).symm q).2.2.2 = q.2.2.2 ∧
          (twoTimeState (Φ p) ((C p).symm q)).2.1 = q.2.2.1) ∧
        (∀ q ∈ (C p).target, twoTimeState (Φ p) ((C p).symm q) ∈ U ∧
          (twoTimeState (Φ p) ((C p).symm q)).1 = q.1) ∧
        (∀ w ∈ ball z c.sourceRadius, (w.1, w) ∈ (C p).target ∧
          (C p).symm (w.1, w) = (w.1, w) ∧
          twoTimePhase (C p) (w.1, w) = inner ℝ w.2.1 w.2.2) ∧
        (∀ q ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed (C p) q - 1‖ ≤ 1/2) ∧
        (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase (C p)) ≤
          c.phaseCost m * (1+cNorm (closedBall x RQ) (m+1) Q)) ∧
        ball (z.1, z) c.outerRadius ⊆ (C p).target ∧
        MapsTo (C p) (closedBall (z.1, z) c.maskRadius)
          (closedBall (z.1, z) (c.bufferRadius/2)) ∧
        ContDiff ℝ ∞ (G p) ∧
        (∀ t y η, G p (t, (t, (y, η))) = inner ℝ y η) ∧
        (∀ q ∈ tsupport (collared c.radialSection 0 (angular p) (Fs 0)) ∪
          tsupport (collared c.radialSection 1 (angular p) (Fs 1)),
          G p =ᶠ[𝓝 q] ConicPhase.phase c.radialSection (C p)) ∧
        (∀ q : TPoint, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) →
          collared c.radialSection 1 (angular p) (Fs 2) q ≠ 0 →
          G p =ᶠ[𝓝 q] ConicPhase.phase c.radialSection (C p)) ∧
        (∀ y : E, c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
          WKB.firstOrderApply
            (fun x idx ↦ ((coefficient c.index Q x idx).map Complex.ofReal).mulVecLin)
            (fun x ↦ ((zeroth c.index B x).map Complex.ofReal).mulVecLin)
            (fun x ↦ Complex.exp (Complex.I * (G p (x 0, (s, (spatialPart x, η))) : ℂ)) •
              (fun k ↦ (W 0 + W 1) (x 0) s (spatialPart x) η k j)) y =
            Complex.exp (Complex.I * (G p (y 0, (s, (spatialPart y, η))) : ℂ)) •
              (fun k ↦ twoTimePhysicalApply
                (fun x idx ↦ (coefficient c.index Q x idx).map Complex.ofReal)
                (fun x ↦ (zeroth c.index B x).map Complex.ofReal) (W 1)
                  (y 0) s (spatialPart y) η k j)) ∧
        (∀ y : E, c.timeMask (y 0) = 1 → ∀ η,
          (coefficient c.index Q y 0).map Complex.ofReal * W 0 (y 0) (y 0) (spatialPart y) η =
            conicSourceSymbol c.radialSection (conicMask (angular p)) c.sourceMask y η •
              projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η)) ∧
        let Ψ := fun t s y η ↦ G p (t, (s, (y, η)))
        let a := (coordinateSplit c.index x).1-c.maskRadius/2
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (W 0 + W 1) (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 0 (base 0 p) (cost 0 p) (Op 0 p) ∧
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (W 2) (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 1 (base 1 p) (cost 1 p) (Op 1 p) ∧
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (twoTimePhysicalApply (fun y idx ↦ (coefficient c.index Q y idx).map Complex.ofReal)
            (fun y ↦ (zeroth c.index B y).map Complex.ofReal) (W 1))
          (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 1 (base 1 p) (cost 1 p) (Op 1 p) ∧
        EndpointPdoEstimates c.index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
          (selectedEndpointSymbol f p L Q (W 1)) (Rbox p) M (Dpdo p) (Dgain p) (Gain p) ∧
        (∀ q : TPoint, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
          (fun k ↦ collared c.radialSection 1 (angular p) (Fs 2) q k j) =
            WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
              (fun y k ↦ collared c.radialSection 1 (angular p) (Fs 1)
                (physicalSlice e q.2.1 q.2.2.2 y) k j) (e.symm (q.1, q.2.2.1))) ∧
        ∀ j : Fin 3,
          ContDiff ℝ ∞ (Fs j) ∧ HasCompactSupport (Fs j) ∧ tsupport (Fs j) ⊆ V ∧
          tsupport (Fs j) ⊆ closedBall (z.1, z) (c.bufferRadius/2) ∧
          ContDiff ℝ ∞ (collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j)) ∧
          tsupport (collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j)) ⊆
            ConicPhase.domain c.radialSection V ∧
          (∀ q : TPoint, q.2.1 ≤ z.1-c.maskRadius →
            collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j) q = 0) ∧
          (∀ q ∈ V, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → Fs j =ᶠ[𝓝 q]
            pencilAmplitudeFamily c.index Q B h (Φ p) (C p) c.row c.col c.sourceMask j) ∧
          ∀ m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1)
              (bufferedJetSet c.radialSection z (c.bufferRadius/2) (ra p) (rb p)) m (W j) ∧
            twoTimeOrderSeminorm (if j=0 then 0 else 1)
              (bufferedJetSet c.radialSection z (c.bufferRadius/2) (ra p) (rb p)) m (W j) ≤
              amplitudeCost p m * (1+cNorm (closedBall x RQ) (m+10) Q+
                cNorm (closedBall x RQ) (m+9) B)) ∧
      ∃ (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      let S := fun o : Fin 2 ↦ (sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op o)).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
      let profile := retardedCoefficientProfile (closedBall x RQ) Q B
      let shift := FullLowBounds.fullLowReserve (d+1)+2
      (∀ o : Fin 2, ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = S o ∨ V = (S o).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤
          (maskCost s * (∑ p, cost o p s) * maskCost (s-o.val)) *
            (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + profile (s+shift)*‖u‖)) ∧
      (∀ o : Fin 2, ∀ k : ℕ, ∀ V : H →L[ℂ] H, (V = S o ∨ V = (S o).adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
        vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*(maskCost (k+o.val) * (∑ p, cost o p (k+o.val)) * maskCost k)) *
            (1+profile (k+o.val+shift)) * vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u) ∧
      ∀ (U V : Set E) (hU : MeasurableSet U), MeasurableSet V →
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev V 1 (localRetardedOperator hU V (S 1) u) ∧
          restrictionSobolevNorm V 1 (localRetardedOperator hU V (S 1) u) ≤
            (localCost * (maskCost 1 * (∑ p, cost 1 p 1) * maskCost 0) * (2+2*M)) * ‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU V (S 1)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU V (S 1)).adjoint v) ≤
            (localCost * (maskCost 1 * (∑ p, cost 1 p 1) * maskCost 0) * (2+2*M)) * ‖v‖) := by
  classical
  obtain ⟨L, _, hL, _, angular, χout, χsource, hs, hangular, _, output, r, hr, ho,
    horange, hoc, hos, hop, _, hsource, hout, _, _, _, _, _, _, hevo⟩ :=
    exists_finite_physical_endpoint_pdos hΩ hKΩ f hradii hM
  have hob y : ‖output y‖ ≤ 1 := by rw [Real.norm_of_nonneg (horange y).1]; exact (horange y).2
  have hib y : ‖f.inputMask y‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (f.inputMask_range y).1]; exact (f.inputMask_range y).2
  obtain ⟨maskCost, hmaskCost, hmask⟩ := exists_commonMask_sobolev_constants (q := d+1)
    output f.inputMask ho f.inputMask_smooth hoc f.inputMask_compact hob hib
  have hp p := hevo p L le_rfl
  choose hplateau hsourceEq ra hra rb hrab hcoverage D hD Rbox hRbox Dpdo Dgain Gain
    hDpdo hDgain hGain base0 hbase0 base1 hbase1 cost0 cost1 hcost0 hcost1 H1 hH1 hevoQ using hp
  let base : Fin 2 → f.centers → ℝ := ![base0, base1]
  let cost : Fin 2 → f.centers → ℕ → ℝ := ![cost0, cost1]
  have hbase o p : 0 < base o p := by fin_cases o <;> simp [base, hbase0, hbase1]
  have hcost o p s : 0 < cost o p s := by fin_cases o <;> simp [cost, hcost0, hcost1]
  obtain ⟨localCost, hlocalCost, hlocalBound⟩ := exists_localRetarded_restrictionH1_constant d (d+1)
  refine ⟨L, hL, angular, χout, χsource, hs, output, r, hr, ho, horange, hoc, hos,
    hop, hsource, hout, hevo, withEnlargedThreshold_sourceSymbol f L hL,
    base, cost, maskCost, Rbox, Dpdo, Dgain, Gain, ra, rb, D,
    hbase, hcost, hmaskCost, hRbox, hDpdo, hDgain, hGain, hra, hrab, hD,
    fun p ↦ ⟨(hangular p).1, (hangular p).2.2.2.2⟩, hcoverage, localCost, hlocalCost, ?_⟩
  intro Q hQ hQrange hQlow B hB hBlow
  have hq p := hevoQ p Q hQ (f.mapsTo_local_coefficient_ball p hQrange) hQlow
  choose Φ C hh hhom hUL hgap hC hsourceC hinvsmooth hbuffer hphase hdiff hinv hstate
    hdiag hnear hphaseBudget houter hflow hevoB using hq
  have hb p := hevoB p B hB hBlow
  choose G hGs hGdiag hG hGres hcancel hlead hoperators hphysical hW hendpoint using hb
  choose Solver Residual hSolver hResidual hPW hlocal using hoperators
  let Op : Fin 2 → f.centers → H →L[ℂ] H := ![Solver, Residual]
  refine ⟨Φ, C, G, Op, ?_, ho.continuous, hob, hib, ?_⟩
  · intro p
    exact ⟨hh p, hhom p, hUL p, hgap p, hC p, hsourceC p, hinvsmooth p, hbuffer p,
      hphase p, hdiff p, hinv p, hstate p, hdiag p, hnear p, hphaseBudget p, houter p,
      hflow p, hGs p, hGdiag p, hG p, hGres p, hcancel p, hlead p,
      hSolver p, hResidual p, hPW p, hendpoint p, hphysical p, hW p⟩
  · intro S profile shift
    have hpos p (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H)
        (hV : V = Op o p ∨ V = (Op o p).adjoint) (u : H)
        (hu : MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u) :
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
          vectorFourierSobolevNorm (s : ℝ) (V u) ≤ cost o p s *
            (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + profile (s+shift)*‖u‖) := by
      fin_cases o
      · exact (hSolver p).2.2.2.1 s V hV u hu
      · exact (hResidual p).2.2.2.1 s V hV u hu
    have hprofile m : 0 ≤ profile m := by
      dsimp [profile, retardedCoefficientProfile]
      linarith [cNorm_nonneg (closedBall x RQ) (m+10) Q,
        cNorm_nonneg (closedBall x RQ) (m+9) B]
    have hpositive (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H)
        (hV : V = S o ∨ V = (S o).adjoint) (u : H)
        (hu : MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u) :
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
          vectorFourierSobolevNorm (s : ℝ) (V u) ≤
            (maskCost s * (∑ p, cost o p s) * maskCost (s-o.val)) *
              (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + profile (s+shift)*‖u‖) := by
      exact hmask (finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op o))
        (s-o.val) s (∑ p, cost o p s) (profile (s+shift))
        (Finset.sum_nonneg fun p _ ↦ (hcost o p s).le) (hprofile _)
        (fun V hV u hu ↦ finitePhysicalOperator_positive_integer_bounds
          (fun p ↦ (f.chart p).index) (Op o) o.val shift (cost o) profile
          (fun p ↦ hpos p o) s V hV u hu) V hV u hu
    refine ⟨hpositive, ?_, ?_⟩
    · intro o k V hV u
      have hp (W : H →L[ℂ] H) (hW : W = S o ∨ W = (S o).adjoint) (v : H)
          (hv : MemVectorFourierSobolev (k : ℝ) v) :=
        hpositive o (k+o.val) W hW v (by simpa using hv)
      simp only [Nat.add_sub_cancel] at hp
      have hc : 0 ≤ maskCost (k+o.val) * (∑ p, cost o p (k+o.val)) * maskCost k :=
        mul_nonneg (mul_nonneg (zero_le_one.trans (hmaskCost _))
          (Finset.sum_nonneg fun p _ ↦ (hcost o p _).le)) (zero_le_one.trans (hmaskCost _))
      rcases hV with rfl | rfl
      · simpa only [Nat.cast_add, Nat.cast_one] using negativeVectorFourierSobolev_tame_bound_of_adjoint
          (Nat.cast_nonneg k) (Nat.cast_nonneg (k+o.val)) hc (hprofile _) (S o)
          (fun v hv ↦ hp (S o).adjoint (Or.inr rfl) v hv) u
      · simpa only [Nat.cast_add, Nat.cast_one] using negativeVectorFourierSobolev_tame_bound_of_adjoint
          (Nat.cast_nonneg k) (Nat.cast_nonneg (k+o.val)) hc (hprofile _) (S o).adjoint
          (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using
            (hp (S o) (Or.inl rfl) v hv)) u
    · intro U V hU hV
      obtain ⟨hf, ha⟩ := hlocalBound (S 1) shift 1
        (fun s ↦ maskCost s * (∑ p, cost 1 p s) * maskCost (s-1)) profile
        (by simpa only [one_mul, show (1 : Fin 2).val = 1 from rfl] using hpositive 1) U V hU hV
      have hlow := retarded_gain_one_profile_le (closedBall x RQ) Q B hQlow hBlow
      have hc : 0 ≤ localCost * (maskCost 1 * (∑ p, cost 1 p 1) * maskCost 0) :=
        mul_nonneg hlocalCost.le (mul_nonneg
          (mul_nonneg (zero_le_one.trans (hmaskCost _))
            (Finset.sum_nonneg fun p _ ↦ (hcost 1 p 1).le)) (zero_le_one.trans (hmaskCost _)))
      have hb := mul_le_mul_of_nonneg_left hlow hc
      exact ⟨fun u ↦ ⟨(hf u).1, (hf u).2.trans (by
          simpa only [one_mul, Nat.sub_self] using mul_le_mul_of_nonneg_right hb (norm_nonneg u))⟩,
        fun v ↦ ⟨(ha v).1, (ha v).2.trans (by
          simpa only [one_mul, Nat.sub_self] using mul_le_mul_of_nonneg_right hb (norm_nonneg v))⟩⟩


end JanetCartan.RegularSector.FiniteAssembly
