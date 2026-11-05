module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.InitializedCharts
public import JanetCartan.Iteration.PhysicalSeed.CommonReference
public meta import JanetCartan.Iteration.PhysicalSeed.Templates

/-! Same-tuple seed and normalized source charts, retaining the generic callback. -/

set_option warningAsError true
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalSeed
open ContinuumRow.NormalizedSelection
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates CurrentCoefficientProfiles CurrentCoefficientProfiles.JointExtensions
open NormalizedBackground NormalizedBackground.SourceGeometry FrozenPhaseReference HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs

open PositiveReference.FlowConstruction

/-- Retain the unrestricted leading callback while constructing the original
actual seed and source charts on its same cells (`app:ch_background:prop:bg-normalized`). -/
theorem exists_normalized_charts_with_generic_leading {n : ℕ} (hn : 5 ≤ n) :
    retain_physical_seed%
      (ContinuumRow.NormalizedSelection.exists_common_initializer_with_normalized_charts hn)
      before εframe retaining
      (∃ η : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
        (∀ i, 0 < η i) ∧ ∀ i,
        GenericLeading (T i) (K := closedBall (0 : Euclidean n) b)
          (η i) (centers i) (row i) (col i) (ρlead i) (L i) (τ i)
          (Rc i) (τc i) (Mc i) (rcomp i) (δcomp i) (σcover i)
          (Ωc i) (ρc i) (Bc i) (gc i) (Bfull i)) := by
  classical
  have initialized :=
    exists_common_reference_with_generic_leading hn
  choose G₀ hG₀ b R hb hbR hR D c C hD kCenter hkCenter hkDomain
    T hposition hphysical hgeometry γ hγ hgap r hr hrb hradius
    εlead hεlead centers row col ρlead L τ Rc τc Mc rcomp δcomp σcover
    hrc hpositive Ωc ρc Bc gc μc Bfull hsourceGeometry hfullTime
    hgeometryc hworking εcarrier ρdet hcell hcarrierCover V hV hgeneric hinit using initialized
  have hball (i) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      ball 0 R :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      (ball_subset_ball hbR.le)
  obtain ⟨capAdmission, hcapAdmission, _, hadmit⟩ :=
    exists_finite_retained_source_scale_interval G₀ isBounded_ball T hball
      (fun _ ↦ hγ) (fun i ↦ (T i).family.threshold_pos) hgap
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, kCenter, hkCenter, hkDomain,
    T, hposition, hphysical, hgeometry, γ, hγ, hgap, r, hr, hrb, hradius,
    εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hrc, hpositive, Ωc, ρc, Bc, gc, μc, Bfull, hsourceGeometry, hfullTime,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover, V, hV, hgeneric, ?_⟩
  intro εframe hεframe qext hqcenter hqradius k hk hkD
  have quotientResult :=
    hinit εframe hεframe qext hqcenter hqradius k hk hkD
  choose hz hinc hd ρF ρT qrad s e cF bF cT bT VF LF VT LT
    hboxes ρFext ρText qextRad sext eext cFext bFext cText bText
    VFext LFext VText LText hextBoxes ψF χF ψT χT hcutoffs
    εtransport gtransport hεtransport hgtransport transportCenters
    transportRow transportCol ρtransport Ltransport hρtransport Ωtransport
    hdomains hcover Dq Dt hDq hDt εcommon hεcommon hεcommonr hcommon hinit using quotientResult
  refine ⟨hz, hinc, hd, ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT,
    hboxes, ρFext, ρText, qextRad, sext, eext, cFext, bFext, cText, bText,
    VFext, LFext, VText, LText, hextBoxes, ψF, χF, ψT, χT, hcutoffs,
    εtransport, gtransport, hεtransport, hgtransport, transportCenters,
    transportRow, transportCol, ρtransport, Ltransport, hρtransport, Ωtransport,
    hdomains, hcover, Dq, Dt, hDq, hDt, εcommon, hεcommon, hεcommonr, hcommon, ?_⟩
  intro p orders margin extendedMargin hmargin hextendedMargin cap hcap
  have referenceResult :=
    hinit p orders margin extendedMargin hmargin hextendedMargin
      (min cap capAdmission) (lt_min hcap hcapAdmission)
  choose θ hθ hθcap hθ1 H hHdomain hHmap hcontraction hmean using referenceResult
  have hbase := hadmit θ ⟨hθ, (hθcap.trans_le (min_le_right _ _)).le⟩
  rw [← hHmap] at hbase
  obtain ⟨_, _, _, _, hseedframe⟩ := hbase
  have hHone : sourceDilation H.map 1 = H.map := by
    funext x
    simp [sourceDilation]
  obtain ⟨_, _, _, G, _, hGH, _, _, _, _, _, _, hlead, _⟩ :=
    hcontraction 1 zero_lt_one le_rfl
  have hGH' : G.map = H.map := hGH.trans hHone
  obtain ⟨kMin, hkMin⟩ := exists_nat_gt
    (displacementLoss n + bandExponent * ((14 : ℝ) + (n : ℝ) / 2) + 2)
  obtain ⟨S, _, κ, _, g, Amap, E, A, Hflow, B, _, _, _, hhistory⟩ :=
    hlead 14 0 kMin le_rfl (by norm_num) hkMin 1 1 (by norm_num) zero_lt_one
  have hempty := hhistory S le_rfl 0 (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
    (isAdmissibleHistory_empty _ _ _ _)
  dsimp only at hempty
  simp only [finiteHistoryMap_empty, hGH'] at hempty
  obtain ⟨hF, hi, hrank, _, _, _, _, hlow, hactual⟩ := hempty
  have hseeds (i) (j : centers i) :
      ∃ seed : Chart (T i) (Ωc i j) (closedBall ((0 : Euclidean n), j.1.1) (ρc i j))
        ((0 : Euclidean (n - 1)), j.1.1) (Rc i j) (Bc i j) (τc i j)
        (row i j) (col i j) H.map,
      cNorm (Icc (-τc i j) (τc i j) ×ˢ
        closedBall ((0 : Euclidean (n - 1)), j.1.1) (Rc i j / 8)) 1 seed.forward ≤ Mc i j := by
    obtain ⟨_, _, _, Dc, φ, y, hcarrierData, hDc, hsmall, hbig, hφD, hyD,
      hφ₀, hyφ, hφy, hode, hφbuffer, hforward, _⟩ := hactual i j
    obtain ⟨hk, hl, hd, hc, hB, hsymm, hnull, himage, hcoeff, _, _,
      hφ, hy, hφz, hyz, hybuffer⟩ := hcarrierData
    let Q := (⟨projectedStress H.map,
      contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball 0 R) ∧
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    exact ⟨RetainedLeading.chartOfRetainedCarrierData (T i) Q H.map rfl Dc φ y
      hk hl hd hc hB hsymm hnull himage hcoeff hφ hy hφz hyz hybuffer
      hDc hsmall hbig hφD hyD hφ₀ hyφ hφy hode hφbuffer, hforward⟩
  choose seed hseedforward using hseeds
  have hseed (i) (j : centers i) : (seed i j).Q.1 0 = cubeStress n ∧
      ∀ q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius,
        ⟪(normalizedHomogeneousSymbol isOpen_ball (seed i j).Q.1 (seed i j).Q.2.1).hp q,
          (T i).data.adapted.normal⟫_ℝ ≠ 0 := by
    obtain ⟨Q, hQ, hzero, _, htrans, _⟩ := hseedframe i
    have he : (seed i j).Q = Q := Subtype.ext ((seed i j).frame_eq.trans hQ.symm)
    simpa only [he] using And.intro hzero htrans
  refine ⟨θ, hθ, hθcap.trans_le (min_le_left _ _), hθ1, H, hHdomain, hHmap,
    ⟨seed, hseedforward, hseed, ?_⟩, ?_, hmean⟩
  · intro J δgeometry hδgeometry
    have hpatch (i : J) : Ωc i.1 i.2 ⊆ ball 0 (T i.1).physicalRadius ×ˢ
        parameterCube (2 * (D.patches i.1.1 i.1.2).radius) := by
      intro w hw
      have hh := (hgeometryc i.1 i.2).2.2.2.2.2.1 hw
      exact ⟨hh.1.1, fun l ↦ (hh.2 l).le.trans
        (by have := ((hD.2.2.2.2.1 i.1.1 i.1.2).1).1; linarith)⟩
    exact NormalizedChartFamily.exists_finite_source_charts_with_lifts H
      (by simpa only [hHdomain, LocalDomain.chart] using
        (ball_subset_ball hR.le : ball (0 : Euclidean n) R ⊆ ball 0 G₀.domain.chartRadius))
      isBounded_ball (fun i : J ↦ T i.1) (fun i ↦ Ωc i.1 i.2)
      (fun i ↦ (hgeometryc i.1 i.2).2.2.2.1) (fun i ↦ i.2.1.1)
      (fun i ↦ ρc i.1 i.2) (fun i ↦ Rc i.1 i.2) (fun i ↦ Bc i.1 i.2)
      (fun i ↦ τc i.1 i.2) δgeometry (fun i ↦ row i.1 i.2) (fun i ↦ col i.1 i.2)
      (fun i ↦ (hpositive i.1 i.2).2.2.2.1)
      (fun i ↦ (hgeometryc i.1 i.2).2.1.le) hδgeometry
      (fun i ↦ (hgeometryc i.1 i.2).2.2.2.2.2.2.2.2.1)
      (fun i ↦ (hgeometryc i.1 i.2).2.2.2.2.1) hpatch
      (fun i w hw ↦ closedBall_subset_ball hbR
        (interior_subset ((hgeometryc i.1 i.2).2.2.2.2.2.1 hw).1.2))
      (fun i ↦ (hsourceGeometry i.1 i.2).2.1) (fun i ↦ hball i.1)
      (fun i ↦ (hgeometryc i.1 i.2).2.2.2.2.2.2.2.1)
      (fun i ↦ seed i.1 i.2) (fun i ↦ (hseed i.1 i.2).2)
  · intro σ hσ hσ1
    obtain ⟨hρ, hρcap, hρ1, hrest⟩ := hcontraction σ hσ hσ1
    exact ⟨hρ, hρcap.trans_le (min_le_left _ _), hρ1, hrest⟩

end JanetCartan.PhysicalSeed
