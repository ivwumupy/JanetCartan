module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedPrescribedCorrectedRaw
public import JanetCartan.Iteration.PhysicalSeed.DensityProducts
public meta import JanetCartan.Iteration.PhysicalSeed.Templates

/-!
# Actual prescribed source inverse on the strengthened initializer

The source inverse is constructed for the same newly strengthened tuple, not
identified with any previous weaker choice. The entire original arbitrary
frame/extension/order/margin/cap continuation is retained verbatim.
-/

set_option warningAsError true
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalSeed
open ContinuumInverse
open ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ContinuumNormal.SourceDensityLimitRealization
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates CurrentCoefficientProfiles CurrentCoefficientProfiles.JointExtensions
open NormalizedBackground NormalizedBackground.SourceGeometry FrozenPhaseReference HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs

open PositiveReference PositiveReference.FlowConstruction

open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol CanonicalCarrier CanonicalConic
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement
open CarrierSobolev

open TransportKernel CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- The actual common initializer with its same-source prescribed inverse and
its full arbitrary-smooth-map leading callback, selected together before frames
(`app:ch_background:prop:bg-inverse`, `new:sec:order-of-choices`). -/
theorem exists_prescribed_source_with_generic_leading {n : ℕ} (hn : 5 ≤ n) :
    retain_physical_seed%
      (ContinuumInverse.exists_common_initializer_with_prescribed_corrected_source_raw_inverse hn)
      before εframe retaining
      (∃ η : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
        (∀ i, 0 < η i) ∧ ∀ i,
        GenericLeading (T i) (K := closedBall (0 : Euclidean n) b)
          (η i) (centers i) (row i) (col i) (ρlead i) (L i) (τ i)
          (Rc i) (τc i) (Mc i) (rcomp i) (δcomp i) (σcover i)
          (Ωc i) (ρc i) (Bc i) (gc i) (Bfull i)) := by
  classical
  have initialized := exists_density_products_with_generic_leading hn
  choose G₀ hG₀ b R hb hbR hR D c C hD kCenter hkCenter hkDomain
    T hposition hphysical hgeometry γ hγ hgap r hr hrb hradius
    εlead hεlead centers row col ρlead L τ Rc τc Mc rcomp δcomp σcover
    hrc hpositive Ωc ρc Bc gc μc Bfull hsourceGeometry hfullTime
    hgeometryc hworking εcarrier ρdet hcell hcarrierCover V hV
    Mproduct Rproduct hproduct hcoverProduct hgeneric hinit using initialized
  have hball (i) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      ball 0 R :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      (ball_subset_ball hbR.le)
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, kCenter, hkCenter, hkDomain,
    T, hposition, hphysical, hgeometry, γ, hγ, hgap, r, hr, hrb, hradius,
    εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hrc, hpositive, Ωc, ρc, Bc, gc, μc, Bfull, hsourceGeometry, hfullTime,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover, V, hV,
    Mproduct, Rproduct, hproduct, hcoverProduct, hgeneric, ?_⟩
  intro εframe hεframe qext hqcenter hqradius k hk hkD
  have quotientResult := hinit εframe hεframe qext hqcenter hqradius k hk hkD
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
  have referenceResult := hinit p orders margin extendedMargin hmargin hextendedMargin cap hcap
  choose θ hθ hθcap hθ1 H hHdomain hHmap hseedResult hcontraction hmean using referenceResult
  choose seed hseedforward hseed hsource using hseedResult
  refine ⟨θ, hθ, hθcap, hθ1, H, hHdomain, hHmap,
    ⟨seed, hseedforward, hseed, ?_, hsource⟩, hcontraction, hmean⟩
  intro incidenceCap hincidenceCap Tm Im Rm Vm rowm colm c₀
    Ωm zCellm ρcm Rcm Mm τleadm Lm aExtra
  exact exists_finite_prescribed_measured_source_raw_inverse hD hn H
    (by simpa only [hHdomain, LocalDomain.chart] using
      (ball_subset_ball hR.le : ball (0 : Euclidean n) R ⊆ ball 0 G₀.domain.chartRadius))
    isBounded_ball Tm Im Ωm
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.1)
    zCellm ρcm Rcm Mm τleadm rowm colm
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.1)
    (fun b l j w hw ↦ by
      have hh := (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.1 hw
      exact ⟨⟨closedBall_subset_ball hbR (interior_subset hh.1.2), hh.1.1⟩, hh.2⟩)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.1.le)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.2.2.2.1)
    (fun b l j ↦ (hsourceGeometry ⟨b, l⟩ j).2.1)
    (fun b l j ↦ (hpositive ⟨b, l⟩ j).2.2.2.1)
    (fun b l j ↦ (hpositive ⟨b, l⟩ j).2.2.2.2.1)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.2.2.1)
    (fun b l ↦ hball ⟨b, l⟩) c₀ (fun b l j ↦ (hseed ⟨b, l⟩ j).2)
    Rm Vm (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.1)
    (fun _ _ _ ↦ isOpen_ball)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2.1)
    Lm (fun b l j ↦ Mproduct ⟨b, l⟩ j)
    (fun b l j ↦ (hpositive ⟨b, l⟩ j).2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).1)
    (fun b l j ↦ ((hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2.2.2.2
      H.map (row ⟨b, l⟩ j) (col ⟨b, l⟩ j) (seed ⟨b, l⟩ j)).1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2.2.1)
    (fun b l ↦ hcoverProduct ⟨b, l⟩) hincidenceCap aExtra

end JanetCartan.PhysicalSeed
