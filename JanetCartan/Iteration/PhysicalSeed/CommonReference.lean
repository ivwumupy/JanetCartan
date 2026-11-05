module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.NormalizedHistory.ChartCenters.RetainedWitnesses
public import JanetCartan.Iteration.PhysicalSeed.RetainedFamily
public meta import JanetCartan.Iteration.PhysicalSeed.Templates

/-!
# One original reference and one genuinely strengthened retained menu

This replays the original reference construction, but calls the strengthened
finite producer once and exports its unrestricted leading callback before the
arbitrary frame/quotient/direction continuation. All original finite margins,
source contractions and matched seed-mean conclusions remain on the same tuple.
-/

set_option warningAsError true
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalSeed
open ReferenceInitialization.NormalizedHistory
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates CurrentCoefficientProfiles CurrentCoefficientProfiles.JointExtensions
open NormalizedBackground NormalizedBackground.SourceGeometry FrozenPhaseReference HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs

/-- The original arbitrary-frame and source/seed continuation, with the genuine
same-row arbitrary-smooth-map leading callback retained before all frames
(`new:sec:order-of-choices`, `app:ch_seed:prop:seed-frozen-menu`). -/
theorem exists_common_reference_with_generic_leading {n : ℕ} (hn : 5 ≤ n) :
    retain_physical_seed%
      (ReferenceInitialization.NormalizedHistory.exists_common_normalized_history_reference_with_chart_centers_and_source_geometry hn)
      before εframe retaining
      (∃ η : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
        (∀ i, 0 < η i) ∧ ∀ i,
        GenericLeading (T i) (K := closedBall (0 : Euclidean n) b)
          (η i) (centers i) (row i) (col i) (ρlead i) (L i) (τ i)
          (Rc i) (τc i) (Mc i) (rcomp i) (δcomp i) (σcover i)
          (Ωc i) (ρc i) (Bc i) (gc i) (Bfull i)) := by
  classical
  obtain ⟨G₀, hG₀⟩ := exists_analytic_flatReference hn
  let b := G₀.domain.coreRadius / 2
  let R := G₀.domain.coreRadius
  have hb : 0 < b := half_pos G₀.domain.coreRadius_pos
  have hbR : b < R := half_lt_self G₀.domain.coreRadius_pos
  have hR : R < G₀.domain.chartRadius := G₀.domain.coreRadius_lt_chartRadius
  have hBU : closedBall (0 : Euclidean n) b ⊆ ball 0 R := closedBall_subset_ball hbR
  obtain ⟨D, c, C, hD, kCenter, hkCenter, hkDomain, T, hposition, hphysical, hgeometry, γ, hγ, hgap⟩ :=
    exists_positive_geometry_retained_seed_family_with_chart_centers_and_position_smoothness hn (U := ball (0 : Euclidean n) R)
      isOpen_ball hb (ball_subset_ball hbR.le)
  let J := (j : Fin D.chartCount) × Fin (D.patchCount j)
  obtain ⟨rsmall, _, _, hrsmall, _, _, _, hsmall⟩ := exists_common_phase_buffers
    (fun i : J ↦ (T i).reference.radius) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun i ↦ (T i).reference.radius_pos) (fun _ ↦ zero_lt_one)
  let r := min rsmall (b / 4)
  have hr : 0 < r := lt_min hrsmall (by positivity)
  have hrb : 3 * r < b := by
    have : r ≤ b / 4 := min_le_right _ _
    linarith
  have hradius (i : J) : 3 * r < (T i).reference.radius :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 3)).trans_lt
      (hsmall i).1
  have hball (i) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall 0 b :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      ball_subset_closedBall
  obtain ⟨εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp,
    σcover, hrc, hpositive, hcarrier⟩ :=
    exists_retained_family_with_generic_leading
      (I := (j : Fin D.chartCount) × Fin (D.patchCount j)) hn G₀ hb hbR hR
      (fun i ↦ D.patches i.1 i.2) (fun i ↦ (hD.2.2.2.2.1 i.1 i.2).1) T hball
  obtain ⟨Ωc, ρc, Bc, gc, μc, Bfull, hsource, hfullTime, hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover,
    V, hV, hgeneric, capLead, hcapLead, _, hlead⟩ := hcarrier
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, ?_⟩
  refine ⟨kCenter, hkCenter, hkDomain, T, hposition, hphysical, hgeometry,
    γ, hγ, hgap, r, hr, hrb, hradius, ?_⟩
  refine ⟨εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp,
    σcover, hrc, hpositive, ?_⟩
  refine ⟨Ωc, ρc, Bc, gc, μc, Bfull, hsource, hfullTime, hgeometryc, hworking,
    εcarrier, ρdet, hcell, hcarrierCover, V, hV, hgeneric, ?_⟩
  intro εframe hεframe qext hqcenter hqradius k hk hkD
  have hz (i) := ((hD.2.2.2.2.1 i.1 i.2).2.2.1 (k i) (hkD i)).1
  have hinc (i) := ((hD.2.2.2.2.1 i.1 i.2).2.2.1 (k i) (hkD i)).2.2.2
  have hd (i) : fderiv ℝ (fun w ↦ incidence (k i)
      ((D.patches i.1 i.2).toFun w)) (D.roots i.1 i.2 (k i))
      (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le
      ((hD.2.2.2.2.1 i.1 i.2).2.2.2 (k i) (hkD i) _ (fun j ↦ (hz i j).le)))
  obtain ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, hboxes,
    capQ, hcapQ, _, hquotient⟩ :=
    FixedReferenceProfiles.exists_source_scale_cap_for_fixed_reference_history_profiles
      (I := (j : Fin D.chartCount) × Fin (D.patchCount j)) G₀ hb hbR hR
      qext hqcenter hqradius (fun i ↦ D.patches i.1 i.2)
      (fun i ↦ (hD.2.2.2.2.1 i.1 i.2).1) T hball
      (fun i ↦ D.roots i.1 i.2 (k i)) k hz hk hinc hd
  obtain ⟨ρFext, ρText, qextRad, sext, eext, cFext, bFext, cText, bText,
    VFext, LFext, VText, LText, hextBoxes, hcutoffs⟩ :=
    exists_source_scale_cap_for_fixed_reference_joint_extensions
      (I := (j : Fin D.chartCount) × Fin (D.patchCount j)) hn G₀ hb hbR hR
      qext hqcenter hqradius (fun i ↦ D.patches i.1 i.2)
      (fun i ↦ (hD.2.2.2.2.1 i.1 i.2).1) T hball
      (fun i ↦ D.roots i.1 i.2 (k i)) k hz hk hinc hd hεframe
  obtain ⟨ψF, χF, ψT, χT, hcutoffs, εtransport, gtransport,
    hεtransport, hgtransport, htransport⟩ := hcutoffs
  obtain ⟨transportCenters, transportRow, transportCol, ρtransport, Ltransport,
    hρtransport, Ωtransport, hdomains, hcover, Dq, Dt, hDq, hDt,
    capExt, hcapExt, _, hext⟩ := htransport
  obtain ⟨εsmall, _, _, hεsmall, _, _, _, hsmall⟩ := exists_common_phase_buffers
    (fun i ↦ min (εlead i) εtransport) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun i ↦ lt_min (hεlead i) hεtransport) (fun _ ↦ zero_lt_one)
  let εcommon := min εsmall (r / 2)
  have hεcommon : 0 < εcommon := lt_min hεsmall (half_pos hr)
  have hcommonLead (i) : εcommon ≤ εlead i := by
    have h := (hsmall i).1.trans_le (min_le_left _ _)
    have hle : εcommon ≤ εsmall := min_le_left _ _
    linarith only [h, hle, hεsmall]
  have hcommonTransport (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) :
      εcommon ≤ εtransport := by
    have h := (hsmall i).1.trans_le (min_le_right _ _)
    have hle : εcommon ≤ εsmall := min_le_left _ _
    linarith only [h, hle, hεsmall]
  refine ⟨hz, hinc, hd, ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT,
    hboxes, ?_⟩
  refine ⟨ρFext, ρText, qextRad, sext, eext, cFext, bFext, cText, bText,
    VFext, LFext, VText, LText, hextBoxes, ?_⟩
  refine ⟨ψF, χF, ψT, χT, hcutoffs, εtransport, gtransport,
    hεtransport, hgtransport, ?_⟩
  refine ⟨transportCenters, transportRow, transportCol, ρtransport, Ltransport,
    hρtransport, Ωtransport, hdomains, hcover, Dq, Dt, hDq, hDt,
    εcommon, hεcommon, (min_le_right _ _).trans_lt (half_lt_self hr), ?_, ?_⟩
  · intro i
    exact ⟨(prod_mono (ball_subset_ball (hcommonLead i)) Subset.rfl).trans (hV i).2.2,
      (prod_mono (closedBall_subset_closedBall (hcommonTransport i)) Subset.rfl).trans
        (hcover i)⟩
  intro p orders margin extendedMargin hmargin hextendedMargin cap hcap
  obtain ⟨capMargin, hcapMargin, hcapMarginCap, hcapMargin1, hmargins⟩ :=
    exists_source_scale_full_and_extended_margin_interval G₀
      (isCompact_closedBall (0 : Euclidean n) b) p orders margin extendedMargin
      hmargin hextendedMargin (half_pos hεframe)
      (lt_min hcap (lt_min hcapLead (lt_min hcapQ hcapExt)))
  obtain ⟨θ, hθ, hθcap, hθ1, H, hHdomain, hHmap, hmean⟩ :=
    exists_relative_matched_seed_mean hn G₀ D hD
      (ball_subset_ball hR.le) T (isCompact_closedBall (0 : Euclidean n) b)
      hBU hball hγ hgap hcapMargin
  have hθMargin : θ ≤ capMargin := hθcap.le
  have hθcapAll := hθcap.trans hcapMarginCap
  refine ⟨θ, hθ, hθcapAll.trans_le (min_le_left _ _), hθ1,
    H, hHdomain, hHmap, ?_, hmean⟩
  intro σ hσ hσ1
  dsimp only
  have hρ : 0 < θ * σ := mul_pos hθ hσ
  have hρθ : θ * σ ≤ θ := mul_le_of_le_one_right hθ.le hσ1
  have hρ1 : θ * σ ≤ 1 := hρθ.trans hθ1
  have hρcaps := hρθ.trans_lt hθcapAll
  have hleadCap : θ * σ ≤ capLead :=
    (hρcaps.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hquotientCap : θ * σ ≤ capQ :=
    ((hρcaps.le.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hextCap : θ * σ ≤ capExt :=
    ((hρcaps.le.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  have hcompose : sourceDilation H.map σ = sourceDilation G₀.map (θ * σ) := by
    rw [hHmap]
    funext x
    simp only [sourceDilation, smul_smul, mul_inv_rev]
  obtain ⟨hfull, hclose, hsmooth, hextended⟩ :=
    hmargins (θ * σ) ⟨hρ, hρθ.trans hθMargin⟩
  let Gwide := sourceDilationReference G₀ hρ hρ1
  obtain ⟨δ, hδ, C₀, hC₀, κ, hκ, hnear⟩ :=
    CurrentGeometricNeighborhood.exists_cube_frame_neighborhood Gwide hb hbR hR hεframe hclose
  have hrchart : εcommon / 2 < Gwide.domain.chartRadius := by
    change εcommon / 2 < G₀.domain.chartRadius
    have hcommonr : εcommon < r := (min_le_right _ _).trans_lt (half_lt_self hr)
    linarith
  let domain : LocalDomain :=
    ⟨εcommon / 4, εcommon / 2, by positivity, by linarith,
      hrchart.trans G₀.domain.chartRadius_lt_half⟩
  let G : FlatReference n := { Gwide with
    domain := domain
    fullNormalRank := fun x hx ↦ Gwide.fullNormalRank x
      (ball_subset_ball hrchart.le hx) }
  have hmap : G.map = sourceDilation G₀.map (θ * σ) := rfl
  have hnearG := hnear univ G.map isOpen_univ (subset_univ _)
    G.contDiff.contDiffOn (by simpa only [show G.map = Gwide.map from rfl, sub_self,
      cNorm_zero] using hδ)
  obtain ⟨hi, hrank, hlowF, hmet, hnormal, _, _⟩ := hnearG
  refine ⟨hρ, hρcaps.trans_le (min_le_left _ _), hρ1, G, hmap,
    hmap.trans hcompose.symm, rfl, rfl, hfull, hsmooth, hextended,
    ⟨δ, C₀, κ, hδ, hC₀, hκ, hnear, hi, hrank, hlowF, hmet, hnormal⟩,
    hlead (θ * σ) hρ hleadCap G hmap,
    hquotient (θ * σ) hρ hquotientCap G hmap,
    hext (θ * σ) hρ hextCap G hmap, ?_⟩
  intro gtarget Vtarget hVtarget h0target hgtarget kMin horder
  exact exists_normalized_common_target_initialization G hρ hVtarget h0target hgtarget horder

end JanetCartan.PhysicalSeed
