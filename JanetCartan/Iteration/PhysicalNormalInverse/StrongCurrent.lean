module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongGeometry
public import JanetCartan.Iteration.PhysicalNormalInverse.CurrentInverse
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongCurrentApplication

/-!
# Current inverse geometric application on the one strengthened seed

Apply the physical current-inverse constructor to `PhysicalSeed`'s literal
retained geometry, selected with the shared `strongCappedExtra` callback.
The SAME callback must be supplied to `StrongSource`. The raw cap retains all
earlier phase/scalar/positive user extras. No old weak tuple is identified with
this one, and the empty-history witness proves only static working geometry.

The numeric inverse cap and scalar budget are retained before the final source
scale, densities and histories. The actual strong source coercivity and the
same physical leading callback remain the explicit consumers of the returned
tail; this geometric application alone is not a completed current inverse.
Consumer: `app:ch_background:prop:bg-inverse` and the uncut current auxiliary.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius InnerProductSpace
namespace JanetCartan.PhysicalNormalInverse.StrongCurrent
open ContinuumInverse PhysicalSeed
open JanetCartan.PhysicalNormalInverse.StrongGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation ProjectedStressFrame
open ContinuumRow LeadingPrimitive CanonicalCarrier CanonicalConic TransportKernel CarrierNormalRealization
open ContinuumNormalReduction.TransportSymbol ContinuumNormal.RetainedFrozen
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedRowGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2
open ContinuumAdjoint ContinuumAdjoint.Canonical CarrierSobolev
open ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumAdjoint.Canonical.AmplitudeProfiles AmbientResponse LeadingWave

attribute [local instance 10] Classical.propDecidable

check_strong_physical_inverse_application initialized :=
  fun {n : ℕ} (hn : 5 ≤ n)
    (εframe : ℝ) (hεframe : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n))
    (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
    (k : ((j : Fin (OriginalBoundary.D hn).chartCount) ×
      Fin ((OriginalBoundary.D hn).patchCount j)) → Euclidean n)
    (hk : ∀ i, k i ≠ 0) (hkD : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.1)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmargin : ∀ j ∈ orders, 0 < margin j)
    (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
    (aExtra : (q : IncidenceCenter (OriginalBoundary.D hn)) →
      (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1)) →
      ↥(OriginalBoundary.centers hn ⟨q.1.1, l⟩) → {ε : ℝ // 0 < ε}) ↦
  let D := strong_boundary% D
  let b := strong_boundary% b
  let R := strong_boundary% R
  let T := strong_boundary% T
  have hD := strong_boundary% hD
  have hb := strong_boundary% b_pos
  have hbR := strong_boundary% b_lt_R
  let H := strong_reference% H
  have hHdomain := strong_reference% fact5
  have hHchart : R < H.domain.chartRadius :=
    lt_of_lt_of_eq (strong_boundary% R_lt_chartRadius)
      (congrArg LocalDomain.chartRadius hHdomain).symm
  let Tm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) ↦ T ⟨b, l⟩
  let Im := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) ↦
    ↥((strong_boundary% centers) ⟨b, l⟩)
  let L := strong_boundary% L
  let τ := strong_boundary% τ
  let _Rc := strong_boundary% Rc
  let _τc := strong_boundary% τc
  let Ωc := strong_boundary% Ωc
  let ρc := strong_boundary% ρc
  let Bc := strong_boundary% Bc
  let σcover := strong_boundary% σcover
  let _ρdet := strong_boundary% ρdet
  let Rproduct := strong_boundary% Rproduct
  let εcarrier := strong_boundary% εcarrier
  have hpositive := strong_boundary% comparison_pos
  have hworking := strong_boundary% comparison_cover
  have hcell := strong_boundary% carrier_cells
  have hproduct := strong_boundary% density_product_geometry
  let Kin := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
    closedBall ((0 : Euclidean (n - 1)), j.1.1) (L ⟨b, l⟩ j / 8)
  let Jfull := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
    closedBall ((0 : Euclidean n), (j.1.1, (Tm b l).reference.spatialPatch j.1.1)) (σcover ⟨b, l⟩ j)
  let E := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
    ball (0 : Euclidean n) (Rproduct ⟨b, l⟩ j) ×ˢ
      ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier ⟨b, l⟩ j)
  have hball (b' : Fin D.chartCount) (l : Fin (D.patchCount b')) :
      closedBall (0 : Euclidean n) (Tm b' l).data.localReference.stateRadius ⊆ closedBall 0 b :=
    (frameBall_subset_of_stateDomain (T ⟨b', l⟩).data.localReference
      ((strong_boundary% stateDomain_subset_ball) ⟨b', l⟩)).trans ball_subset_closedBall
  have hgraph (b' : Fin D.chartCount) (l : Fin (D.patchCount b')) (j : Im b' l) :
      MapsTo (LeadingPrimitive.carrierGraph (Tm b' l)) (E b' l j) (Jfull b' l j) :=
    (((hcell ⟨b', l⟩ j).2.2.1).mono_left
      (hproduct ⟨b', l⟩ j).2.2.2.2.2.2.1).mono_right ball_subset_closedBall
  let cappedExtra := strongCappedExtra hn aExtra
  let cell := strong_selected% cell
  let centers := strong_selected% centers
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let patch := fun i : ι ↦ (⟨i.1.1.1.1, i.2⟩ : (j : Fin D.chartCount) × Fin (D.patchCount j))
  let chosen := fun i : ι ↦ cell i.1.1 i.2
  let family := fun i : ι ↦ T (patch i)
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let a' := strong_selected% a'
  have hrmask := strong_selected% _hr
  have hamask := strong_selected% _ha
  have hr' := strong_selected% hr'
  have ha' := strong_selected% ha'
  have hmaskCell := strong_selected% hcell
  have hηb := strong_selected% hηb
  have hextra := strong_selected% fact22
  have houter := strong_selected% fact23
  let _δ := strong_selected% δ
  have hδ := strong_selected% fact33
  let Dc := strong_selected% Dc
  let p₀ := strong_selected% p₀
  let q₀ := strong_selected% q₀
  let A := strong_selected% A
  let Gphase := strong_selected% Gphase
  have hroot (i : ι) : z i ∈ parameterInterior (D.patches (patch i).1 (patch i).2).radius :=
    ((hD.2.2.2.2.1 i.1.1.1.1 i.2).2.2.1 i.1.1.1.2 i.1.1.2.2).1
  have hcenter (i : ι) : chartCenter (z i) ∈ E i.1.1.1.1 i.2 (chosen i) :=
    (strong_selected% fact1) i.1.1 i.2
  have selectedCaps (i : ι) :=
    InitializedCappedHistory.selected_raw_cap_le (by omega : 0 < n) hD Tm Im
      (isCompact_closedBall _ _) (closedBall_subset_ball hbR) hball Kin
      Jfull (fun _ _ _ ↦ isCompact_closedBall _ _) E
      (fun _ _ _ ↦ isOpen_ball.prod isOpen_ball) hgraph
      i.1.1 i.2 (chosen i) (hcenter i)
      (a := a' i) (userCap := (aExtra i.1.1 i.2 (chosen i)).val)
      (hextra i)
  have hrawCap (i : ι) : a' i ≤
      (exists_current_rawAdjoint_cap_on_supplied_geometry (N := embeddingDimension n)
        (by omega : 0 < n) (hD.2.2.2.2.1 i.1.1.1.1 i.2).1 (family i)
        (isCompact_closedBall _ _) (closedBall_subset_ball hbR) (hball i.1.1.1.1 i.2)
        (Kin i.1.1.1.1 i.2 (chosen i)) (isCompact_closedBall _ _)
        (E i.1.1.1.1 i.2 (chosen i)) (isOpen_ball.prod isOpen_ball)
        (hgraph i.1.1.1.1 i.2 (chosen i)) (hroot i) (hcenter i)).choose := (selectedCaps i).2
  have hwork := working_geometry hn εframe hεframe qext hqcenter hqradius k hk hkD
    p orders margin extendedMargin hmargin hextendedMargin cap hcap
  let zCell := fun i : ι ↦ (chosen i).1.1
  let rowi := fun i : ι ↦ (strong_boundary% row) (patch i) (chosen i)
  let coli := fun i : ι ↦ (strong_boundary% col) (patch i) (chosen i)
  let zFull := fun i : ι ↦ (zCell i, (family i).reference.spatialPatch (zCell i))
  let Eouter := fun i : ι ↦ E i.1.1.1.1 i.2 (chosen i)
  let Wfull := fun i : ι ↦
    (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates (family i).data.adapted)).symm ''
      (Icc (-τ (patch i) (chosen i) / 2) (τ (patch i) (chosen i) / 2) ×ˢ
        closedBall ((0 : Euclidean (n - 1)), zFull i) (L (patch i) (chosen i) / 64))
  have hWfull (i : ι) : IsCompact (Wfull i) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image
      (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates (family i).data.adapted)).symm.continuous
  have hJW (i : ι) : Jfull i.1.1.1.1 i.2 (chosen i) ⊆ Wfull i :=
    (closedBall_subset_closedBall (by have := (hpositive (patch i) (chosen i)).2.2.2.2.2.2.2.2; linarith)).trans
      (hworking (patch i) (chosen i)).1
  have hfirst := strong_conic% first
  have hρ := strong_conic% hρi
  have hτi := strong_conic% hτi
  have hW := strong_conic% hW
  have hKiW := strong_conic% hKiW
  have hBi := strong_conic% hBi
  have hWBi := strong_conic% hWBi
  have hBiDom := strong_conic% hBiDom
  have hDRegion := strong_conic% hDregion
  have hfoot := strong_conic% hcontains
  have hsupport := strong_conic% hsupportD
  have hIt := strong_conic% hIt
  have hIIt := strong_conic% hIIt
  have hsegT := strong_conic% hsegT
  have hseg := strong_conic% hseg
  have hε := strong_conic% hη
  have hfreq := strong_conic% hfreq
  have hgap := strong_conic% hgap
  have hgeom := strong_conic% current_geometry
  have hp₀ (i : ι) := (hfirst i).1
  have _hq₀ (i : ι) := (hfirst i).2.1
  have har (i : ι) := (hfirst i).2.2.1
  have hcarrierDomain (i : ι) := (hfirst i).2.2.2.2.1
  have hrρ (i : ι) := (hfirst i).2.2.2.2.2.1
  have haρ (i : ι) := (hfirst i).2.2.2.2.2.2.1
  have hcJ (i : ι) := (hfirst i).2.2.2.2.2.2.2.2.1
  have hVphase (i : ι) := (hfirst i).2.2.2.2.2.2.2.2.2.1
  have hLV (i : ι) := (hfirst i).2.2.2.2.2.2.2.2.2.2.2.2
  PhysicalNormalInverse.exists_capped_source_history_inverse_with_scalar_admission
    (hn := by omega) H hb hbR hHchart family
    (fun i ↦ (hD.2.2.2.2.1 (patch i).1 (patch i).2).1)
    (fun i ↦ hball i.1.1.1.1 i.2) Dc zCell
    (fun i ↦ (hpositive (patch i) (chosen i)).2.1)
    (fun _ ↦ isCompact_closedBall _ _) zFull
    (fun i ↦ (hpositive (patch i) (chosen i)).2.2.2.2.2.2.2.2)
    (fun _ ↦ rfl) (fun i ↦ hwork.1 (patch i) (chosen i))
    (fun i ↦ hwork.2 (patch i) (chosen i)) Wfull hWfull hJW Eouter
    (fun _ ↦ isOpen_ball.prod isOpen_ball)
    (fun i ↦ hgraph i.1.1.1.1 i.2 (chosen i))
    (fun i ↦ (hDRegion i).trans inter_subset_left)
    (fun i ↦ ((hcell (patch i) (chosen i)).2.2.2.2.1).trans' (hproduct (patch i) (chosen i)).2.2.2.2.2.2.1)
    (fun i ↦ ((hcell (patch i) (chosen i)).2.2.2.2.2.1).trans' (hproduct (patch i) (chosen i)).2.2.2.2.2.2.1)
    (fun i ↦ ((0 : Euclidean n), zCell i))
    (fun i ↦ (hcell (patch i) (chosen i)).2.1)
    (fun i ↦ (hcell (patch i) (chosen i)).2.2.2.2.2.2.1)
    (fun i ↦ (hcell (patch i) (chosen i)).2.2.2.2.2.2.2.1)
    (fun i ↦ ((hcell (patch i) (chosen i)).2.2.2.2.2.2.2.2).mono_left
      ((Dc i).field.ball_subset.trans ((hDRegion i).trans inter_subset_left) |>.trans
        (hproduct (patch i) (chosen i)).2.2.2.2.2.2.1))
    z hroot hcenter hηb hrmask hr' ha' hmaskCell hrawCap hamask har
    (fun i ↦ (houter i).2.2.2.2.2) (fun i ↦ (houter i).2.2.1)
    (fun i ↦ (houter i).2.2.2.1) (fun i ↦ (houter i).2.2.2.2.1)
    hcarrierDomain (fun i ↦ (houter i).2.1) hsupport p₀ hp₀ q₀ hρ hτi haρ hrρ
    hW hKiW hBi hWBi hBiDom hfoot hIt hIIt hsegT hseg A hε hgap
    (fun _ ↦ hδ) hfreq hcJ hVphase hLV Gphase
    hgeom
    (Ωflow := fun i ↦ Ωc (patch i) (chosen i))
    (Kflow := fun i ↦ closedBall ((0 : Euclidean n), zCell i) (ρc (patch i) (chosen i)))
    (Bflow := fun i ↦ Bc (patch i) (chosen i))
    (fun i ↦ (hpositive (patch i) (chosen i)).2.2.2.1)
    (fun i ↦ (hpositive (patch i) (chosen i)).2.2.2.2.1)
    (fun i ↦ (hproduct (patch i) (chosen i)).1)
    (fun i ↦ (hproduct (patch i) (chosen i)).2.2.2.2.2.2.2.2.2.1)
    (fun i ↦ (hproduct (patch i) (chosen i)).2.2.2.2.2.2.2.2.2.2.1)
    (fun i ↦ (hproduct (patch i) (chosen i)).2.2.2.2.2.2.2.2.2.2.2.1)
    (fun i ↦ (hDRegion i).trans inter_subset_right) rowi coli
    (fun i F current ↦ ((hproduct (patch i) (chosen i)).2.2.2.2.2.2.2.2.2.2.2.2 F
      (rowi i) (coli i) current).1)

end JanetCartan.PhysicalNormalInverse.StrongCurrent

cache_strong_current_inverse_cap
