module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Comparison

/-!
# The original carrier output cylinder at a distinct incidence center

The compatibility-radius producer proves `8 * rcomp ≤ Rc / 32` before finite
selection. This bound, together with the retained coordinate containment,
allows a restriction of physical time preserving all zero-position carrier
points. No angular mask is shrunk. The strengthened `ChartCenters.CarrierData`
initializer exports the bound on its original selected witnesses. Applying
this restriction to that same menu remains an assembly obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open FullPhaseCharts.ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- At zero physical position, the weighted comparison's output cylinder
requires precisely the original carrier-center distance bound. This checks
the center condition for `exists_retained_conic_weighted_comparison` without
identifying `zRoot` with `zCell` (`app:ch_background:eq:bg-Psi`). -/
theorem zero_densityCoordinates_mem_outputCylinder_iff (zCell zRoot : Euclidean 3)
    {Rc τ : ℝ} (hτ : 0 ≤ τ) :
    densityCoordinates T ((0 : Euclidean n), (zRoot 0, spectatorCenter zRoot)) ∈
      outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ ↔
        zRoot ∈ closedBall zCell (Rc / 64) := by
  have hcoord : densityCoordinates T ((0 : Euclidean n), (zRoot 0, spectatorCenter zRoot)) =
      (0, ((0 : Euclidean (n - 1)), zRoot)) := by
    change ((adaptedCoordinates T.data.adapted (0 : Euclidean n)).1,
      (adaptedCoordinates T.data.adapted (0 : Euclidean n)).2,
      parameter (zRoot 0, spectatorCenter zRoot)) = _
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, parameter_apply,
      carrierParameters_spectatorCenter]
  rw [hcoord]
  simp only [outputCylinder, mem_prod, mem_Icc, mem_closedBall, Prod.dist_eq,
    dist_self, max_eq_right (dist_nonneg : 0 ≤ dist zRoot zCell)]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨⟨by linarith, by linarith⟩, h⟩

/-- The primitive comparison-radius bound gives an open output-cylinder
restriction preserving EVERY zero-position carrier point. Its producer is
`CarrierCompatibility.exists_comparison_radii`, whose `8 * rcomp ≤ Rc / 32`
conclusion is used in the actual local full-modulation construction. The
coordinate containment is exactly the retained compatibility-cell output.

Consumer: `exists_retained_conic_weighted_comparison.hSflow`. The strengthened
`ChartCenters.CarrierData` initializer exports this radius bound; its actual
application on the SAME selected cells remains required. Sources:
`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-frame`, and
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_original_outputCylinder_region (zCell : Euclidean 3)
    {Rc τ rcomp δcomp : ℝ} (hτ : 0 < τ) (hrcomp : 0 < rcomp)
    (hrc : 8 * rcomp ≤ Rc / 32)
    {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E)
    (hcomp : MapsTo (densityCoordinates T) E
      (Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), zCell) rcomp)) :
    ∃ E' : Set (Euclidean n × CarrierParameter), IsOpen E' ∧ E' ⊆ E ∧
      (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ E' ↔
        ((0 : Euclidean n), z) ∈ E) ∧
      MapsTo (densityCoordinates T) E'
        (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) := by
  let E' := E ∩ (fun p ↦ (densityCoordinates T p).1) ⁻¹' Ioo (-(τ / 2)) (τ / 2)
  refine ⟨E', hE.inter (isOpen_Ioo.preimage (densityCoordinates T).continuous.fst),
    inter_subset_left, ?_, ?_⟩
  · intro z
    constructor
    · exact fun h ↦ h.1
    · intro hz
      refine ⟨hz, ?_⟩
      change (adaptedCoordinates T.data.adapted (0 : Euclidean n)).1 ∈
        Ioo (-(τ / 2)) (τ / 2)
      simpa only [map_zero, Prod.fst_zero, mem_Ioo, neg_lt_zero] using
        And.intro (half_pos hτ) (half_pos hτ)
  · intro p hp
    refine ⟨Ioo_subset_Icc_self hp.2, ?_⟩
    exact ball_subset_closedBall ((ball_subset_ball (by linarith : rcomp ≤ Rc / 64))
      (hcomp hp.1).2)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
