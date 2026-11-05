module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceLabels

/-!
# A measurement cap for the original finite scalar domains

Shrink the physical radius after the original finite conic family has been
chosen. Its entire closed carrier supports then lie in the original null-flow
cylinders, simultaneously for every supplied chart. The incidence root and
the scalar-cell center may differ. Neither masks nor scalar domains are
reselected. This supplies the support premise of
`retained_chart_normalized_kernel_and_integrals` and the common measurement
choice in `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open FlowConstruction NullTransport ActualFlow FlowAmplitude
open FullPhaseCharts.ActualComparison

/-- One physical cap puts the FULL original carrier supports in all retained
scalar output cylinders, before any source scale or choice of ODE solution.
The original compatibility estimate `8 * rcomp ≤ Rc / 32` is exported by
`ChartCenters.CarrierData`. Only physical time is reduced; the original
angular width, incidence center and initial scalar class are kept
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_scalar_measurement_cap
    {n : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (zCell zRoot : ι → Euclidean 3)
    {rCarrier a a' Rc τ rcomp δcomp : ι → ℝ}
    (ha' : ∀ i, 0 < a' i) (hτ : ∀ i, 0 < τ i)
    (haa : ∀ i, a' i ≤ a i) (har : ∀ i, a' i ≤ rCarrier i)
    (hcompRadius : ∀ i, 8 * rcomp i ≤ Rc i / 32)
    (E : ι → Set (Euclidean n × CarrierParameter))
    (houter : ∀ i, coefficientDomain (zRoot i) (rCarrier i) (6 * a i) ⊆ E i)
    (hcomp : ∀ i, MapsTo (densityCoordinates (T i)) (E i)
      (Ioo (-δcomp i) (δcomp i) ×ˢ
        ball ((0 : Euclidean (n - 1)), zCell i) (rcomp i))) :
    ∃ cap > (0 : ℝ), (∀ i, cap < a' i ∧ cap < τ i) ∧
      ∀ r : ℝ, 0 < r → 6 * r < cap → ∀ i,
        MapsTo (densityCoordinates (T i))
          (closedBall (0 : Euclidean n) (6 * r) ×ˢ carrierSupport (zRoot i) (r := a' i))
          (Ioo (-τ i) (τ i) ×ˢ
            ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 32)) := by
  obtain ⟨cap, hcap, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (fun i ↦ lt_min (ha' i) (hτ i))
  have hcapBounds (i) : cap < a' i ∧ cap < τ i := by
    exact lt_min_iff.mp (by simpa only [zero_add] using hsmall i)
  refine ⟨cap, hcap, hcapBounds, ?_⟩
  intro r hr hrcap i p hp
  have hE := NormalizedMeasurement.source_product_subset_retained_cell (zRoot i) hr
    (hrcap.trans (hcapBounds i).1) (haa i) (har i) (houter i) hp
  have hlabel := (hcomp i hE).2
  have hrcomp : 0 < rcomp i := lt_of_le_of_lt dist_nonneg (mem_ball.mp hlabel)
  refine ⟨?_, ball_subset_ball (by linarith [hcompRadius i]) hlabel⟩
  change (adaptedCoordinates (T i).data.adapted p.1).1 ∈ Ioo (-τ i) (τ i)
  rw [adaptedCoordinates_apply]
  apply abs_lt.mp
  have hnorm : ‖p.1‖ ≤ 6 * r := mem_closedBall_zero_iff.mp hp.1
  have htime := abs_real_inner_le_norm (T i).data.adapted.normal p.1
  rw [(T i).data.adapted.normal_unit, one_mul] at htime
  exact (htime.trans hnorm).trans_lt (hrcap.trans (hcapBounds i).2)

/-- The original angular support and fixed periodic cutoff satisfy the
literal kernel's scalar-domain premise. This specializes the preceding full
closed-support inclusion without choosing a new mask or label
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-normalized`). -/
theorem measurement_angular_support_in_retained_cylinder
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (zCell zRoot : Euclidean 3) (η₀ : Euclidean (n - 1))
    {r a' width Rc τ : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (ha' : 0 < a') (hwidth : 0 < width)
    (hbuffer : MapsTo (densityCoordinates T)
      (closedBall (0 : Euclidean n) (6 * r) ×ˢ carrierSupport zRoot (r := a'))
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), zCell) (Rc / 32))) :
    ∀ (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1)),
      FixedCutoffs.periodic hr hcell 1 x ≠ 0 → angularMask zRoot η₀ ha' hwidth z η ≠ 0 →
      densityCoordinates T (AmplitudeBound.centeredTorusRepresentative x, z) ∈
        Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), zCell) (Rc / 32) := by
  intro x z η hx hz
  apply hbuffer
  have hs : (z, η) ∈ tsupport (Function.uncurry (angularMask zRoot η₀ ha' hwidth)) :=
    subset_tsupport _ hz
  refine ⟨?_, (angularMask_tsupport zRoot η₀ ha' hwidth hs).1⟩
  apply closedBall_subset_closedBall (by linarith : 4 * r ≤ 6 * r)
  exact FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx)

/-- A single physical cap retains the ORIGINAL initial scalar ball for all
positive source contractions on the FULL fixed carrier support. The label
bound is derived from the original full-modulation working cylinder; the
divided source footpoint is controlled by its retained forward C¹ estimate.
No source-dependent density extension or inverse derivative estimate is used.

The seed chart and its forward bound are outputs of the common initializer.
Consumers: the two original-label range premises of
`NormalizedCarrierBaseline.exists_actual_source_density_coefficient_controls`
and the normalized row's arbitrary positive-density class
(`app:ch_background:eq:bg-mixed-input`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_source_label_measurement_cap
    {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (zCell zRoot : ι → Euclidean 3)
    {rCarrier a a' L Rc τ Mc rcomp δcomp σcover τfull : ι → ℝ}
    (ha' : ∀ i, 0 < a' i) (hL : ∀ i, 0 < L i) (hRc : ∀ i, 0 < Rc i)
    (hτ : ∀ i, 0 < τ i) (hMc : ∀ i, 0 < Mc i) (hσcover : ∀ i, 0 < σcover i)
    (haa : ∀ i, a' i ≤ a i) (har : ∀ i, a' i ≤ rCarrier i)
    (hcompRadius : ∀ i, 8 * rcomp i ≤ Rc i / 32)
    (E : ι → Set (Euclidean n × CarrierParameter))
    (houter : ∀ i, coefficientDomain (zRoot i) (rCarrier i) (6 * a i) ⊆ E i)
    (hcomp : ∀ i, MapsTo (densityCoordinates (T i)) (E i)
      (Ioo (-δcomp i) (δcomp i) ×ˢ
        ball ((0 : Euclidean (n - 1)), zCell i) (rcomp i)))
    (hgraph : ∀ i, MapsTo (LeadingPrimitive.carrierGraph (T i)) (E i)
      (ball ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i))) (σcover i)))
    (hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i))) (2 * σcover i) ⊆
        (coordinates (adaptedCoordinates (T i).data.adapted)).symm ''
          (Icc (-τfull i / 2) (τfull i / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)),
              (zCell i, (T i).reference.spatialPatch (zCell i))) (L i / 64))) :
    ∃ cap > (0 : ℝ), (∀ i, cap < a' i) ∧
      ∀ r : ℝ, 0 < r → 6 * r < cap → ∀ i,
      let Ksupport := closedBall (0 : Euclidean n) (6 * r) ×ˢ
        carrierSupport (zRoot i) (r := a' i)
      MapsTo (densityCoordinates (T i)) Ksupport
        (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τ i)) ∧
      ∀ (Ω K : Set (Euclidean n × Euclidean 3)) (B : ℝ)
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart (T i) Ω K ((0 : Euclidean (n - 1)), zCell i) (Rc i) B (τ i) row col F),
        cNorm (Icc (-τ i) (τ i) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 c.forward ≤ Mc i →
        ∀ σ ∈ Ioc (0 : ℝ) 1,
          MapsTo (densityFootpoint (T i) (NormalizedBackground.SourceGeometry.sourceTransportFlow
            c.inverse σ)) Ksupport
            (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 16)) := by
  obtain ⟨cap, hcap, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (fun i ↦ lt_min (ha' i) (lt_min (half_pos (hτ i))
      (div_pos (hL i) (mul_pos (show (0 : ℝ) < 64 by norm_num) (hMc i)))))
  have hcapBounds (i) : cap < a' i ∧ cap < τ i / 2 ∧ cap < L i / (64 * Mc i) := by
    simpa only [zero_add, lt_min_iff] using hsmall i
  refine ⟨cap, hcap, fun i ↦ (hcapBounds i).1, ?_⟩
  intro r hr hrcap i Ksupport
  have hE : Ksupport ⊆ E i :=
    NormalizedMeasurement.source_product_subset_retained_cell (zRoot i) hr
      (hrcap.trans (hcapBounds i).1) (haa i) (har i) (houter i)
  have htime (p : Euclidean n × CarrierParameter) (hp : p ∈ Ksupport) :
      |(densityCoordinates (T i) p).1| < cap := by
    change |(adaptedCoordinates (T i).data.adapted p.1).1| < cap
    rw [adaptedCoordinates_apply]
    have h := abs_real_inner_le_norm (T i).data.adapted.normal p.1
    rw [(T i).data.adapted.normal_unit, one_mul] at h
    exact (h.trans (mem_closedBall_zero_iff.mp hp.1)).trans_lt hrcap
  have houtput : MapsTo (densityCoordinates (T i)) Ksupport
      (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τ i)) := by
    intro p hp
    refine ⟨abs_le.mp ((htime p hp).trans (hcapBounds i).2.1).le, ?_⟩
    exact ball_subset_closedBall (ball_subset_ball (by linarith [hcompRadius i, hRc i])
      (hcomp i (hE hp)).2)
  refine ⟨houtput, ?_⟩
  intro Ω K B F row col c hforward σ hσ p hp
  exact ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.sourceDensityFootpoint_mem_original_ball_of_forward_cNorm
    (T i) (hL i) (hRc i) (hτ i) (hMc i) c hforward (houtput hp)
    ((ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.densityCoordinates_mem_original_cylinder
      (T i) (zCell i) (hσcover i) (hgraph i) (hworking i) (hE hp)).2)
    ((htime p hp).trans (hcapBounds i).2.2) hσ.1 hσ.2

end JanetCartan.ContinuumRow.NormalizedSelection
