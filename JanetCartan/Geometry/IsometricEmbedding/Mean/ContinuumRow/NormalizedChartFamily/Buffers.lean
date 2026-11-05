module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceLabels

/-!
# Common density buffers on supplied finite retained cells

The original comparison and full-modulation working cylinders give the three
domain hypotheses of the normalized retained baseline. Only the physical
radius is bounded; the supplied carrier regions and the scalar radii stay fixed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open CanonicalCarrier LeadingPrimitive
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction

/-- One physical cap gives exactly `hflow`, `hlabel` and `htime` of
`NormalizedCarrierBaseline.exists_finite_retained_original_density_reflected_baselines`
on every supplied coefficient product contained in the original cells. The
comparison radius and full-modulation working cylinder are the primitive
outputs of `ChartCenters.CarrierData`; the label conclusion is projected from
that SAME cylinder. The cap precedes every source scale and any restriction
to a coefficient norm region. Neither the incidence centers nor the carrier
masks are selected here (`app:ch_background:eq:bg-T`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_finite_retained_density_product_buffers
    {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (zCell : ι → Euclidean 3)
    {Ω K : ι → Set (Euclidean n × Euclidean 3)}
    {L Rc B τ rcomp δcomp σcover τfull : ι → ℝ} {row col : ι → Fin n}
    {F : Euclidean n → Euclidean N}
    (seed : (i : ι) → Chart (T i) (Ω i) (K i)
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τ i) (row i) (col i) F)
    (hL : ∀ i, 0 < L i) (hRc : ∀ i, 0 < Rc i) (hτ : ∀ i, 0 < τ i)
    (hσcover : ∀ i, 0 < σcover i)
    (hcompRadius : ∀ i, 8 * rcomp i ≤ Rc i / 32)
    (E : ι → Set (Euclidean n × CarrierParameter))
    (hcomp : ∀ i, MapsTo (densityCoordinates (T i)) (E i)
      (Ioo (-δcomp i) (δcomp i) ×ˢ
        ball ((0 : Euclidean (n - 1)), zCell i) (rcomp i)))
    (hgraph : ∀ i, MapsTo (carrierGraph (T i)) (E i)
      (ball ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i))) (σcover i)))
    (hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i)))
        (2 * σcover i) ⊆
      (coordinates (adaptedCoordinates (T i).data.adapted)).symm ''
        (Icc (-τfull i / 2) (τfull i / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)),
            (zCell i, (T i).reference.spatialPatch (zCell i))) (L i / 64))) :
    ∃ cap > (0 : ℝ), ∀ R : ℝ, R ≤ cap → ∀ i (V : Set CarrierParameter),
      ball (0 : Euclidean n) R ×ˢ V ⊆ E i →
      MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) R ×ˢ V)
        (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τ i)) ∧
      (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V, (densityCoordinates (T i) p).2 ∈
        closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64)) ∧
      (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
        |(densityCoordinates (T i) p).1| < L i / (64 *
          (cNorm (Icc (-τ i) (τ i) ×ˢ
            closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8))
            1 (seed i).forward + 1))) := by
  let Mc (i : ι) := cNorm (Icc (-τ i) (τ i) ×ˢ
    closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (seed i).forward + 1
  have hMc (i : ι) : 0 < Mc i := by
    have := cNorm_nonneg (Icc (-τ i) (τ i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (seed i).forward
    dsimp only [Mc]
    linarith
  obtain ⟨cap, hcap, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (fun i ↦ lt_min (half_pos (hτ i))
      (div_pos (hL i) (mul_pos (by norm_num : (0 : ℝ) < 64) (hMc i))))
  have hcapBounds (i : ι) : cap < τ i / 2 ∧ cap < L i / (64 * Mc i) := by
    simpa only [zero_add, lt_min_iff] using hsmall i
  refine ⟨cap, hcap, ?_⟩
  intro R hR i V hproduct
  have htime (p : Euclidean n × CarrierParameter) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :
      |(densityCoordinates (T i) p).1| < cap := by
    change |(adaptedCoordinates (T i).data.adapted p.1).1| < cap
    rw [adaptedCoordinates_apply]
    have hh := abs_real_inner_le_norm (T i).data.adapted.normal p.1
    rw [(T i).data.adapted.normal_unit, one_mul] at hh
    exact (hh.trans_lt (mem_ball_zero_iff.mp hp.1)).trans_le hR
  refine ⟨?_, ?_, fun p hp ↦ (htime p hp).trans (hcapBounds i).2⟩
  · intro p hp
    refine ⟨abs_le.mp ((htime p hp).trans (hcapBounds i).1).le, ?_⟩
    exact ball_subset_closedBall (ball_subset_ball
      (by linarith [hcompRadius i, hRc i] : rcomp i ≤ Rc i / 64)
      (hcomp i (hproduct hp)).2)
  · intro p hp
    exact (RetainedRowGeometry.densityCoordinates_mem_original_cylinder
      (T i) (zCell i) (hσcover i) (hgraph i) (hworking i) (hproduct hp)).2

end JanetCartan.ContinuumRow.NormalizedChartFamily
