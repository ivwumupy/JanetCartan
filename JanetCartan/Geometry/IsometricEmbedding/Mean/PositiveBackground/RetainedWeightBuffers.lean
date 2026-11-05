module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.WeightBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.Buffers

/-!
# Retained flow domains on the original external-weight supports

Choose one physical buffer using the already selected finite family and its
original external weights. The retained comparison and working-cylinder
geometry supplies the scalar-coordinate domains, original label bounds and
time bounds on the full support, including the weight collars.

The resulting radius precedes the source scale. Its doubled buffer leaves
room for the closed `6*r` source neighborhood used in `RetainedSource`.
In particular, `hseed` and `hcurrent` there follow by restricting these maps;
they do not require separately chosen domains at each source scale.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier LeadingPrimitive RetainedAssembly.ExternalWeights
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction
set_option backward.isDefEq.respectTransparency false

/-- The original external weights have one common retained flow buffer.
The full-support product lies in the original cells and in the domain of every
chart with the same retained parameters. The original scalar label and time
bounds are also retained, for the normalized density-profile producers
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-normalized`,
`app:ch_background:prop:bg-positive`, `new:sec:order-of-choices`).

Consumers: the seed/current domain maps of
`exists_retained_fixedSource_sobolev_bounds` and the full-support scalar
profiles used by preparation. The finite seed family, comparison cells and
weights are supplied by the original selection; no inverse estimate, source
bound, or alternative choice of weights is an input. -/
theorem exists_retained_weight_flow_buffer
    {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (h0U : (0 : Euclidean n) ∈ U)
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
    (E : ι → Set (Euclidean n × CarrierParameter)) (hE : ∀ i, IsOpen (E i))
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
            (zCell i, (T i).reference.spatialPatch (zCell i))) (L i / 64)))
    (χ : ι → CarrierParameter → ℝ) (hχcompact : ∀ i, HasCompactSupport (χ i))
    (hχE : ∀ i, tsupport (χ i) ⊆ carrierNeighborhood (E i))
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ (r : ℝ) (_hr : 0 < r), 4 * r < 1 / 2 ∧ 12 * r < cap ∧ 12 * r < 1 / 2 ∧
      closedBall (0 : Euclidean n) (12 * r) ⊆ U ∧
    ∃ V : ι → Set CarrierParameter,
      (∀ i, IsOpen (V i)) ∧ (∀ i, tsupport (χ i) ⊆ V i) ∧
      (∀ i, closedBall (0 : Euclidean n) (12 * r) ×ˢ V i ⊆ E i) ∧
      ∀ i,
      let W := ball (0 : Euclidean n) (12 * r) ×ˢ V i
      MapsTo (densityCoordinates (T i)) W
        (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τ i)) ∧
      (∀ p ∈ W, (densityCoordinates (T i) p).2 ∈
        closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64)) ∧
      (∀ p ∈ W, |(densityCoordinates (T i) p).1| < L i / (64 *
        (cNorm (Icc (-τ i) (τ i) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8))
          1 (seed i).forward + 1))) ∧
      ∀ (F' : Euclidean n → Euclidean N)
        (current : Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), zCell i)
          (Rc i) (B i) (τ i) (row i) (col i) F'),
        MapsTo (densityCoordinates (T i)) W current.D := by
  obtain ⟨flowCap, hflowCap, hflow⟩ :=
    NormalizedChartFamily.exists_finite_retained_density_product_buffers T zCell seed
      hL hRc hτ hσcover hcompRadius E hcomp hgraph hworking
  obtain ⟨b, hb, hbcell, hbcap, hbhalf, hbU, V, hV, hχV, hproduct, _hsupport⟩ :=
    exists_fixed_weight_measurement_buffer E hE χ hχcompact hχE hU h0U
      (lt_min hcap hflowCap)
  let r := b / 2
  have hr : 0 < r := half_pos hb
  have hsize : 12 * r = 6 * b := by dsimp [r]; ring
  have hcapr : 12 * r < cap := hsize ▸ hbcap.trans_le (min_le_left _ _)
  have hflowr : 12 * r ≤ flowCap := (hsize ▸ hbcap.trans_le (min_le_right _ _)).le
  have hproductr (i) : closedBall (0 : Euclidean n) (12 * r) ×ˢ V i ⊆ E i :=
    hsize ▸ hproduct i
  refine ⟨r, hr, by dsimp [r]; linarith, hcapr, hsize ▸ hbhalf,
    hsize ▸ hbU, V, hV, hχV, hproductr, ?_⟩
  intro i W
  obtain ⟨hout, hlabel, htime⟩ := hflow (12 * r) hflowr i (V i)
    ((prod_mono ball_subset_closedBall Subset.rfl).trans (hproductr i))
  refine ⟨hout, hlabel, htime, ?_⟩
  intro F' current p hp
  exact current.small_subset ((outputCylinder_spec (hRc i) (hτ i)).2 (hout hp))

end JanetCartan.PositiveBackground
