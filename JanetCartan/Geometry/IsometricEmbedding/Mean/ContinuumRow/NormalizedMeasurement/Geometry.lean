module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.MaskContainment
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Supported

/-!
# Measurement geometry before the normalized source scale

The inputs are the original positive radii of the supplied retained finite
family. Only the physical measurement radius is reduced. The incidence labels,
angular masks, and their full carrier supports retain the original radii.
The normalized selector can therefore use these choices before constructing
any source dilation, without a coercivity or inverse hypothesis.

Consumers: `NormalizedMeasurement.exists_supplied_family_normalized_measurement`,
then `PositiveBackground.exists_small_uncorrectedDensity_of_normal_estimates`
and `ContinuumCommutator.exists_normalized_row_elliptic_estimates`.
Sources: `app:ch_background:eq:bg-uniform-normalized`, `bg-T`, and
paper-v2.tex `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedMeasurement
open CommonMeasurement CanonicalConic
open ContinuumAdjoint.Canonical.PhaseExtension

variable {n : ℕ}

/-- Fix all four cutoffs from the supplied retained radii and chart bounds,
before even the reference to be dilated. The three row cutoffs are literally
`FixedCutoffs.physical` and `FixedCutoffs.periodic`; their full supports lie
in the coefficient plateau and every original local measurement plateau.
This is the geometric choice in `app:ch_background:eq:bg-uniform-normalized`
and paper-v2.tex `new:sec:order-of-choices`. -/
theorem exists_measurement_cutoffs_before_scale {ι : Type*} [Fintype ι]
    (a' : ι → ℝ) (ha' : ∀ i, 0 < a' i)
    {b R : ℝ} (hb : 0 < b) (hR : 0 < R) :
    ∃ (r : ℝ) (hr : 0 < r) (hcell : 4 * r < 1 / 2),
      6 * r < b ∧ 6 * r < R ∧ 6 * r < 1 / 2 ∧ (∀ i, 6 * r < a' i) ∧
      ∃ χcoeff : Euclidean n → ℝ,
        ContDiff ℝ ∞ χcoeff ∧ (∀ x, χcoeff x ∈ Icc (0 : ℝ) 1) ∧
        HasCompactSupport χcoeff ∧ tsupport χcoeff ⊆ ball 0 (5 * r) ∧
        closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1} ∧
        (∀ j : Fin 3, tsupport (FixedCutoffs.physical (n := n) hr j) ⊆
          interior {x | χcoeff x = 1}) ∧
        (∀ (i : ι) (j : Fin 3), tsupport (FixedCutoffs.physical (n := n) hr j) ⊆
          interior {x | FixedCutoffs.physical (ha' i) 1 x = 1}) ∧
        (∀ (hlocal : ∀ i, 4 * a' i < 1 / 2) (i : ι),
          FixedCutoffs.periodic (n := n) hr hcell 1 *
          FixedCutoffs.periodic (ha' i) (hlocal i) 1 =
          FixedCutoffs.periodic hr hcell 1) := by
  let bounds : Option ι → ℝ := fun i ↦
    match i with
    | none => min b (min R (1 / 2))
    | some i => a' i
  have hbounds : ∀ i, 0 < bounds i := by
    intro i
    cases i with
    | none => exact lt_min hb (lt_min hR (by norm_num))
    | some i => exact ha' i
  obtain ⟨ε, hε, hεbounds⟩ := Pi.exists_forall_pos_add_lt hbounds
  have hsmall : ε < min b (min R (1 / 2)) := by
    simpa only [zero_add] using hεbounds none
  have hlocal : ∀ i, ε < a' i := fun i ↦ by
    simpa only [zero_add] using hεbounds (some i)
  let r := ε / 6
  have hr : 0 < r := div_pos hε (by norm_num)
  have hsix : 6 * r = ε := by dsimp only [r]; ring
  have hhalf : 6 * r < 1 / 2 := by
    rw [hsix]
    exact (lt_min_iff.mp (lt_min_iff.mp hsmall).2).2
  have hra : ∀ i, 6 * r < a' i := by simpa only [hsix] using hlocal
  have hcell : 4 * r < 1 / 2 := by linarith
  let χ := bufferedBallBump (0 : Euclidean n) (4 * r) (5 * r)
    (by positivity) (by linarith)
  have hp : closedBall 0 (4 * r) ⊆ interior {x | χ x = 1} :=
    bufferedBallBump_plateau _ _ _ _ _
  refine ⟨r, hr, hcell, ?_, ?_, hhalf, hra, χ, χ.contDiff,
    (fun _ ↦ ⟨χ.nonneg, χ.le_one⟩), χ.hasCompactSupport,
    bufferedBallBump_tsupport_subset _ _ _ _ _, hp,
    (fun j ↦ (FixedCutoffs.physical_tsupport_four hr j).trans hp), ?_, ?_⟩
  · rw [hsix]
    exact (lt_min_iff.mp hsmall).1
  · rw [hsix]
    exact (lt_min_iff.mp (lt_min_iff.mp hsmall).2).1
  · intro i j
    apply (FixedCutoffs.physical_tsupport_four hr j).trans
    apply (closedBall_subset_closedBall ?_).trans (FixedCutoffs.physical_plateau (ha' i) 1)
    norm_num
    linarith [hra i]
  · intro hlocal i
    exact periodic_measurement_mul hr (ha' i) hcell (hlocal i) (by linarith [hra i])

/-- Shrinking only the physical radius preserves the FULL original carrier
support, including its boundary. This is the supported-chart input for every
source/initial buffer retained in `RetainedFrozen.Row`, and for
`app:ch_background:eq:bg-uniform-normalized`. -/
theorem source_product_subset_original_supportedChart
    (z₀ : Euclidean 3) {r a' : ℝ} (hr : 0 < r) (hra : 6 * r < a') :
    closedBall (0 : Euclidean n) (6 * r) ×ˢ carrierSupport z₀ (r := a') ⊆
      supportedChart z₀ a' := by
  exact prod_mono (closedBall_subset_closedBall (by linarith)) (Subset.refl _)

/-- The original retained-cell coefficient inclusion still contains the
whole source ball times the FULL original carrier support. `houter`, `haa`
and `har` come from `RetainedFrozen.Row` (with `har` obtained from
`a' ≤ r' ≤ rCarrier`). Thus its SAME graph, detector and source-domain maps
restrict to this product by `MapsTo.mono_left`; none is reselected
(`bg-T`, `bg-uniform-normalized`, `new:sec:order-of-choices`). -/
theorem source_product_subset_retained_cell
    (z₀ : Euclidean 3) {r a' rCarrier a : ℝ}
    (hr : 0 < r) (hra : 6 * r < a')
    (haa : a' ≤ a) (har : a' ≤ rCarrier)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain z₀ rCarrier (6 * a) ⊆ E) :
    closedBall (0 : Euclidean n) (6 * r) ×ˢ carrierSupport z₀ (r := a') ⊆ E := by
  rintro ⟨x, z⟩ ⟨hx, hs, hv⟩
  apply houter
  exact ⟨closedBall_subset_ball (by linarith) hx,
    closedBall_subset_ball (by linarith) hs, closedBall_subset_ball (by linarith) hv⟩

/-- Every point of the full closed angular support, including its boundary,
uses the original retained detector cell on the common source ball. This is
the actual support inclusion needed to retain the detector and graph maps,
not just an incidence-point assertion (`bg-full-complex-amplitude`,
`bg-uniform-normalized`). -/
theorem full_angular_support_mem_retained_cell
    (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1)) {r a' rCarrier a width : ℝ}
    (hr : 0 < r) (ha' : 0 < a') (hwidth : 0 < width) (hra : 6 * r < a')
    (haa : a' ≤ a) (har : a' ≤ rCarrier)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain z₀ rCarrier (6 * a) ⊆ E)
    {x : Euclidean n} (hx : x ∈ closedBall 0 (6 * r))
    {q : CarrierParameter × Euclidean (n - 1)}
    (hq : q ∈ tsupport (Function.uncurry (angularMask z₀ θ₀ ha' hwidth))) :
    (x, q.1) ∈ E :=
  source_product_subset_retained_cell z₀ hr hra haa har houter
    ⟨hx, (angularMask_tsupport z₀ θ₀ ha' hwidth hq).1⟩

/-- The same original initial plateau works on the entire common source
chart and original carrier support. No initial cutoff, flow or carrier label
is reselected (`bg-T`, `app:ch_background:prop:bg-adjoint`). -/
theorem initial_buffer_on_common_source {α : Type*}
    (z₀ : Euclidean 3) {r a' : ℝ} (hr : 0 < r) (hra : 6 * r < a')
    (f : Euclidean n × CarrierParameter → α) (K : Set α)
    (hbuffer : MapsTo f (supportedChart z₀ a') K) :
    MapsTo f (closedBall 0 (6 * r) ×ˢ carrierSupport z₀ (r := a')) K :=
  hbuffer.mono_left (source_product_subset_original_supportedChart z₀ hr hra)

/-- The full closed angular support, at both common physical positions,
remains inside the original conic chart. The radii of the original angular
mask are not replaced by the smaller measurement radius
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem original_angular_support_mem_symbolInputDomain
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r r' a' : ℝ}
    (hr : 0 < r) (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a')
    (har : a' ≤ r') (hra : 6 * r < a')
    {x y : Euclidean n}
    (hx : x ∈ closedBall 0 (6 * r)) (hy : y ∈ closedBall 0 (6 * r))
    {z : CarrierParameter} {η : Euclidean (n - 1)} (hη : η ≠ 0)
    (hm : (z, NormedSpace.normalize η) ∈ tsupport
      (Function.uncurry (angularMask z₀ (NormedSpace.normalize ηb) ha'
        (angularWidth_spec hηb hr').1))) :
    ((x, y), z, η) ∈ symbolInputDomain z₀ ηb r' (6 * a') := by
  apply angularMask_tsupport_mem_symbolInputDomain hηb hr' ha' har
    (closedBall_subset_closedBall (by linarith) hx)
    (closedBall_subset_closedBall (by linarith) hy) hη hm

variable {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}

/-- The canonical data on the common chart are a literal update of the
supplied data. In particular the incidence/angular mask, high cutoff, initial
scalar, null column and transport functions are the SAME functions
(`bg-T`, `bg-uniform-normalized`, `new:sec:order-of-choices`). -/
theorem commonChartData_canonicalData
    (T : ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r a' : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (ha' : 0 < a') (hlocal : 4 * a' < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    commonChartData
      (CanonicalCarrier.data T Q F row col φ y initial ha' hlocal angular high)
      (closedBall 0 (4 * r)) (FixedCutoffs.periodic hr hcell 1) =
      CanonicalCarrier.data T Q F row col φ y initial hr hcell angular high := rfl

end JanetCartan.ContinuumRow.NormalizedMeasurement
