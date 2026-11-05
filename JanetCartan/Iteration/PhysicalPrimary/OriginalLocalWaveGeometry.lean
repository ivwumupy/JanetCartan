module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles
public import JanetCartan.Iteration.RevisedUniform.OriginalSmoothing
public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeights
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Rounding
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelExtensions
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-!
# The same local source and final-cutoff charts

The original χ₂ source support, its native smoothing chart, the selected doubled
parameter cell and the actual leading domain are joined without another cutoff.
The finite-band buffer uses the LAST VALID label `J-1`, not `J`.

Consumers: the actual local atom/source construction in `OriginalLocalWaves`,
`app:ch_waves:thm:individual`, and the one final physical cutoff in
`main:eq:primary`. No raw or corrected field is asserted globally Schwartz.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry

/-- The native open χ₂ plateau lies in the support of the SAME bump.
This proves the cutoff-chart inclusion, without changing either radius
(`main:eq:primary`, `main:lem:smoothing`). -/
theorem inner_ball_subset_tsupport {n : ℕ} (χ : ContDiffBump (0 : Euclidean n)) :
    ball (0 : Euclidean n) χ.rIn ⊆ tsupport (χ : Euclidean n → ℝ) := by
  intro x hx
  exact subset_tsupport _ ((χ.one_of_mem_closedBall (ball_subset_closedBall hx)).trans_ne one_ne_zero)

/-- Slice the actual open leading chart using the original product inclusion.
Only this elementary geometric implication is used for source admission. -/
theorem source_slice_mem {n : ℕ}
    {X : Set (Euclidean n)} {V : Set (Euclidean 3 × Euclidean (n-1))}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hproduct : X ×ˢ V ⊆ Ω) {χ : Euclidean n → ℝ}
    (hχ : tsupport χ ⊆ X) {c : Euclidean 3 × Euclidean (n-1)} (hc : c ∈ V) :
    ∀ x ∈ tsupport χ, (x,c) ∈ Ω :=
  fun _ hx ↦ hproduct ⟨hχ hx,hc⟩

/-- Local regularity is restricted to the SAME physical slice; values outside
that slice are not extended or replaced (`app:ch_waves:thm:individual`). -/
theorem contDiffOn_slice {n N : ℕ}
    {X : Set (Euclidean n)} {V : Set (Euclidean 3 × Euclidean (n-1))}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    {f : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin N)}
    (hf : ContDiffOn ℝ ∞ f Ω) (hproduct : X ×ˢ V ⊆ Ω)
    {c : Euclidean 3 × Euclidean (n-1)} (hc : c ∈ V) :
    ContDiffOn ℝ ∞ (fun x ↦ f (x,c)) X :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ hproduct ⟨hx,hc⟩)

/-- The WHOLE original product collar gives a parameter in the selected doubled
cell, even outside the inner angular carrier support. This is the geometric
reason the unscaled positive baseline remains admissible there. -/
theorem outer_carrier_in_closed_cell {n : ℕ} (hn : 5 ≤ n)
    (a : PhysicalInitialization.OriginalPatchIndex hn) (cell : PhysicalSeed.OriginalBoundary.centers hn a)
    (p : ContinuumRow.CarrierParameter)
    (hp : p ∈ ball (cell.1.1 0, FullPhaseCharts.ActualComparison.spectatorCenter cell.1.1)
      (PhysicalSeed.OriginalBoundary.εcarrier hn a cell)) :
    (ContinuumRow.CanonicalCarrier.parameter p,
      (PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch
        (ContinuumRow.CanonicalCarrier.parameter p)) ∈
        closedBall (cell.1.1,(PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch cell.1.1)
          (PhysicalSeed.OriginalBoundary.σcover hn a cell) := by
  have hcell := PhysicalSeed.OriginalBoundary.carrier_cells hn a cell
  have hgraph := hcell.2.2.1 (show ((0 : Euclidean n),p) ∈
      ball (0 : Euclidean n) (PhysicalSeed.OriginalBoundary.εcarrier hn a cell) ×ˢ
        ball (cell.1.1 0, FullPhaseCharts.ActualComparison.spectatorCenter cell.1.1)
          (PhysicalSeed.OriginalBoundary.εcarrier hn a cell) from
    ⟨mem_ball_self hcell.1,hp⟩)
  change ((0 : Euclidean n),(ContinuumRow.CanonicalCarrier.parameter p,
    (PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch
      (ContinuumRow.CanonicalCarrier.parameter p))) ∈
    ball ((0 : Euclidean n),(cell.1.1,
      (PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch cell.1.1))
      (PhysicalSeed.OriginalBoundary.σcover hn a cell) at hgraph
  rw [← ball_prod_same] at hgraph
  exact ball_subset_closedBall hgraph.2

/-- The original small closed parameter cell lies inside the doubled window
used by source admission (`app:ch_response:cor:current-atoms`). -/
theorem outer_carrier_in_parameter_window {n : ℕ} (hn : 5 ≤ n)
    (a : PhysicalInitialization.OriginalPatchIndex hn) (cell : PhysicalSeed.OriginalBoundary.centers hn a)
    (p : ContinuumRow.CarrierParameter)
    (hp : p ∈ ball (cell.1.1 0, FullPhaseCharts.ActualComparison.spectatorCenter cell.1.1)
      (PhysicalSeed.OriginalBoundary.εcarrier hn a cell)) :
    (ContinuumRow.CanonicalCarrier.parameter p,
      (PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch
        (ContinuumRow.CanonicalCarrier.parameter p)) ∈ OriginalSourceMasks.parameterWindow hn a cell :=
  (OriginalSourceMasks.parameterWindow_spec hn a cell).2.2.2.2
    (outer_carrier_in_closed_cell hn a cell p hp)

/-- A nonzero OUTER sample weight puts the SAME node in the support of its
actual χ. No division, new weight, positivity of the inner b, or removal of
labels is used (`main:eq:primary`). -/
theorem outer_weight_support (χ : ContinuumRow.CarrierParameter → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (shifts : SeparatedSampling.Lattice → SeparatedSampling.Point)
    (a : SeparatedSampling.Sample)
    (ha : SeparatedSampling.weight
      (fun z ↦ (χ (ContinuumRow.carrierSamplingEquiv.symm z))^2)
      w h shifts a ≠ 0) :
    ContinuumRow.carrierSamplingEquiv.symm (SeparatedSampling.node h shifts a) ∈
      tsupport χ := by
  apply subset_tsupport
  intro hz
  have hn := (SeparatedSampling.weight_ne_zero_factors ha).1
  apply hn
  simp only [hz,zero_pow (by decide : 2 ≠ 0)]

/-- Apply the proved outer support map to the unchanged sampled node. The input
is the static actual-χ geometry, not a smoothness assumption on a wave. -/
theorem outer_weight_parameter_window {n : ℕ}
    {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily P U hU)
    (χ : ContinuumRow.CarrierParameter → ℝ)
    {V : Set (Euclidean 3 × Euclidean (n-1))}
    (hχ : ∀ p ∈ tsupport χ,
      (ContinuumRow.CanonicalCarrier.parameter p,
        T.reference.spatialPatch (ContinuumRow.CanonicalCarrier.parameter p)) ∈ V)
    (w : ℝ → ℝ) (h : ℝ) (shifts : SeparatedSampling.Lattice → SeparatedSampling.Point)
    (a : SeparatedSampling.Sample)
    (ha : SeparatedSampling.weight
      (fun z ↦ (χ (ContinuumRow.carrierSamplingEquiv.symm z))^2)
      w h shifts a ≠ 0) :
    let p := ContinuumRow.carrierSamplingEquiv.symm (SeparatedSampling.node h shifts a)
    (ContinuumRow.CanonicalCarrier.parameter p,
      T.reference.spatialPatch (ContinuumRow.CanonicalCarrier.parameter p)) ∈ V :=
  hχ _ (outer_weight_support χ w h shifts a ha)

/-- The whole closed Hilbert ceiling has an open one-band buffer. The factor
four from the last valid label to the buffer is retained, so the displacement
is at most ρ/2. These are numerical rate inputs, not a wave regularity premise
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem finite_band_open_buffer {d J : ℕ} {τ ε ρ : ℝ}
    (hJ : 0 < J) (hτ : 0 ≤ τ) (hε : ε ≤ ρ/8)
    (hmargin : ∀ j : Fin J, τ * (2 : ℝ)^j.val ≤ ε) :
    closedBall (0 : Euclidean d) ((2 : ℝ)^J) ⊆
        ball 0 ((2 : ℝ)^(J+1)) ∧
      ∀ η ∈ ball (0 : Euclidean d) ((2 : ℝ)^(J+1)), ‖τ • η‖ ≤ ρ/2 := by
  have hp : (2 : ℝ)^J < (2 : ℝ)^(J+1) := by
    rw [pow_succ]
    have hpos : 0 < (2 : ℝ)^J := by positivity
    linarith
  refine ⟨closedBall_subset_ball hp, ?_⟩
  have hlast := hmargin ⟨J-1, by omega⟩
  have hpow : τ * (2 : ℝ)^(J+1) ≤ 4*ε := by
    rw [show J+1 = (J-1)+1+1 by omega, pow_succ, pow_succ]
    nlinarith only [hlast]
  intro η hη
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
  have hη' : ‖η‖ ≤ (2 : ℝ)^(J+1) :=
    (mem_ball_zero_iff.mp hη).le
  exact (mul_le_mul_of_nonneg_left hη' hτ).trans (hpow.trans (by linarith))

/-- The literal original cutoff count is positive; no frequency label is
renamed or added to the sampler (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem original_finite_band_open_buffer {d : ℕ} {Λ τ ε ρ : ℝ}
    (hΛ : 1 ≤ Λ) (hτ : 0 ≤ τ) (hε : ε ≤ ρ/8)
    (hmargin : ∀ j : Fin (RawInputPartition.cutoffCount Λ), τ * (2 : ℝ)^j.val ≤ ε) :
    closedBall (0 : Euclidean d) ((2 : ℝ)^RawInputPartition.cutoffCount Λ) ⊆
        ball 0 ((2 : ℝ)^(RawInputPartition.cutoffCount Λ+1)) ∧
      ∀ η ∈ ball (0 : Euclidean d) ((2 : ℝ)^(RawInputPartition.cutoffCount Λ+1)),
        ‖τ • η‖ ≤ ρ/2 := by
  obtain ⟨q,hq,_⟩ := RawInputPartition.cutoffCount_spec hΛ
  exact finite_band_open_buffer (by omega) hτ hε hmargin

/-- The *parameter* of every shifted original wide-band mode already lies in
its small σ-cell, before it is included in the larger source product. The
parameter cutoff is identically one as a germ there, not throughout the
entire doubled parameter window (`app:ch_response:eq:response-graded-source`). -/
theorem shifted_parameter_in_cell {d : ℕ}
    {P : FrozenMenu.Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily P U hU)
    {zRoot zCell z : Euclidean 3} {ρ σ : ℝ} (hρ : 0 < ρ)
    (hparent : closedBall ((0 : Euclidean (d+1)),(zRoot,T.reference.spatialPatch zRoot))
      (2*ρ) ⊆ ball ((0 : Euclidean (d+1)),(zCell,T.reference.spatialPatch zCell)) σ)
    (hz : (z,T.reference.spatialPatch z) ∈
      closedBall (zRoot,T.reference.spatialPatch zRoot) (ρ/4))
    {V : Set (Euclidean (d+1-1))} {τ : ℝ} (hshift : ∀ η ∈ V, ‖τ • η‖ ≤ ρ/2) :
    ∀ η ∈ V, (z,T.reference.spatialPatch z+τ • η) ∈
      ball (zCell,T.reference.spatialPatch zCell) σ := by
  intro η hη
  have hplateau := Sampling.MeasuredAmplitude.retained_shift_mem_plateau T
    ((0 : Euclidean (d+1)),(zRoot,T.reference.spatialPatch zRoot)) (ρ := 2*ρ)
    (x := 0) (by simpa only [show (2*ρ)/2 = ρ by ring] using
      (mem_closedBall_self hρ.le : (0 : Euclidean (d+1)) ∈ closedBall 0 ρ))
    (closedBall_subset_closedBall (by linarith : ρ/4 ≤ (2*ρ)/4) hz)
    (by simpa only [show (2*ρ)/4 = ρ/2 by ring] using hshift η hη)
  have hparentPoint := hparent
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2*ρ)
      (by simpa only [show (2*ρ)/2 = ρ by ring] using hplateau))
  rw [← ball_prod_same] at hparentPoint
  exact hparentPoint.2

/-- The original sampling graph and finite-band displacement fit the original
selected cell. Use the retained parameter-cell bound; physical source points
then use their own original σ-cover certificate. There is no new physical or
parameter cutoff (`app:ch_waves:eq:individual-representation`). -/
theorem shifted_source_product {d : ℕ}
    {P : FrozenMenu.Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily P U hU)
    {zRoot zCell z : Euclidean 3} {ρ σ : ℝ} (hρ : 0 < ρ)
    {X : Set (Euclidean (d+1))}
    {Ω : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean (d+1-1)))}
    (hX : X ⊆ ball (0 : Euclidean (d+1)) σ)
    (hparent : closedBall ((0 : Euclidean (d+1)),(zRoot,T.reference.spatialPatch zRoot))
      (2*ρ) ⊆ ball ((0 : Euclidean (d+1)),(zCell,T.reference.spatialPatch zCell)) σ)
    (hcell : closedBall ((0 : Euclidean (d+1)),(zCell,T.reference.spatialPatch zCell)) (2*σ) ⊆ Ω)
    (hz : (z,T.reference.spatialPatch z) ∈
      closedBall (zRoot,T.reference.spatialPatch zRoot) (ρ/4))
    {V : Set (Euclidean (d+1-1))} {τ : ℝ}
    (hshift : ∀ η ∈ V, ‖τ • η‖ ≤ ρ/2) :
    ∀ p ∈ X ×ˢ V, (p.1,(z,T.reference.spatialPatch z+τ • p.2)) ∈ Ω := by
  intro p hp
  have hz' := shifted_parameter_in_cell T hρ hparent hz hshift p.2 hp.2
  have hσ : 0 < σ := lt_of_le_of_lt dist_nonneg (mem_ball.mp hz')
  apply hcell
  apply closedBall_subset_closedBall (by linarith : σ ≤ 2*σ)
  apply ball_subset_closedBall
  rw [← ball_prod_same]
  exact ⟨hX hp.1,hz'⟩

end JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry

abbreviate_original_local_inputs_through 40

retain_original_local_cutoff_geometry
retain_original_local_current_geometry 0
retain_original_local_current_geometry 1
retain_original_local_current_geometry 2
retain_original_local_current_geometry 3
retain_original_local_current_geometry 4
retain_original_local_current_geometry 5
retain_original_local_current_geometry 6
retain_original_local_outer_geometry
