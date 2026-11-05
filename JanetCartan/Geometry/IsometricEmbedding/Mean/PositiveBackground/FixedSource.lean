module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Plateaus
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SourceSobolev

/-!
# The source with the original fixed physical cutoffs

The source cutoff θ is the smallest fixed cutoff, the measurement cutoff is
the next one, and the image-input cutoff χ_src is the largest one. In
`app:ch_background:eq:bg-current-raising` the source and its buffered residual
use these already fixed choices. The buffer represents the residual in L²;
it disappears identically after multiplication by θ. The density synthesis
is unaffected and remains uncut in the initial spatial variables.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow UniformStep.Periodization

variable {n : ℕ} {r : ℝ}

/-- Each fixed physical cutoff gives a smooth periodic reduced source on the
SAME torus. Smoothness of the geometric fields is needed only on their common
physical chart (`app:ch_background:eq:bg-current-raising`). -/
theorem fixedCutReducedSource_periodic (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    {Q : Euclidean n → Fin n → MetricTensor n} {R : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) (i : Fin 3) :
    IsSmoothPeriodic (vectorPeriodization (cutReducedSource (FixedCutoffs.physical hr i) Q R)) := by
  have hsupport : tsupport (FixedCutoffs.physical (n := n) hr i) ⊆ ball 0 (4 * r) := by
    apply (FixedCutoffs.physical_tsupport hr i).trans (ball_subset_ball _)
    have hi : (i : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
    nlinarith
  exact (cutReducedSource_periodic hcell isOpen_ball (FixedCutoffs.physical hr i).contDiff
    hsupport (ImageGeometry.imageCutoff_support_box (FixedCutoffs.physical_tsupport_four hr i))
    hQ hR).1

/-- The concrete measured source class for the original uncorrected inverse
(`app:ch_background:eq:bg-current-raising`). -/
def fixedSourceToL2 (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) : OutputL2 n :=
  sourceToL2 (cutReducedSource (FixedCutoffs.physical hr 0) Q R)
    (fixedCutReducedSource_periodic hr hcell hQ hR 0)

/-- The residual is represented using the existing measurement cutoff. The
factor `-2` removes the source's `-1/2`; multiplication by θ then recovers the
original source exactly (`app:ch_background:eq:bg-current-raising`). -/
def fixedResidualToL2 (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) : OutputL2 n :=
  (-2 : ℝ) • sourceToL2 (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
    (fixedCutReducedSource_periodic hr hcell hQ hR 1)

/-- Equality on the original physical chart identifies every fixed cut source;
values of the residual outside that chart do not enter the periodization
(`app:ch_background:eq:bg-current-raising`). -/
private theorem fixedCutReducedSource_eq_of_residual_eqOn (hr : 0 < r)
    (Q : Euclidean n → Fin n → MetricTensor n) {R S : MetricField n}
    (heq : EqOn R S (ball 0 (4 * r))) (i : Fin 3) :
    cutReducedSource (FixedCutoffs.physical hr i) Q R =
      cutReducedSource (FixedCutoffs.physical hr i) Q S := by
  funext x
  by_cases hx : FixedCutoffs.physical hr i x = 0
  · simp only [cutReducedSource, hx, mul_zero, zero_smul]
  · have hs := FixedCutoffs.physical_tsupport hr i
      (subset_tsupport (FixedCutoffs.physical hr i) hx)
    have hi : (i : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
    have hxball : x ∈ ball (0 : Euclidean n) (4 * r) :=
      ball_subset_ball (by nlinarith) hs
    simp only [cutReducedSource, heq hxball]

/-- Matching the physical and normalized residuals on the SAME source chart
identifies their literal L² inputs to the uncorrected inverse, retaining its
cutoff and factor `-1/2` (`app:ch_background:eq:bg-current-raising`). -/
theorem fixedSourceToL2_eq_of_residual_eqOn (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) {R S : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r)))
    (hS : ContDiffOn ℝ ∞ S (ball 0 (4 * r)))
    (heq : EqOn R S (ball 0 (4 * r))) :
    fixedSourceToL2 hr hcell Q R hQ hR = fixedSourceToL2 hr hcell Q S hQ hS := by
  unfold fixedSourceToL2
  congr 1
  exact fixedCutReducedSource_eq_of_residual_eqOn hr Q heq 0

/-- Matching residuals on the original chart also identifies the SAME buffered
residual passed to `uncorrectedDensity`. The measurement cutoff and factor `-2`
are unchanged (`app:ch_background:eq:bg-current-raising`). -/
theorem fixedResidualToL2_eq_of_residual_eqOn (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) {R S : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r)))
    (hS : ContDiffOn ℝ ∞ S (ball 0 (4 * r)))
    (heq : EqOn R S (ball 0 (4 * r))) :
    fixedResidualToL2 hr hcell Q R hQ hR = fixedResidualToL2 hr hcell Q S hQ hS := by
  unfold fixedResidualToL2
  apply congrArg ((-2 : ℝ) • ·)
  congr 1
  exact fixedCutReducedSource_eq_of_residual_eqOn hr Q heq 1

/-- The constructed residual has the actual reduced geometric value wherever
the original source is nonzero (`app:ch_background:eq:bg-current-raising`). -/
theorem fixedResidualToL2_coeFn (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) :
    fixedResidualToL2 hr hcell Q R hQ hR =ᵐ[volume]
      fun z ↦ FixedCutoffs.periodic hr hcell 1 z •
        WithLp.toLp 2 (CubeKernel.tensorContraction
          (Q (AmplitudeBound.centeredTorusRepresentative z))
          (R (AmplitudeBound.centeredTorusRepresentative z))) := by
  filter_upwards [Lp.coeFn_smul (-2 : ℝ)
      (sourceToL2 (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
        (fixedCutReducedSource_periodic hr hcell hQ hR 1)),
    sourceToL2_coeFn (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
      (fixedCutReducedSource_periodic hr hcell hQ hR 1)] with z hsm hs
  change _ = _ at hsm
  change ((-2 : ℝ) • sourceToL2 _ _) z = _
  rw [hsm, Pi.smul_apply, hs]
  simp only [vectorPeriodization, Function.comp_apply, cutReducedSource,
    FixedCutoffs.periodic_apply, smul_smul]
  congr 1
  ring

/-- No residual realization or plateau premise remains in the source identity:
the existing nested cutoffs and local geometric smoothness discharge both
(`app:ch_background:eq:bg-current-raising`). -/
theorem inverseSource_fixedResidualToL2 (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) :
    inverseSource (FixedCutoffs.periodic hr hcell 0)
      (fixedResidualToL2 hr hcell Q R hQ hR) = fixedSourceToL2 hr hcell Q R hQ hR := by
  apply inverseSource_bufferedResidual
  intro x hx
  have hs := FixedCutoffs.physical_tsupport hr 0 (subset_tsupport _ hx)
  have hball : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * r) := by
    convert ball_subset_closedBall hs using 1
    norm_num
  have hp : x ∈ {x : Euclidean n | FixedCutoffs.physical hr 1 x = 1} :=
    interior_subset (FixedCutoffs.physical_plateau hr 1 hball)
  exact hp

/-- The actual measurement operator fixes the compact source. This is the
support condition consumed by the uncut carrier identity
(`app:ch_background:eq:bg-density-twice`). -/
theorem measurement_fixedSourceToL2 (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) :
    cutoffMultiplier (FixedCutoffs.periodic hr hcell 1)
      (fixedSourceToL2 hr hcell Q R hQ hR) = fixedSourceToL2 hr hcell Q R hQ hR := by
  apply cutoffMultiplier_sourceToL2
  intro z hz
  have hs := FixedCutoffs.physical_tsupport hr 0 (subset_tsupport _ hz)
  have hball : AmplitudeBound.centeredTorusRepresentative z ∈
      closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * r) := by
    convert ball_subset_closedBall hs using 1
    norm_num
  have hp : AmplitudeBound.centeredTorusRepresentative z ∈
      {x : Euclidean n | FixedCutoffs.physical hr 1 x = 1} :=
    interior_subset (FixedCutoffs.physical_plateau hr 1 hball)
  exact hp

/-- Every Sobolev level contains the SAME constructed source, ready for the
one uncorrected continuum inverse (`app:ch_background:prop:bg-inverse`). -/
theorem fixedSourceToL2_mem (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) (s : ℕ) :
    fixedSourceToL2 hr hcell Q R hQ hR ∈ periodicSobolevLevel n (Euclidean n) s :=
  sourceToL2_mem _ _ s

/-- The literal smooth buffered residual used by the original inverse;
the buffer is the fixed measurement cutoff, not a new source choice
(`app:ch_background:eq:bg-current-raising`). -/
def fixedResidualRepresentative (hr : 0 < r)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n) :
    Torus n → Euclidean n :=
  (-2 : ℝ) • vectorPeriodization (cutReducedSource (FixedCutoffs.physical hr 1) Q R)

/-- Smoothness of the actual residual representative
(`app:ch_background:prop:bg-positive`). -/
theorem isSmoothPeriodic_fixedResidualRepresentative (hr : 0 < r)
    (hcell : 4 * r < 1 / 2)
    {Q : Euclidean n → Fin n → MetricTensor n} {R : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) :
    IsSmoothPeriodic (fixedResidualRepresentative hr Q R) := by
  have h := fixedCutReducedSource_periodic hr hcell hQ hR 1
  exact ⟨h.1.const_smul (-2 : ℝ), h.2.const_smul (-2 : ℝ)⟩

/-- The smooth representative is the same original residual L² class
(`app:ch_background:eq:bg-current-raising`). -/
theorem fixedResidualRepresentative_ae (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) :
    fixedResidualToL2 hr hcell Q R hQ hR =ᵐ[volume] fixedResidualRepresentative hr Q R := by
  filter_upwards [Lp.coeFn_smul (-2 : ℝ)
      (sourceToL2 (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
        (fixedCutReducedSource_periodic hr hcell hQ hR 1)),
    sourceToL2_coeFn (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
      (fixedCutReducedSource_periodic hr hcell hQ hR 1)] with x hx he
  exact hx.trans (by rw [Pi.smul_apply, he]; rfl)

/-- On the actual physical core the buffer disappears and this representative
is exactly the Frobenius reduction of the same residual tensor
(`app:ch_background:eq:bg-current-identity`). -/
theorem fixedResidualRepresentative_on_core (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    {x : Euclidean n} (hx : x ∈ closedBall 0 r) :
    fixedResidualRepresentative hr Q R (torusQuotient x) =
      WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x)) := by
  have hx4 : x ∈ closedBall (0 : Euclidean n) (4 * r) :=
    closedBall_subset_closedBall (by linarith) hx
  have hrep := PeriodicLocalL2.centeredTorusRepresentative_quotient
    (FixedCutoffs.closedBall_four_subset_cell hcell hx4)
  have hx2 : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * r) := by
    apply closedBall_subset_closedBall _ hx
    norm_num
    linarith
  have hm : x ∈ {y | FixedCutoffs.physical hr 1 y = 1} :=
    interior_subset (FixedCutoffs.physical_plateau hr 1 hx2)
  change FixedCutoffs.physical hr 1 x = 1 at hm
  simp only [fixedResidualRepresentative, Pi.smul_apply, vectorPeriodization,
    Function.comp_apply, hrep, cutReducedSource, hm, mul_one, smul_smul]
  norm_num

/-- Every point of the closed physical core lies in the OPEN torus source
plateau. This is the precise neighborhood needed to promote almost-everywhere
cancellation to pointwise cancellation, including boundary points of the core
(`app:ch_background:eq:bg-current-identity`). -/
theorem torusQuotient_mem_fixedSourcePlateau (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    {x : Euclidean n} (hx : x ∈ closedBall 0 r) :
    torusQuotient x ∈ interior {z | FixedCutoffs.periodic hr hcell 0 z = 1} := by
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  apply mem_interior_iff_mem_nhds.mpr
  apply hq.isOpenMap.nhds_le x
  change ∀ᶠ y in nhds x, FixedCutoffs.periodic hr hcell 0 (torusQuotient y) = 1
  have hx4 : x ∈ closedBall (0 : Euclidean n) (4 * r) :=
    closedBall_subset_closedBall (by linarith) hx
  have hx0 : x ∈ closedBall (0 : Euclidean n) (((0 : Fin 3) + 1 : ℝ) * r) := by
    simpa using hx
  filter_upwards [FixedCutoffs.periodic_eventuallyEq hr hcell 0 hx4,
    isOpen_interior.mem_nhds (FixedCutoffs.physical_plateau hr 0 hx0)] with y he hp
  have hy : y ∈ {z | FixedCutoffs.physical hr 0 z = 1} := interior_subset hp
  exact he.trans hy

end JanetCartan.PositiveBackground
