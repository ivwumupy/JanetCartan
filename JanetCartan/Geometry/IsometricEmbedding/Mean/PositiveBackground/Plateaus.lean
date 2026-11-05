module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks

/-!
# Fixed source, measurement, and external carrier plateaus

The cutoffs in `app:ch_background:prop:bg-positive` are fixed before synthesis.
The external carrier weight is the square of a smooth nonnegative cutoff that
equals one on the closed carrier support of the EXISTING angular mask. Its
support stays strictly inside the original carrier chart. The initial spatial
variables are unrestricted.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.PositiveBackground
open ContinuumRow ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison

variable {n N : ℕ} {r : ℝ}

/-- Buffered incidence factor of the external carrier cutoff
(`app:ch_background:prop:bg-positive`). -/
def externalIncidenceCutoff (z₀ : Euclidean 3) (hr : 0 < r) : ContDiffBump (z₀ 0) where
  rIn := 2 * r / 3
  rOut := 5 * r / 6
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Buffered spectator factor on the original Lebesgue labels
(`app:ch_background:prop:bg-positive`). -/
def externalSpectatorCutoff (z₀ : Euclidean 3) (hr : 0 < r) :
    ContDiffBump (spectatorCenter z₀) where
  rIn := 2 * r / 3
  rOut := 5 * r / 6
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The external carrier cutoff for the original angular mask, on the literal
`(s,v)` labels (`app:ch_background:prop:bg-positive`). -/
def externalCarrierCutoff (z₀ : Euclidean 3) (hr : 0 < r) (z : CarrierParameter) : ℝ :=
  externalIncidenceCutoff z₀ hr z.1 * externalSpectatorCutoff z₀ hr z.2

/-- The external weight is smooth jointly in the original carrier variables
(`app:ch_background:eq:bg-affine-mean`). -/
theorem externalCarrierCutoff_contDiff (z₀ : Euclidean 3) (hr : 0 < r) :
    ContDiff ℝ ∞ (externalCarrierCutoff z₀ hr) :=
  ((externalIncidenceCutoff z₀ hr).contDiff.comp contDiff_fst).mul
    ((externalSpectatorCutoff z₀ hr).contDiff.comp contDiff_snd)

/-- Nonnegative contractive external cutoff (`app:ch_background:prop:bg-positive`). -/
theorem externalCarrierCutoff_mem_Icc (z₀ : Euclidean 3) (hr : 0 < r)
    (z : CarrierParameter) : externalCarrierCutoff z₀ hr z ∈ Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg (externalIncidenceCutoff z₀ hr).nonneg
      (externalSpectatorCutoff z₀ hr).nonneg,
    (mul_le_of_le_one_left (externalSpectatorCutoff z₀ hr).nonneg
      (externalIncidenceCutoff z₀ hr).le_one).trans (externalSpectatorCutoff z₀ hr).le_one⟩

private theorem externalCarrierCutoff_tsupport_small (z₀ : Euclidean 3) (hr : 0 < r) :
    tsupport (externalCarrierCutoff z₀ hr) ⊆
      closedBall (z₀ 0) (5 * r / 6) ×ˢ closedBall (spectatorCenter z₀) (5 * r / 6) := by
  apply closure_minimal _ (isClosed_closedBall.prod isClosed_closedBall)
  intro z hz
  have hz' := mul_ne_zero_iff.mp hz
  exact ⟨ball_subset_closedBall ((externalIncidenceCutoff z₀ hr).support_eq ▸ hz'.1),
    ball_subset_closedBall ((externalSpectatorCutoff z₀ hr).support_eq ▸ hz'.2)⟩

/-- The external cutoff has compact support strictly inside the same radius-`r`
carrier chart (`app:ch_background:prop:bg-positive`). -/
theorem externalCarrierCutoff_support (z₀ : Euclidean 3) (hr : 0 < r) :
    HasCompactSupport (externalCarrierCutoff z₀ hr) ∧
      tsupport (externalCarrierCutoff z₀ hr) ⊆
        ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) r := by
  have hs := externalCarrierCutoff_tsupport_small z₀ hr
  exact ⟨((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).of_isClosed_subset
    (isClosed_tsupport _) hs,
    hs.trans (prod_mono (closedBall_subset_ball (by linarith))
      (closedBall_subset_ball (by linarith)))⟩

/-- The SAME original closed carrier support lies in the external plateau
(`app:ch_background:eq:bg-density-twice`). -/
theorem externalCarrierCutoff_one (z₀ : Euclidean 3) (hr : 0 < r)
    {z : CarrierParameter} (hz : z ∈ carrierSupport z₀ (r := r)) :
    externalCarrierCutoff z₀ hr z = 1 := by
  have hs : z.1 ∈ closedBall (z₀ 0) (2 * r / 3) :=
    closedBall_subset_closedBall (by linarith) hz.1
  have hv : z.2 ∈ closedBall (spectatorCenter z₀) (2 * r / 3) :=
    closedBall_subset_closedBall (by linarith) hz.2
  simp only [externalCarrierCutoff, (externalIncidenceCutoff z₀ hr).one_of_mem_closedBall hs,
    (externalSpectatorCutoff z₀ hr).one_of_mem_closedBall hv, mul_one]

/-- The constructed external cutoff discharges the angular plateau premise of
the uncut synthesis theorem (`app:ch_background:eq:bg-density-twice`). -/
theorem externalCarrierCutoff_one_of_angularMask
    (z₀ : Euclidean 3) (η₀ : Euclidean (n - 1)) (hr : 0 < r)
    {a : ℝ} (ha : 0 < a) {z : CarrierParameter} {η : Euclidean (n - 1)}
    (h : angularMask z₀ η₀ hr ha z η ≠ 0) : externalCarrierCutoff z₀ hr z = 1 := by
  obtain ⟨hs, hv, _⟩ := angularMask_nonzero z₀ η₀ hr ha h
  exact externalCarrierCutoff_one z₀ hr ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩

/-- Exact external-weight removal for the actual canonical angular mask and
literal factor-four density, at every initial position
(`app:ch_background:eq:bg-density-four`, `app:ch_background:eq:bg-density-twice`). -/
theorem externalCarrierCutoff_sq_mul_initialDensity
    (d : CarrierData n N) (z₀ : Euclidean 3) (η₀ : Euclidean (n - 1)) (hr : 0 < r)
    {a : ℝ} (ha : 0 < a) (hd : d.angularCutoff = angularMask z₀ η₀ hr ha)
    (f : CarrierVariable n → ℂ) (p : CarrierVariable n) :
    externalCarrierCutoff z₀ hr p.1 ^ 2 * UncutDensity.initialDensity d 4 f p =
      UncutDensity.initialDensity d 4 f p := by
  apply UncutDensity.externalWeight_mul_initialDensity
  intro z η h
  rw [hd] at h
  exact externalCarrierCutoff_one_of_angularMask z₀ η₀ hr ha h

/-- The compact source cutoff is inside the fixed measurement plateau, before
periodization or synthesis (`app:ch_background:eq:bg-current-raising`). -/
theorem measurement_mul_cutReducedSource (hr : 0 < r)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n) (x : Euclidean n) :
    FixedCutoffs.physical hr 1 x • cutReducedSource (FixedCutoffs.physical hr 0) Q R x =
      cutReducedSource (FixedCutoffs.physical hr 0) Q R x := by
  by_cases hx : FixedCutoffs.physical hr 0 x = 0
  · simp [cutReducedSource, hx]
  · have hs := FixedCutoffs.physical_tsupport hr 0 (subset_tsupport _ hx)
    have hx' : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * r) := by
      convert ball_subset_closedBall hs using 1
      norm_num
    have hp : x ∈ {x : Euclidean n | FixedCutoffs.physical hr 1 x = 1} :=
      interior_subset (FixedCutoffs.physical_plateau hr 1 hx')
    rw [show FixedCutoffs.physical hr 1 x = 1 from hp, one_smul]

end JanetCartan.PositiveBackground
