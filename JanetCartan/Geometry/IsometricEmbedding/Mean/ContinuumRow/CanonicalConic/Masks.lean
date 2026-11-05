module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalPhase
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes

/-!
# Fixed carrier and angular masks

The supported masks of `app:ch_background:defn:bg-row` are chosen from frozen
centers and positive radii. They have a plateau at the selected incidence point
and direction, and compact support with room for enlarging every coordinate.
No current immersion or coefficient estimate enters these choices.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison

variable {n : ℕ} (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1))
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)

/-- Incidence cutoff, with its support strictly inside the radius-`r` chart
(`app:ch_background:defn:bg-row`). -/
def incidenceMask : ContDiffBump (z₀ 0) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Spectator cutoff for the literal two-dimensional Lebesgue integral
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def spectatorMask : ContDiffBump (spectatorCenter z₀) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Smooth ambient angular cutoff, restricted to unit directions by the
carrier formula (`app:ch_background:defn:bg-row`). -/
def directionMask : ContDiffBump θ₀ where
  rIn := a / 4
  rOut := a / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Actual nonnegative carrier/angular weight on the original `(s,v)` labels
(`app:ch_background:defn:bg-row`). -/
def angularMask (z : CarrierParameter) (θ : Euclidean (n - 1)) : ℝ :=
  incidenceMask z₀ hr z.1 * spectatorMask z₀ hr z.2 * directionMask θ₀ ha θ

/-- Joint smoothness before restricting the last variable to the sphere
(`app:ch_background:eq:bg-mixed-input`). -/
theorem angularMask_smooth :
    ContDiff ℝ ∞ (Function.uncurry (angularMask z₀ θ₀ hr ha)) :=
  (((incidenceMask z₀ hr).contDiff.comp contDiff_fst.fst).mul
    ((spectatorMask z₀ hr).contDiff.comp contDiff_fst.snd)).mul
      ((directionMask θ₀ ha).contDiff.comp contDiff_snd)

/-- The actual weights are nonnegative contractions
(`app:ch_background:defn:bg-row`). -/
theorem angularMask_mem_Icc (z : CarrierParameter) (θ : Euclidean (n - 1)) :
    angularMask z₀ θ₀ hr ha z θ ∈ Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg (mul_nonneg (incidenceMask z₀ hr).nonneg
      (spectatorMask z₀ hr).nonneg) (directionMask θ₀ ha).nonneg,
    (mul_le_of_le_one_left (directionMask θ₀ ha).nonneg
      ((mul_le_of_le_one_left (spectatorMask z₀ hr).nonneg
        (incidenceMask z₀ hr).le_one).trans (spectatorMask z₀ hr).le_one)).trans
      (directionMask θ₀ ha).le_one⟩

/-- Every nonzero weight lies in the smaller incidence, spectator and angular
balls (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem angularMask_nonzero {z : CarrierParameter} {θ : Euclidean (n - 1)}
    (h : angularMask z₀ θ₀ hr ha z θ ≠ 0) :
    z.1 ∈ ball (z₀ 0) (r / 2) ∧ z.2 ∈ ball (spectatorCenter z₀) (r / 2) ∧
      θ ∈ ball θ₀ (a / 2) := by
  have h₁ := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1
  have h₂ := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2
  have h₃ := (mul_ne_zero_iff.mp h).2
  exact ⟨(incidenceMask z₀ hr).support_eq ▸ h₁,
    (spectatorMask z₀ hr).support_eq ▸ h₂,
    (directionMask θ₀ ha).support_eq ▸ h₃⟩

/-- The closed support stays a positive distance inside the larger coordinate
chart (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem angularMask_tsupport :
    tsupport (Function.uncurry (angularMask z₀ θ₀ hr ha)) ⊆
      (closedBall (z₀ 0) (r / 2) ×ˢ closedBall (spectatorCenter z₀) (r / 2)) ×ˢ
        closedBall θ₀ (a / 2) := by
  apply closure_minimal _ ((isClosed_closedBall.prod isClosed_closedBall).prod isClosed_closedBall)
  intro p hp
  obtain ⟨h₁, h₂, h₃⟩ := angularMask_nonzero z₀ θ₀ hr ha hp
  exact ⟨⟨ball_subset_closedBall h₁, ball_subset_closedBall h₂⟩, ball_subset_closedBall h₃⟩

/-- Compactness of the full carrier/angular support follows from the actual
bump construction (`app:ch_background:defn:bg-row`). -/
theorem angularMask_compact :
    HasCompactSupport (Function.uncurry (angularMask z₀ θ₀ hr ha)) :=
  (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod
    (isCompact_closedBall _ _)).of_isClosed_subset (isClosed_tsupport _)
      (angularMask_tsupport z₀ θ₀ hr ha)

/-- The original carrier support is compact, independently of the angular
variable (`app:ch_background:defn:bg-row`). -/
def carrierSupport : Set CarrierParameter :=
  closedBall (z₀ 0) (r / 2) ×ˢ closedBall (spectatorCenter z₀) (r / 2)

/-- Compactness for the carrier extension's parameter truncation
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem carrierSupport_compact : IsCompact (carrierSupport z₀ (r := r)) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

/-- The mask vanishes outside the same compact carrier set used by the
Lebesgue initial-space producer (`app:ch_background:defn:bg-row`). -/
theorem angularMask_zero_outside {z : CarrierParameter}
    (hz : z ∉ carrierSupport z₀ (r := r)) (θ : Euclidean (n - 1)) :
    angularMask z₀ θ₀ hr ha z θ = 0 := by
  by_contra h
  obtain ⟨h₁, h₂, _⟩ := angularMask_nonzero z₀ θ₀ hr ha h
  exact hz ⟨ball_subset_closedBall h₁, ball_subset_closedBall h₂⟩

/-- A full neighborhood of the frozen incidence point and selected direction
has weight one, hence positive weight (`app:ch_background:defn:bg-row`). -/
theorem angularMask_one {z : CarrierParameter} {θ : Euclidean (n - 1)}
    (hs : z.1 ∈ closedBall (z₀ 0) (r / 4))
    (hv : z.2 ∈ closedBall (spectatorCenter z₀) (r / 4))
    (hθ : θ ∈ closedBall θ₀ (a / 4)) : angularMask z₀ θ₀ hr ha z θ = 1 := by
  simp only [angularMask, (incidenceMask z₀ hr).one_of_mem_closedBall hs,
    (spectatorMask z₀ hr).one_of_mem_closedBall hv,
    (directionMask θ₀ ha).one_of_mem_closedBall hθ, mul_one]

end JanetCartan.ContinuumRow.CanonicalConic
