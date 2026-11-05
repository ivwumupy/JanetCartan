module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhase

/-!
# Integration buffers for the constructed Hamilton phases

The fixed doubled carrier patch is strictly inside the quantitative full-phase
target. Compactness gives a positive shift interval before the current frame is
chosen. The interval and the physical segment buffers extend past both ends of
the unit integration interval, as required in `app:ch_seed:eq:seed-quotient-integral`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualPhase
open ActualCarriers ActualCarriers.CurrentFullPhase ActualCarriers.FrozenPhaseReference FrozenMenu

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The middle cube contains the original closed patch and lies strictly
inside its doubled smoothness domain (`app:ch_seed:prop:seed-phase-charts`). -/
theorem middle_parameter_buffers {c C : ℝ} (hP : P.IsValid c C) :
    parameterCube P.radius ⊆ parameterInterior (3 * P.radius / 2) ∧
      parameterCube (3 * P.radius / 2) ⊆ parameterInterior (2 * P.radius) := by
  constructor <;> intro z hz i
  · exact (hz i).trans_lt (by linarith [hP.1])
  · exact (hz i).trans_lt (by linarith [hP.1])

/-- Construct a positive, two-sided shift buffer for the actual spatial
carrier. Only the fixed frame family and a direction-radius bound enter;
no current phase or assumed segment containment is an input
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem exists_covector_shift_buffer {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M) :
    ∃ εStar > (0 : ℝ), ∀ z ∈ parameterCube (3 * P.radius / 2),
      ∀ η : Euclidean (n - 1), ‖η‖ ≤ M →
      ∀ ε, |ε| ≤ εStar → ∀ s ∈ Ioo (-1 : ℝ) 2,
        T.reference.spatialPatch z + (s * ε) • η ∈
          ball (covectorCenter T) T.family.radius := by
  have hsub := (middle_parameter_buffers hP).2
  have hc : ContinuousOn (fun z ↦ dist (T.reference.spatialPatch z) (covectorCenter T))
      (parameterCube (3 * P.radius / 2)) := by
    change ContinuousOn (fun z ↦ ‖T.reference.spatialPatch z - covectorCenter T‖) _
    exact (((T.reference.spatialPatch_smooth hP).continuousOn.mono hsub).sub
      continuousOn_const).norm
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_parameterCube (3 * P.radius / 2)).exists_isMaxOn
    ⟨0, zero_mem_parameterCube (by linarith [hP.1])⟩ hc
  let d := dist (T.reference.spatialPatch z₀) (covectorCenter T)
  have hd : d < T.family.radius := by
    have hb := T.patch_buffer z₀ (fun i ↦ (hsub hz₀ i).le)
    have hh := (mem_ball.mp hb).trans_le (min_le_left _ _)
    simpa only [PatchQuantitativeFamily.reference, CarrierPhaseReference.spatialPatch,
      AdaptedSection.baseData, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      covectorCenter, d] using hh
  let εStar := (T.family.radius - d) / (4 * M)
  have he : 0 < εStar := div_pos (sub_pos.mpr hd) (by positivity)
  have hem : 2 * εStar * M = (T.family.radius - d) / 2 := by
    dsimp [εStar]
    field_simp [hM.ne']
    norm_num
  refine ⟨εStar, he, fun z hz η hη ε hε s hs ↦ ?_⟩
  have hs' : |s| ≤ 2 := (abs_le).mpr ⟨by linarith [hs.1], hs.2.le⟩
  have hnorm : ‖(s * ε) • η‖ ≤ 2 * εStar * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul hs' hε (abs_nonneg _) (by norm_num)) hη
      (norm_nonneg _) (by positivity)
  have hz' : dist (T.reference.spatialPatch z) (covectorCenter T) ≤ d := hmax hz
  rw [mem_ball]
  calc
    dist (T.reference.spatialPatch z + (s * ε) • η) (covectorCenter T)
        ≤ dist (T.reference.spatialPatch z) (covectorCenter T) + ‖(s * ε) • η‖ := by
          simpa only [dist_eq_norm, add_sub_right_comm] using
            norm_add_le (T.reference.spatialPatch z - covectorCenter T) ((s * ε) • η)
    _ ≤ d + (T.family.radius - d) / 2 := by rw [← hem]; exact add_le_add hz' hnorm
    _ < T.family.radius := by linarith

/-- Physical segments also have an open unit-interval buffer, including for
points in the closed outer physical box
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem physical_segment_mem_phase_ball
    {x y : WithLp 2 (ℝ × Euclidean (n - 1))}
    (hx : x ∈ closedBall 0 (T.family.radius / 8))
    (hy : y ∈ closedBall 0 (T.family.radius / 8))
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 2) :
    y + s • (x - y) ∈ ball 0 T.family.radius := by
  have hx' : ‖x‖ ≤ T.family.radius / 8 := by simpa using hx
  have hy' : ‖y‖ ≤ T.family.radius / 8 := by simpa using hy
  have hs' : |s| ≤ 2 := (abs_le).mpr ⟨by linarith [hs.1], hs.2.le⟩
  rw [mem_ball, dist_zero_right]
  calc
    ‖y + s • (x - y)‖ ≤ ‖y‖ + |s| * ‖x - y‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le y (s • (x - y))
    _ ≤ T.family.radius / 8 + 2 * (T.family.radius / 8 + T.family.radius / 8) :=
      add_le_add hy' (mul_le_mul hs' ((norm_sub_le x y).trans (add_le_add hx' hy'))
        (norm_nonneg _) (by norm_num))
    _ < T.family.radius := by linarith [T.family.radius_pos]

end JanetCartan.FullPhaseCharts.ActualPhase
