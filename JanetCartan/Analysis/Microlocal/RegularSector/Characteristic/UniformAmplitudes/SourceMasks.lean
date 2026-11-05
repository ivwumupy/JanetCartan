module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Fixed source and time masks on the common characteristic box

Construct the actual source mask before the coefficient field. Its support
is compact in the common source ball, its inner plateau contains a full
closed ball, and its source time stays strictly above one fixed lower endpoint.
The output-time mask has a plateau on that same inner interval. These are the
literal masks consumed by `ResidualCoordinates.buffered_pencil_matrices_regular`
and the lower-time vanishing input of `EvolutionIntegral`.

Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
variable {d : ℕ}

/-- A common chart source radius constructs both masks and their lower-time
buffer. All choices precede the varying coefficients, flow and chart.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_common_characteristic_source_masks
    (z : RootState (Euclidean d)) {a : ℝ} (ha : 0 < a) :
    ∃ (mask : RootState (Euclidean d) → ℝ) (κ : ℝ → ℝ),
      ContDiff ℝ ∞ mask ∧ ContDiff ℝ ∞ κ ∧
      (∀ w, mask w ∈ Icc (0 : ℝ) 1) ∧ (∀ t, κ t ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport mask ∧ HasCompactSupport κ ∧
      tsupport mask ⊆ ball z (a / 2) ∧ tsupport κ ⊆ ball z.1 (a / 2) ∧
      closedBall z (a / 4) ⊆ interior {w | mask w = 1} ∧
      closedBall z.1 (a / 4) ⊆ interior {t | κ t = 1} ∧
      tsupport mask ⊆ {w | z.1 - a < w.1} ∧
      tsupport κ ×ˢ tsupport mask ⊆ ball (z.1, z) a ∧
      ∀ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
          (TwoTimePoint (Euclidean d)),
        C.source = ball (z.1, z) a →
        ball z.1 (a / 2) ×ˢ (ball z.1 (a / 2) ×ˢ ball z.2 (a / 2)) ⊆ C.source ∧
        tsupport mask ⊆ ball z.1 (a / 2) ×ˢ ball z.2 (a / 2) := by
  obtain ⟨mask, hm, hmr, hmc, hms, hmp⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_closedBall z (a / 4)) isOpen_ball
    (closedBall_subset_ball (by linarith : a / 4 < a / 2))
  obtain ⟨κ, hk, hkr, hkc, hks, hkp⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_closedBall z.1 (a / 4)) isOpen_ball
    (closedBall_subset_ball (by linarith : a / 4 < a / 2))
  refine ⟨mask, κ, hm, hk, hmr, hkr, hmc, hkc, hms, hks, hmp, hkp, ?_, ?_, ?_⟩
  · intro w hw
    have h := hms hw
    have ht : dist w.1 z.1 < a / 2 := (le_max_left _ _).trans_lt h
    have hl := (abs_lt.mp (show |w.1 - z.1| < a / 2 from ht)).1
    change z.1 - a < w.1
    linarith
  · intro q hq
    have ht := hks hq.1
    have hw := hms hq.2
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (ht.trans (by linarith)) (hw.trans (by linarith))
  · intro C hC
    rw [hC]
    constructor
    · intro q hq
      have hw : q.2 ∈ ball z (a / 2) := by
        simpa only [mem_ball, Prod.dist_eq, max_lt_iff, mem_prod] using hq.2
      rw [mem_ball, Prod.dist_eq]
      exact max_lt (hq.1.trans (by linarith)) (hw.trans (by linarith))
    · intro w hw
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff, mem_prod] using hms hw

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
