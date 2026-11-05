module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Regularity of the radial extension of a compactly supported phase

Compact support supplies the bound needed for continuity at the entire
hyperplane where the normalizing linear coordinate vanishes. Away from the
zero spatial covector, the extension vanishes locally on that hyperplane:
the normalized frequency leaves every compact set. Smoothness at the zero
covector is neither needed nor asserted.

Consumer: the globally continuous auxiliary phase for the full graph in
`app:ch_regular_base:eq:fixed-time-representation`, retaining the phase germs
in `app:ch_regular_base:lem:retarded-kernel` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.ConicPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A compactly supported continuous local phase has a globally continuous
radial extension, including at zero frequency. This supplies the global
continuity input of the graph in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_extend_of_hasCompactSupport (ℓ : E →L[ℝ] ℝ)
    {F : TwoTimePoint E → ℝ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Continuous (extend ℓ F) := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hF
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : ℓ q.2.2.2 = 0
  · change Tendsto (extend ℓ F) (𝓝 q) (𝓝 (extend ℓ F q))
    rw [show extend ℓ F q = 0 by simp [extend, hq]]
    apply squeeze_zero_norm (a := fun p : TwoTimePoint E ↦ ‖ℓ p.2.2.2‖ * M)
    · intro p
      simpa only [extend, norm_mul] using
        mul_le_mul_of_nonneg_left (hM (normalize ℓ p)) (norm_nonneg (ℓ p.2.2.2))
    · have hl := ((ℓ.continuous.comp continuous_snd.snd.snd).norm.mul_const M).tendsto q
      simpa only [Function.comp_apply, hq, norm_zero, zero_mul] using hl
  · exact (ℓ.continuous.continuousAt.comp continuous_snd.snd.snd.continuousAt).mul
      (hF.continuousAt.comp (contDiffAt_normalize ℓ hq).continuousAt)

/-- At a nonzero spatial covector where the linear coordinate vanishes,
the compactly supported radial extension vanishes on a full joint
neighborhood. Consumer: smoothness off zero for the auxiliary phase in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem extend_eventuallyEq_zero_of_linearCoordinate_eq_zero (ℓ : E →L[ℝ] ℝ)
    {F : TwoTimePoint E → ℝ} (hc : HasCompactSupport F) {q : TwoTimePoint E}
    (hq : ℓ q.2.2.2 = 0) (hη : q.2.2.2 ≠ 0) :
    extend ℓ F =ᶠ[𝓝 q] (fun _ ↦ 0) := by
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  have he : ∀ᶠ p : TwoTimePoint E in 𝓝 q,
      ‖ℓ p.2.2.2‖ * R < ‖p.2.2.2‖ :=
    ((ℓ.continuous.comp continuous_snd.snd.snd).norm.mul_const R).continuousAt.eventually_lt
      continuous_snd.snd.snd.norm.continuousAt (by simpa [hq] using norm_pos_iff.mpr hη)
  filter_upwards [he] with p hp
  by_cases hl : ℓ p.2.2.2 = 0
  · simp [extend, hl]
  · have hf : F (normalize ℓ p) = 0 := by
      by_contra hn
      have hb := hR (normalize ℓ p) (subset_tsupport F hn)
      have hfreq : ‖(normalize ℓ p).2.2.2‖ ≤ R :=
        (norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans hb))
      have hnrm : ‖p.2.2.2‖ ≤ ‖ℓ p.2.2.2‖ * R := by
        calc
          ‖p.2.2.2‖ = ‖ℓ p.2.2.2 • (normalize ℓ p).2.2.2‖ := by
            rw [normalize, smul_inv_smul₀ hl]
          _ = ‖ℓ p.2.2.2‖ * ‖(normalize ℓ p).2.2.2‖ := norm_smul _ _
          _ ≤ ‖ℓ p.2.2.2‖ * R := mul_le_mul_of_nonneg_left hfreq (norm_nonneg _)
      exact (not_lt_of_ge hnrm) hp
    simp [extend, hf]

/-- The radial extension of a smooth compactly supported phase is smooth
at every nonzero spatial covector, even outside the normalizing chart.
Consumer: auxiliary phase regularity in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem contDiffAt_extend_of_hasCompactSupport (ℓ : E →L[ℝ] ℝ)
    {F : TwoTimePoint E → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {q : TwoTimePoint E} (hq : q.2.2.2 ≠ 0) : ContDiffAt ℝ ∞ (extend ℓ F) q := by
  by_cases hl : ℓ q.2.2.2 = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (extend_eventuallyEq_zero_of_linearCoordinate_eq_zero ℓ hc hl hq)
  · exact (ℓ.contDiff.contDiffAt.comp q contDiffAt_snd.snd.snd).mul
      (hF.contDiffAt.comp q (contDiffAt_normalize ℓ hl))

/-- Joint smoothness away from the zero spatial frequency, the precise
regularity asserted for the auxiliary phase in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem contDiffOn_extend_off_zero (ℓ : E →L[ℝ] ℝ)
    {F : TwoTimePoint E → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiffOn ℝ ∞ (extend ℓ F) {q | q.2.2.2 ≠ 0} :=
  fun _ hq ↦ (contDiffAt_extend_of_hasCompactSupport ℓ hF hc hq).contDiffWithinAt

/-- A local extension agreeing near the normalized buffer gives joint germ
agreement with the same conic phase, preserving both times and every jet.
Consumer: supported phase replacement in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem extend_eventuallyEq_phase (ℓ : E →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E))
    {F : TwoTimePoint E → ℝ} {q : TwoTimePoint E} (hq : ℓ q.2.2.2 ≠ 0)
    (he : F =ᶠ[𝓝 (normalize ℓ q)] twoTimePhase C) :
    extend ℓ F =ᶠ[𝓝 q] phase ℓ C := by
  filter_upwards [he.comp_tendsto (contDiffAt_normalize ℓ hq).continuousAt] with p hp
  exact congrArg (fun a ↦ ℓ p.2.2.2 * a) hp

end JanetCartan.RegularSector.Characteristic.ConicPhase
