module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions

/-!
# Initial-scalar buffers from the retained forward flow

The full-modulation producer fixes `Rc`, `τc`, and `Mc` before immersion and
scalar budgets. Its forward `C¹` bound, initial condition, inverse identity,
and inverse range suffice to bound the SAME inverse footpoint. No inverse
derivative estimate is needed. The scalar radius `R` is independent of `Rc`.

Consumer: the literal kernel agreement and amplitude extensions for
`app:ch_background:prop:bg-adjoint`, with the original initial norm domain
from `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
open ContinuumRow PhaseExtension AmplitudeProfiles ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ActualFlow FlowAmplitude

variable {n : ℕ}

/-- The retained forward `C¹` bound controls the inverse footpoint by its
time displacement. Every premise is exported by
`CurrentCoefficientProfiles.exists_full_joint_leading_wave_before_geometry`.
This is the quantitative input to the budget-independent scalar buffer in
`app:ch_background:prop:bg-adjoint`. -/
theorem inverseFootpoint_dist_le_of_forward_cNorm
    (z₀ : Euclidean 3) {Rc τc Mc : ℝ} (hRc : 0 < Rc) (hτc : 0 < τc)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
    (hy : MapsTo (fun q ↦ (q.1, y q)) D
      (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)))
    (hφ₀ : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8), φ (0, p) = p)
    (hφy : ∀ q ∈ D, φ (q.1, y q) = q.2)
    (hφ : ContDiffOn ℝ ∞ φ
      (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 4)))
    (hMc : cNorm (Icc (-τc) τc ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 φ ≤ Mc)
    {q : ℝ × (Euclidean (n - 1) × Euclidean 3)} (hq : q ∈ D) :
    dist (y q) q.2 ≤ Mc * |q.1| := by
  let pc := ((0 : Euclidean (n - 1)), z₀)
  let J := Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)
  let O := Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)
  have hJO : J ⊆ O := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      (mem_closedBall.mp hp.2).trans_lt (by linarith)⟩
  have hJ : IsCompact J := isCompact_Icc.prod (isCompact_closedBall ..)
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_ball
  have hφat (p) (hp : p ∈ J) : ContDiffAt ℝ ∞ φ p :=
    hφ.contDiffAt (hO.mem_nhds (hJO hp))
  have hder (p) (hp : p ∈ J) : ‖fderiv ℝ φ p‖ ≤ Mc := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
      (fun p hp ↦ (hφat p hp).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hp (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans hMc
  have hyp := hy hq
  have hzero : (0, y q) ∈ J :=
    ⟨⟨by linarith, hτc.le⟩, ball_subset_closedBall hyp.2⟩
  have htime : (q.1, y q) ∈ J :=
    ⟨⟨hyp.1.1.le, hyp.1.2.le⟩, ball_subset_closedBall hyp.2⟩
  have hh := ((convex_Icc (-τc) τc).prod (convex_closedBall pc (Rc / 8))).norm_image_sub_le_of_norm_fderiv_le
    (fun p hp ↦ (hφat p hp).differentiableAt (by simp)) hder hzero htime
  rw [hφy q hq, hφ₀ _ hyp.2] at hh
  simpa only [← dist_eq_norm, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg),
    Real.dist_eq, sub_zero, max_eq_left (abs_nonneg q.1), dist_comm q.2] using hh

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Choose a cap from the retained carrier geometry BEFORE source-dependent
immersion or scalar budgets. The complete supported chart lies in every
retained carrier tube and its SAME inverse footpoint lies in the original
full-modulation scalar's `R/16` ball. The two radii `Rc` and `R` are unrelated.
All flow hypotheses are literal outputs of
`exists_full_joint_leading_wave_before_geometry`; no inverse-flow norm is
assumed (`app:ch_background:eq:bg-T`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_supportedChart_initialBuffer_before_budgets
    (z₀ : Euclidean 3) {R Rc τc Mc : ℝ}
    (hR : 0 < R) (hRc : 0 < Rc) (hτc : 0 < τc) (hMc : 0 < Mc) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ}, 0 < a → a < cap →
      ∀ (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
      let pc := ((0 : Euclidean (n - 1)), z₀)
      Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ D →
      MapsTo (fun q ↦ (q.1, y q)) D (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) →
      (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) →
      (∀ q ∈ D, φ (q.1, y q) = q.2) →
      ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) →
      cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
        (supportedChart z₀ a) D ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ odeInitialPoint T y (p.2, p.1))
        (supportedChart z₀ a) (ball pc (R / 16)) := by
  let δ := min (τc / 2) (min (Rc / 64) (min (R / 64) (R / (64 * Mc))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδτ : δ ≤ τc / 2 := min_le_left ..
  have hδRc : δ ≤ Rc / 64 := (min_le_right ..).trans (min_le_left ..)
  have hδR : δ ≤ R / 64 :=
    (min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))
  have hδMc : Mc * δ ≤ R / 64 := by
    have hh : δ ≤ R / (64 * Mc) :=
      (min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))
    have hh' := (le_div_iff₀ (by positivity : 0 < 64 * Mc)).mp hh
    nlinarith
  obtain ⟨cap, hcap, hmaps⟩ := exists_supportedChart_flowCylinder_cap T z₀ hδ
    (show 0 < 32 * δ by positivity)
  refine ⟨cap, hcap, ?_⟩
  intro a ha hacap D φ y pc hcover hy hφ₀ hφy hφ hflow
  have hsmall (p) (hp : p ∈ supportedChart (n := n) z₀ a) :
      coordinates (adaptedCoordinates T.data.adapted)
        (p.1, CanonicalCarrier.parameter p.2) ∈ Ioo (-δ) δ ×ˢ ball pc δ := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (32 : ℝ) ≠ 0)] using
      hmaps ha hacap hp
  have hsupport : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (supportedChart z₀ a) D := by
    intro p hp
    have hh := hsmall p hp
    exact hcover ⟨⟨by linarith [hh.1.1], by linarith [hh.1.2]⟩,
      (mem_ball.mp hh.2).trans_le (by linarith)⟩
  refine ⟨hsupport, ?_⟩
  intro p hp
  let q := coordinates (adaptedCoordinates T.data.adapted)
    (p.1, CanonicalCarrier.parameter p.2)
  have hq := hsmall p hp
  have hdis := inverseFootpoint_dist_le_of_forward_cNorm z₀ hRc hτc φ y D
    hy hφ₀ hφy hφ hflow (hsupport hp)
  have ht : Mc * |q.1| ≤ R / 64 :=
    (mul_le_mul_of_nonneg_left (abs_lt.mpr hq.1).le hMc.le).trans hδMc
  have hp' : dist q.2 pc < R / 64 := (mem_ball.mp hq.2).trans_le hδR
  have htri := dist_triangle (y q) q.2 pc
  change dist (y q) pc < R / 16
  change dist (y q) q.2 ≤ Mc * |q.1| at hdis
  linarith

end JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
