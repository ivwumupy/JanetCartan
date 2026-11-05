module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Autonomous augmentation of a time-rescaled flow

The construction used to turn the spatial flow estimate into the joint estimate
in `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`. The extra state coordinate is constant in time.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set Metric

namespace JanetCartan.TimeRescaling

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the augmented autonomous field. -/
def field (l c : ℝ) (V : E → E) (y : E × ℝ) : E × ℝ :=
  ((l / c * y.2) • V y.1, 0)

/-- `app:ch_regular_base:lem:buffered-interpolation`: the augmented initial section. -/
def sectionMap (c : ℝ) (σ : P → E) (p : P × ℝ) : E × ℝ := (σ p.1, c * p.2)

/-- `app:lem:common-hamilton-phase`: the actual time-rescaled flow. -/
def flow (t₀ l c : ℝ) (Φ : P × ℝ → E) (p : (P × ℝ) × ℝ) : E × ℝ :=
  (Φ (p.1.1, t₀ + l * p.1.2 * p.2), c * p.1.2)

omit [NormedSpace ℝ P] in
/-- `app:lem:common-hamilton-phase`: the enlarged original interval contains every
rescaled time on the explicit open parameter and auxiliary-time domains. -/
theorem rescaledTime_mem {z : P} {R q l t₀ : ℝ} (hl : 0 < l) (hq : 0 < q)
    {p : P × ℝ} (hp : p ∈ ball (z, 0) R) {u : ℝ} (hu : u ∈ Ioo (-q) q) :
    t₀ + l * p.2 * u ∈ Ioo (t₀ - l * q * R) (t₀ + l * q * R) := by
  have hp' : dist p.1 z < R ∧ |p.2| < R := by
    simpa [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] using hp
  have hu' : |u| < q := abs_lt.mpr hu
  have hab : |l * p.2 * u| < l * q * R := by
    rw [abs_mul, abs_mul, abs_of_pos hl]
    calc
      l * |p.2| * |u| ≤ l * |p.2| * q :=
        mul_le_mul_of_nonneg_left hu'.le (mul_nonneg hl.le (abs_nonneg _))
      _ < l * R * q := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hp'.2 hl) hq
      _ = _ := by ring
  exact ⟨by linarith [(abs_lt.mp hab).1], by linarith [(abs_lt.mp hab).2]⟩

/-- `app:ch_regular_base:lem:buffered-interpolation`: smoothness of the field on
`W × univ`, for the spatial-flow theorem's open state domain. -/
theorem contDiffOn_field {W : Set E} {V : E → E} (hV : ContDiffOn ℝ ∞ V W)
    (l c : ℝ) : ContDiffOn ℝ ∞ (field l c V) (W ×ˢ univ) := by
  exact ((contDiffOn_const.mul contDiffOn_snd).smul
    (hV.comp contDiffOn_fst (fun _ h ↦ h.1))).prodMk contDiffOn_const

/-- `app:ch_regular_base:lem:buffered-interpolation`: smoothness of the section on
the augmented parameter ball. -/
theorem contDiffOn_sectionMap {z : P} {R : ℝ} {σ : P → E}
    (hσ : ContDiffOn ℝ ∞ σ (ball z R)) (c : ℝ) :
    ContDiffOn ℝ ∞ (sectionMap c σ) (ball (z, 0) R) := by
  apply (hσ.comp contDiffOn_fst ?_).prodMk (contDiffOn_const.mul contDiffOn_snd)
  intro p hp
  exact (show dist p.1 z ≤ dist p (z, 0) by rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hp

/-- `app:lem:common-hamilton-phase`: joint smoothness of the constructed flow
on the explicit augmented parameter ball times `(-q,q)`. -/
theorem contDiffOn_flow {z : P} {R q l t₀ c : ℝ} (hl : 0 < l) (hq : 0 < q)
    {Φ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (ball z R ×ˢ Ioo (t₀ - l * q * R) (t₀ + l * q * R))) :
    ContDiffOn ℝ ∞ (flow t₀ l c Φ) (ball (z, 0) R ×ˢ Ioo (-q) q) := by
  apply (hΦ.comp (contDiffOn_fst.fst.prodMk
    (contDiffOn_const.add ((contDiffOn_const.mul contDiffOn_fst.snd).mul
      contDiffOn_snd))) ?_).prodMk (contDiffOn_const.mul contDiffOn_fst.snd)
  intro p hp
  refine ⟨?_, rescaledTime_mem hl hq hp.1 hp.2⟩
  exact (show dist p.1.1 z ≤ dist p.1 (z, 0) by
    rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hp.1

omit [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:lem:common-hamilton-phase`: the constructed flow has the prescribed
augmented initial section at auxiliary time zero. -/
theorem flow_initial {z : P} {R t₀ l c : ℝ} {σ : P → E} {Φ : P × ℝ → E}
    (hinit : ∀ p ∈ ball z R, Φ (p, t₀) = σ p)
    {p : P × ℝ} (hp : p ∈ ball (z, 0) R) :
    flow t₀ l c Φ (p, 0) = sectionMap c σ p := by
  simp only [flow, sectionMap, mul_zero, add_zero]
  have hp₁ : p.1 ∈ ball z R :=
    (show dist p.1 z ≤ dist p (z, 0) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hp
  rw [hinit p.1 hp₁]

omit [NormedSpace ℝ P] in
/-- `app:lem:common-hamilton-phase`: the chain rule proves the actual autonomous
ODE, including the stationary extra coordinate. -/
theorem hasDerivAt_flow {z : P} {R q l t₀ c : ℝ} (hl : 0 < l) (hq : 0 < q)
    (hc : c ≠ 0) {V : E → E} {Φ : P × ℝ → E}
    (hode : ∀ p ∈ ball z R, ∀ t ∈ Ioo (t₀ - l * q * R) (t₀ + l * q * R),
      HasDerivAt (fun t' ↦ Φ (p, t')) (V (Φ (p, t))) t)
    {p : P × ℝ} (hp : p ∈ ball (z, 0) R) {u : ℝ} (hu : u ∈ Ioo (-q) q) :
    HasDerivAt (fun v ↦ flow t₀ l c Φ (p, v))
      (field l c V (flow t₀ l c Φ (p, u))) u := by
  have hp₁ : p.1 ∈ ball z R :=
    (show dist p.1 z ≤ dist p (z, 0) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hp
  have h := (hode p.1 hp₁ _ (rescaledTime_mem hl hq hp hu)).scomp u
    (((hasDerivAt_id u).const_mul (l * p.2)).const_add t₀)
  have heq : l / c * (c * p.2) = l * p.2 := by field_simp
  simpa only [flow, field, heq, mul_one, Function.comp_apply, id_eq] using
    h.prodMk (hasDerivAt_const u (c * p.2))

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
/-- `app:ch_regular_base:lem:buffered-interpolation`: containment in the augmented
state ball follows from the original state containment and the low scaling choice. -/
theorem flow_mem_closedBall {z : P} {w : E} {ρ R τ q l t₀ c : ℝ}
    (hρR : ρ < R) (hl : 0 < l) (hq : 0 < q) (hc : 0 ≤ c) (hcρ : c * ρ ≤ τ)
    {Φ : P × ℝ → E}
    (hrange : ∀ p ∈ closedBall z ρ, ∀ t ∈ Ioo (t₀ - l * q * R) (t₀ + l * q * R),
      Φ (p, t) ∈ closedBall w τ)
    {p : P × ℝ} (hp : p ∈ closedBall (z, 0) ρ) {u : ℝ} (hu : u ∈ Ioo (-q) q) :
    flow t₀ l c Φ (p, u) ∈ closedBall (w, 0) τ := by
  have hp' : dist p.1 z ≤ ρ ∧ |p.2| ≤ ρ := by
    simpa [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq] using hp
  have ht := rescaledTime_mem (t₀ := t₀) hl hq (closedBall_subset_ball hρR hp) hu
  have hs := hrange p.1 hp'.1 _ ht
  change max (dist (Φ _) w) (dist (c * p.2) 0) ≤ τ
  apply max_le hs
  simpa [Real.dist_eq, abs_mul, abs_of_nonneg hc] using
    (mul_le_mul_of_nonneg_left hp'.2 hc).trans hcρ

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:lem:common-hamilton-phase`: evaluating at auxiliary time one and
projecting recovers the original flow exactly. -/
theorem flow_recover (t₀ c : ℝ) {l : ℝ} (hl : l ≠ 0) (Φ : P × ℝ → E) (p : P × ℝ) :
    (flow t₀ l c Φ ((p.1, (p.2 - t₀) / l), 1)).1 = Φ p := by
  simp only [flow, mul_one]
  rw [mul_div_cancel₀ _ hl, add_sub_cancel]

end JanetCartan.TimeRescaling
