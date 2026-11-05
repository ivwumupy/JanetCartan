module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Positive density amplitudes

The scalar step in `app:ch_background:prop:bg-positive` is
`r = σ * sqrt (1 + v)`. We prove its positivity, exact density identity,
smoothness, and pointwise stability on the positive density interval.
The pointwise estimates are also ingredients of
`app:ch_mean_pairs:eq:mean-density-lipschitz`; they do not assert that equation's
Sobolev estimate for the transported Hermitian mean.

All positivity and smoothness assumptions are explicit. No existence of a
positive background, transport estimate, or higher derivative estimate is used.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

/-- `app:ch_background:prop:bg-positive`: the amplitude with corrected density `σ²(1+v)`. -/
def positiveDensityAmplitude (σ v : ℝ) : ℝ :=
  σ * Real.sqrt (1 + v)

/-- `app:ch_background:prop:bg-positive`: zero correction preserves the initial scalar. -/
@[simp] theorem positiveDensityAmplitude_zero (σ : ℝ) :
    positiveDensityAmplitude σ 0 = σ := by
  simp [positiveDensityAmplitude]

/-- `app:ch_background:prop:bg-positive`: the corrected amplitude is positive. -/
theorem positiveDensityAmplitude_pos {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < 1 + v) :
    0 < positiveDensityAmplitude σ v :=
  mul_pos hσ (Real.sqrt_pos.mpr hv)

/-- `app:ch_background:prop:bg-positive`: the square is exactly the corrected density. -/
theorem positiveDensityAmplitude_sq {σ v : ℝ} (hv : 0 ≤ 1 + v) :
    positiveDensityAmplitude σ v ^ 2 = σ ^ 2 * (1 + v) := by
  rw [positiveDensityAmplitude, mul_pow, Real.sq_sqrt hv]

/-- `app:ch_background:prop:bg-positive`: the full density interval gives explicit amplitude
bounds, with no change to the scale `σ`. -/
theorem positiveDensityAmplitude_mem_Icc {σ v : ℝ} (hσ : 0 ≤ σ)
    (hv : 1 + v ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    positiveDensityAmplitude σ v ∈
      Set.Icc (σ * Real.sqrt (1 / 2)) (σ * Real.sqrt (3 / 2)) :=
  ⟨mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.1) hσ,
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.2) hσ⟩

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: rationalization of the positive square root. -/
theorem sqrt_sub_sqrt_eq_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
  apply (eq_div_iff (ne_of_gt (add_pos (Real.sqrt_pos.mpr ha)
    (Real.sqrt_pos.mpr hb)))).mpr
  nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: quantitative square-root stability above
any strictly positive lower density bound. -/
theorem abs_sqrt_sub_sqrt_le_div {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / (2 * Real.sqrt c) := by
  have ha' : 0 < a := hc.trans_le ha
  have hb' : 0 < b := hc.trans_le hb
  rw [sqrt_sub_sqrt_eq_div ha' hb', abs_div,
    abs_of_pos (add_pos (Real.sqrt_pos.mpr ha') (Real.sqrt_pos.mpr hb'))]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  linarith [Real.sqrt_le_sqrt ha, Real.sqrt_le_sqrt hb]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: square root is nonexpansive on
`[1/2, 3/2]`, and in fact on the whole half-line `[1/2, ∞)`. -/
theorem abs_sqrt_sub_sqrt_le_abs {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a)
    (hb : (1 / 2 : ℝ) ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  calc
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / (2 * Real.sqrt (1 / 2)) :=
      abs_sqrt_sub_sqrt_le_div (by norm_num) ha hb
    _ ≤ |a - b| := (div_le_iff₀ (by positivity)).mpr (by
      nlinarith [abs_nonneg (a - b)])

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the sharp lower-density constant for
the pointwise amplitude difference. -/
theorem positiveDensityAmplitude_abs_sub_le_div {σ v w : ℝ}
    (hv : (1 / 2 : ℝ) ≤ 1 + v) (hw : (1 / 2 : ℝ) ≤ 1 + w) :
    |positiveDensityAmplitude σ v - positiveDensityAmplitude σ w| ≤
      |σ| * (|v - w| / (2 * Real.sqrt (1 / 2))) := by
  rw [positiveDensityAmplitude, positiveDensityAmplitude, ← mul_sub, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg σ)
  simpa only [add_sub_add_left_eq_sub] using
    abs_sqrt_sub_sqrt_le_div (by norm_num : (0 : ℝ) < 1 / 2) hv hw

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: a simpler pointwise Lipschitz bound
uniform in the density corrections. -/
theorem positiveDensityAmplitude_abs_sub_le {σ v w : ℝ}
    (hv : (1 / 2 : ℝ) ≤ 1 + v) (hw : (1 / 2 : ℝ) ≤ 1 + w) :
    |positiveDensityAmplitude σ v - positiveDensityAmplitude σ w| ≤ |σ| * |v - w| := by
  rw [positiveDensityAmplitude, positiveDensityAmplitude, ← mul_sub, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg σ)
  simpa only [add_sub_add_left_eq_sub] using abs_sqrt_sub_sqrt_le_abs hv hw

/-- `app:ch_background:eq:bg-positive-profile`: pointwise proximity to the initial scalar. -/
theorem positiveDensityAmplitude_abs_sub_initial_le {σ v : ℝ}
    (hv : (1 / 2 : ℝ) ≤ 1 + v) :
    |positiveDensityAmplitude σ v - σ| ≤ |σ| * |v| := by
  simpa using positiveDensityAmplitude_abs_sub_le (σ := σ) (w := 0) hv (by norm_num)

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: density differences are exactly affine
in the correction, before transport or taking Hermitian products. -/
theorem positiveDensityAmplitude_sq_sub_sq {σ v w : ℝ}
    (hv : 0 ≤ 1 + v) (hw : 0 ≤ 1 + w) :
    positiveDensityAmplitude σ v ^ 2 - positiveDensityAmplitude σ w ^ 2 =
      σ ^ 2 * (v - w) := by
  rw [positiveDensityAmplitude_sq hv, positiveDensityAmplitude_sq hw]
  ring

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : WithTop ℕ∞} {v : E → ℝ} {s : Set E} {x : E}

/-- `app:ch_background:prop:bg-positive`: local smoothness of the positive amplitude. -/
theorem contDiffAt_positiveDensityAmplitude (σ : ℝ) (hv : ContDiffAt ℝ n v x)
    (hpos : 0 < 1 + v x) :
    ContDiffAt ℝ n (fun y ↦ positiveDensityAmplitude σ (v y)) x :=
  contDiffAt_const.mul ((contDiffAt_const.add hv).sqrt (ne_of_gt hpos))

/-- `app:ch_background:prop:bg-positive`: smoothness on a carrier or initial-variable domain. -/
theorem contDiffOn_positiveDensityAmplitude (σ : ℝ) (hv : ContDiffOn ℝ n v s)
    (hpos : ∀ x ∈ s, 0 < 1 + v x) :
    ContDiffOn ℝ n (fun x ↦ positiveDensityAmplitude σ (v x)) s :=
  contDiffOn_const.mul ((contDiffOn_const.add hv).sqrt (fun x hx ↦ (hpos x hx).ne'))

/-- `app:ch_background:prop:bg-positive`: smoothness in all variables, at any order including
`∞`, whenever the corrected density stays strictly positive. -/
theorem contDiff_positiveDensityAmplitude (σ : ℝ) (hv : ContDiff ℝ n v)
    (hpos : ∀ x, 0 < 1 + v x) :
    ContDiff ℝ n (fun x ↦ positiveDensityAmplitude σ (v x)) :=
  contDiff_const.mul ((contDiff_const.add hv).sqrt (fun x ↦ (hpos x).ne'))

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: a smooth varying initial amplitude can
also multiply the positive square root. -/
theorem contDiffOn_mul_sqrt_one_add {r : E → ℝ} (hr : ContDiffOn ℝ n r s)
    (hv : ContDiffOn ℝ n v s) (hpos : ∀ x ∈ s, 0 < 1 + v x) :
    ContDiffOn ℝ n (fun x ↦ positiveDensityAmplitude (r x) (v x)) s :=
  hr.mul ((contDiffOn_const.add hv).sqrt (fun x hx ↦ (hpos x hx).ne'))

/-- `app:ch_background:prop:bg-positive`: the scalar construction on the stated density
interval is smooth, strictly positive, and has exactly the prescribed square. -/
theorem positiveDensityAmplitude_properties {σ : ℝ} (hσ : 0 < σ)
    (hv : ContDiff ℝ n v) (hinterval : ∀ x, 1 + v x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    ContDiff ℝ n (fun x ↦ positiveDensityAmplitude σ (v x)) ∧
      (∀ x, 0 < positiveDensityAmplitude σ (v x)) ∧
      (∀ x, positiveDensityAmplitude σ (v x) ^ 2 = σ ^ 2 * (1 + v x)) := by
  have hpos (x : E) : 0 < 1 + v x := lt_of_lt_of_le (by norm_num) (hinterval x).1
  exact ⟨contDiff_positiveDensityAmplitude σ hv hpos,
    fun x ↦ positiveDensityAmplitude_pos hσ (hpos x),
    fun x ↦ positiveDensityAmplitude_sq (hpos x).le⟩

end Smoothness

end JanetCartan
