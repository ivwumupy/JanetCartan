module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Annulus

/-!
# Common annular normalization of transport covectors

The geometric deduction in Step 1 of `app:ch_background:prop:bg-frame`.
The full-phase-chart producer supplies injectivity only on the annulus and
the relative transverse error. No global inverse or conic injectivity is an input.
Physical positions and the spectator are fixed throughout this leaf.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ContinuumNormalReduction.ConicChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Covector dilation in `app:ch_background:eq:bg-Psi`; the incidence parameter
`s` stays fixed. This is deliberately different from scalar multiplication on
the whole product. -/
def radialScale (t : ℝ) (u : ℝ × E) : ℝ × E := (u.1, t • u.2)

/-- Identity dilation in `app:ch_background:eq:bg-Psi`. -/
@[simp] theorem radialScale_one (u : ℝ × E) : radialScale 1 u = u := by
  simp [radialScale]

/-- Composition of covector dilations in `app:ch_background:eq:bg-Psi`. -/
@[simp] theorem radialScale_mul (t r : ℝ) (u : ℝ × E) :
    radialScale t (radialScale r u) = radialScale (t * r) u := by
  simp [radialScale, mul_smul]

/-- An input-only annular chart interface for `app:ch_background:eq:bg-Psi`.
`cone` is the cone over the smaller supported `(s, η̂)` set. For actual data,
`map` is the averaged transport gradient in full time/transverse coordinates.
The strict inequalities ensure that normalization by the transverse output
lands inside the buffered annulus. These hypotheses are to be instantiated by
`jc-full-phase-charts`; they do not assert its construction. -/
structure AnnularData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  map : (ℝ × E) → (ℝ × E)
  cone : Set (ℝ × E)
  innerRadius : ℝ
  outerRadius : ℝ
  error : ℝ
  inner_nonneg : 0 ≤ innerRadius
  error_nonneg : 0 ≤ error
  error_lt_one : error < 1
  inner_buffer : innerRadius * (1 + error) < 1
  outer_buffer : 1 < outerRadius * (1 - error)
  covector_ne_zero : ∀ u ∈ cone, u.2 ≠ 0
  scale_mem : ∀ u ∈ cone, ∀ t : ℝ, 0 < t → radialScale t u ∈ cone
  homogeneous : ∀ u ∈ cone, ∀ t : ℝ, 0 < t → map (radialScale t u) = t • map u
  transverse_close : ∀ u ∈ cone, ‖(map u).2 - u.2‖ ≤ error * ‖u.2‖
  annular_injective : InjOn map
    {u | u ∈ cone ∧ innerRadius < ‖u.2‖ ∧ ‖u.2‖ < outerRadius}

namespace AnnularData

variable (A : AnnularData E)

/-- The buffered annular input set in `app:ch_background:eq:bg-Psi`. -/
def annulus : Set (ℝ × E) :=
  {u | u ∈ A.cone ∧ A.innerRadius < ‖u.2‖ ∧ ‖u.2‖ < A.outerRadius}

/-- Relative transverse comparison gives both magnitude bounds, used for the
common normalization in Step 1 of `app:ch_background:prop:bg-frame`. -/
theorem transverse_norm_bounds {u : ℝ × E} (hu : u ∈ A.cone) :
    (1 - A.error) * ‖u.2‖ ≤ ‖(A.map u).2‖ ∧
      ‖(A.map u).2‖ ≤ (1 + A.error) * ‖u.2‖ := by
  have h := A.transverse_close u hu
  have hl := norm_sub_norm_le u.2 (A.map u).2
  rw [norm_sub_rev] at hl
  have hr := norm_sub_norm_le (A.map u).2 u.2
  constructor <;> nlinarith

/-- Nonzero transverse output on the cone, needed to define the normalization
in `app:ch_background:prop:bg-frame`. -/
theorem transverse_norm_pos {u : ℝ × E} (hu : u ∈ A.cone) :
    0 < ‖(A.map u).2‖ :=
  (mul_pos (sub_pos.mpr A.error_lt_one) (norm_pos_iff.mpr
    (A.covector_ne_zero u hu))).trans_le (A.transverse_norm_bounds hu).1

/-- The lower half of `|k| ≍ |η|` in `app:ch_background:eq:bg-jacobian`.
The upper half also needs a bounded longitudinal component. -/
theorem norm_lower {u : ℝ × E} (hu : u ∈ A.cone) :
    (1 - A.error) * ‖u.2‖ ≤ ‖A.map u‖ :=
  (A.transverse_norm_bounds hu).1.trans (norm_snd_le _)

/-- Transverse output normalization lies strictly in the annular buffer
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normalize_mem_annulus {u : ℝ × E} (hu : u ∈ A.cone) :
    radialScale ‖(A.map u).2‖⁻¹ u ∈ A.annulus := by
  have hp := A.transverse_norm_pos hu
  have hη := norm_pos_iff.mpr (A.covector_ne_zero u hu)
  obtain ⟨hl, hr⟩ := A.transverse_norm_bounds hu
  refine ⟨A.scale_mem u hu _ (inv_pos.mpr hp), ?_, ?_⟩
  all_goals
    simp only [radialScale, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  · have hb := mul_lt_mul_of_pos_right A.inner_buffer hη
    have hm := mul_le_mul_of_nonneg_left hr A.inner_nonneg
    have hlt : A.innerRadius * ‖(A.map u).2‖ < ‖u.2‖ := by nlinarith
    rw [← div_eq_inv_mul]
    exact (lt_div_iff₀ hp).mpr hlt
  · have hb := mul_lt_mul_of_pos_right A.outer_buffer hη
    have ho : 0 < A.outerRadius := by
      nlinarith [sub_pos.mpr A.error_lt_one, A.outer_buffer]
    have hm := mul_le_mul_of_nonneg_left hl ho.le
    have hlt : ‖u.2‖ < A.outerRadius * ‖(A.map u).2‖ := by nlinarith
    rw [← div_eq_inv_mul]
    exact (div_lt_iff₀ hp).mpr hlt

/-- Equal outputs admit one simultaneous positive dilation into the buffered
chart. This supplies the omitted geometric argument in Step 1 of
`app:ch_background:prop:bg-frame`. -/
theorem simultaneous_normalization {u w : ℝ × E}
    (hu : u ∈ A.cone) (hw : w ∈ A.cone) (he : A.map u = A.map w) :
    ∃ t > 0, radialScale t u ∈ A.annulus ∧ radialScale t w ∈ A.annulus := by
  refine ⟨‖(A.map u).2‖⁻¹, inv_pos.mpr (A.transverse_norm_pos hu),
    A.normalize_mem_annulus hu, ?_⟩
  rw [he]
  exact A.normalize_mem_annulus hw

/-- Annular injectivity extends to the full supported cone, as claimed in
Step 1 of `app:ch_background:prop:bg-frame`. -/
theorem injective_on_cone : InjOn A.map A.cone := by
  intro u hu w hw he
  obtain ⟨t, ht, htu, htw⟩ := A.simultaneous_normalization hu hw he
  have he' := A.annular_injective htu htw (by
    rw [A.homogeneous u hu t ht, A.homogeneous w hw t ht, he])
  have := congrArg (radialScale t⁻¹) he'
  simpa [ht.ne'] using this

end AnnularData
end JanetCartan.ContinuumNormalReduction.ConicChart
