module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Jacobian

/-!
# Uniform estimates on the transport cone

The annular upper bounds and determinant gaps imply the full conic estimates
of `app:ch_background:eq:bg-jacobian`. Constants are explicit, hence uniform
in all physical and spectator parameters whenever the annular inputs are.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.ContinuumNormalReduction.ConicChart.AnnularData
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (A : AnnularData E)

/-- An annular output bound gives the upper comparison `|k| ≤ C|η|` in
Step 1 of `app:ch_background:prop:bg-frame`. -/
theorem norm_upper_of_annular_bound {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u ∈ A.annulus, ‖A.map u‖ ≤ M)
    {u : ℝ × E} (hu : u ∈ A.cone) :
    ‖A.map u‖ ≤ (M * (1 + A.error)) * ‖u.2‖ := by
  have hp := A.transverse_norm_pos hu
  have hb := hbound _ (A.normalize_mem_annulus hu)
  rw [A.homogeneous u hu _ (inv_pos.mpr hp), norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), ← div_eq_inv_mul] at hb
  have hb' := (div_le_iff₀ hp).mp hb
  calc
    ‖A.map u‖ ≤ M * ‖(A.map u).2‖ := hb'
    _ ≤ M * ((1 + A.error) * ‖u.2‖) :=
      mul_le_mul_of_nonneg_left (A.transverse_norm_bounds hu).2 hM
    _ = _ := by ring

/-- Compact annular geometry supplies the missing upper magnitude bound;
combined with `norm_lower` this is `|k| ≍ |η|` in
`app:ch_background:prop:bg-frame`. -/
theorem exists_norm_comparison {K : Set (ℝ × E)} (hK : IsCompact K)
    (hsub : A.annulus ⊆ K) (hcont : ContinuousOn A.map K) :
    ∃ C > 0, ∀ u ∈ A.cone,
      (1 - A.error) * ‖u.2‖ ≤ ‖A.map u‖ ∧ ‖A.map u‖ ≤ C * ‖u.2‖ := by
  obtain ⟨M, hM, hbound⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨M * (1 + A.error), mul_pos hM (by linarith [A.error_nonneg]), ?_⟩
  intro u hu
  exact ⟨A.norm_lower hu, A.norm_upper_of_annular_bound hM.le
    (fun w hw ↦ hbound _ ⟨w, hsub hw, rfl⟩) hu⟩

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Smoothness on a compact buffered input set supplies the annular Jacobian
upper bound used by `app:ch_background:eq:bg-jacobian`. In a parameter family,
the producer applies the same compact-image argument jointly in its parameters. -/
theorem exists_annular_jacobian_upper {K : Set (ℝ × E)} (hK : IsCompact K)
    (hsub : A.annulus ⊆ K) (hcont : ContinuousOn (fderiv ℝ A.map) K) :
    ∃ C > 0, ∀ u ∈ A.annulus, A.jacobian u ≤ C := by
  have hj : ContinuousOn (fun u ↦ (fderiv ℝ A.map u).det) K :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hcont
  obtain ⟨C, hC, hb⟩ := (hK.image_of_continuousOn hj).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  simpa only [jacobian, Real.norm_eq_abs] using hb _ ⟨u, hsub hu, rfl⟩

/-- Annular bounds extend to `c|η| ≤ J ≤ C|η|`, with explicit uniform
constants, as required by `app:ch_background:eq:bg-jacobian`. The annular
gaps are supplied by the full phase chart producer. -/
theorem jacobian_bounds_of_annular_bounds
    (hhom : ∀ w : ℝ × E, ∀ t : ℝ, 0 < t →
      A.map (radialScale t w) = t • A.map w)
    (hd : ∀ u ∈ A.cone, DifferentiableAt ℝ A.map u)
    {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : ∀ u ∈ A.annulus, c ≤ A.jacobian u ∧ A.jacobian u ≤ C)
    {u : ℝ × E} (hu : u ∈ A.cone) :
    (c * (1 - A.error)) * ‖u.2‖ ≤ A.jacobian u ∧
      A.jacobian u ≤ (C * (1 + A.error)) * ‖u.2‖ := by
  have hp := A.transverse_norm_pos hu
  obtain ⟨hl, hr⟩ := hb _ (A.normalize_mem_annulus hu)
  rw [A.jacobian_radialScale hhom hd hu (inv_pos.mpr hp), ← div_eq_inv_mul] at hl hr
  have hl' := (le_div_iff₀ hp).mp hl
  have hr' := (div_le_iff₀ hp).mp hr
  constructor
  · calc
      _ = c * ((1 - A.error) * ‖u.2‖) := by ring
      _ ≤ c * ‖(A.map u).2‖ :=
        mul_le_mul_of_nonneg_left (A.transverse_norm_bounds hu).1 hc
      _ ≤ A.jacobian u := hl'
  · calc
      A.jacobian u ≤ C * ‖(A.map u).2‖ := hr'
      _ ≤ C * ((1 + A.error) * ‖u.2‖) :=
        mul_le_mul_of_nonneg_left (A.transverse_norm_bounds hu).2 hC
      _ = _ := by ring

/-- Positive uniform conic Jacobian constants in
`app:ch_background:eq:bg-jacobian`, from positive annular constants. -/
theorem exists_jacobian_bounds
    (hhom : ∀ w : ℝ × E, ∀ t : ℝ, 0 < t →
      A.map (radialScale t w) = t • A.map w)
    (hd : ∀ u ∈ A.cone, DifferentiableAt ℝ A.map u)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ u ∈ A.annulus, c ≤ A.jacobian u ∧ A.jacobian u ≤ C) :
    ∃ a > 0, ∃ b > 0, ∀ u ∈ A.cone,
      a * ‖u.2‖ ≤ A.jacobian u ∧ A.jacobian u ≤ b * ‖u.2‖ :=
  ⟨c * (1 - A.error), mul_pos hc (sub_pos.mpr A.error_lt_one),
    C * (1 + A.error), mul_pos hC (by linarith [A.error_nonneg]),
    fun _ hu ↦ A.jacobian_bounds_of_annular_bounds hhom hd hc.le hC.le hb hu⟩

end JanetCartan.ContinuumNormalReduction.ConicChart.AnnularData
