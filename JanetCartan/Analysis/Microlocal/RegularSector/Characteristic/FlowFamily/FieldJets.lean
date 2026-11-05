module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeChart
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Primitive budgets for the two-time Hamilton field

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the actual
autonomized field costs one derivative of the scalar root. These estimates
provide the field bounds for the common flow construction in `FlowFamily.Flow`.
They concern the existing `rootHamiltonField`, with its physical sign convention.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance rootFieldJetsNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- The spatial part of `(1,-h_η,h_y)` is a fixed linear map of `dh`
(`app:ch_regular_base:lem:characteristic-kernel`). The clock is added separately. -/
def rootFieldOfDifferential : (RootState E →L[ℝ] ℝ) →L[ℝ] RootState E :=
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let iy := (ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inl ℝ E E)
  let ip := (ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inr ℝ E E)
  (0 : (RootState E →L[ℝ] ℝ) →L[ℝ] ℝ).prod
    ((-(R.comp ((ContinuousLinearMap.compL ℝ E (RootState E) ℝ).flip ip))).prod
      (R.comp ((ContinuousLinearMap.compL ℝ E (RootState E) ℝ).flip iy)))

set_option backward.isDefEq.respectTransparency false in
/-- The Riesz isometry and the product maximum norm give norm at most one
for the scalar-differential-to-spatial-field map
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_rootFieldOfDifferential_le : ‖rootFieldOfDifferential (E := E)‖ ≤ 1 := by
  refine (rootFieldOfDifferential (E := E)).opNorm_le_bound zero_le_one ?_
  intro L
  change ‖(0, (-(InnerProductSpace.toDual ℝ E).symm
    (L.comp ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inr ℝ E E))),
    (InnerProductSpace.toDual ℝ E).symm
    (L.comp ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inl ℝ E E)))))‖
      ≤ 1 * ‖L‖
  simp only [Prod.norm_def, norm_zero, norm_neg, LinearIsometryEquiv.norm_map, one_mul]
  refine max_le (norm_nonneg L) (max_le ?_ ?_)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) ?_
    intro v
    simpa using L.le_opNorm (0, (0, v))
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) ?_
    intro v
    simpa using L.le_opNorm (0, (v, 0))

/-- The fixed differential map recovers the existing Hamilton field exactly
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootHamiltonField_eq_clock_add (h : RootState E → ℝ) :
    rootHamiltonField h = (fun _ ↦ (1, (0, 0))) + rootFieldOfDifferential ∘ fderiv ℝ h := by
  funext z
  simp [rootHamiltonField, rootFieldOfDifferential, rootPositionGradient, rootMomentumGradient]

/-- Every field jet costs exactly one primitive root derivative. The extra
one accounts for the autonomous clock, including at order zero
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_iteratedFDeriv_rootHamiltonField_le
    {h : RootState E → ℝ} {D : Set (RootState E)} (hD : IsOpen D)
    {n : ℕ} (hh : ContDiffOn ℝ (n + 1) h D) {z : RootState E} (hz : z ∈ D) :
    ‖iteratedFDeriv ℝ n (rootHamiltonField h) z‖ ≤
      1 + ‖iteratedFDeriv ℝ (n + 1) h z‖ := by
  have hd : ContDiffAt ℝ n (fderiv ℝ h) z :=
    (hh.fderiv_of_isOpen hD (by simp)).contDiffAt (hD.mem_nhds hz)
  have hl := (rootFieldOfDifferential (E := E)).contDiff.contDiffAt.comp z hd
  have hc : ‖iteratedFDeriv ℝ n (fun _ : RootState E ↦ ((1, (0, 0)) : RootState E)) z‖ ≤ 1 := by
    by_cases hn : n = 0
    · subst n; simp [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne hn]; simp
  rw [rootHamiltonField_eq_clock_add,
    iteratedFDeriv_add_apply contDiffAt_const hl]
  apply (norm_add_le _ _).trans (add_le_add hc ?_)
  calc
    _ ≤ ‖rootFieldOfDifferential (E := E)‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ h) z‖ :=
      (rootFieldOfDifferential (E := E)).norm_iteratedFDeriv_comp_left hd le_rfl
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ h) z‖ :=
      mul_le_mul_of_nonneg_right norm_rootFieldOfDifferential_le (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- The joint primitive `cNorm` bound for the actual root field, with reserve
one and constants independent of the root. This supplies both the Picard bounds
and the single-high flow estimates
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem cNorm_rootHamiltonField_le
    {h : RootState E → ℝ} {D K : Set (RootState E)} (hD : IsOpen D)
    (hK : IsCompact K) (hKD : K ⊆ D) (n : ℕ) (hh : ContDiffOn ℝ (n + 1) h D) :
    cNorm K n (rootHamiltonField h) ≤ (n + 1 : ℝ) * (1 + cNorm K (n + 1) h) := by
  apply (cNorm_le_sum_of_bounds (C := fun _ ↦ 1 + cNorm K (n + 1) h)
    (fun _ _ ↦ add_nonneg zero_le_one (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp; ring)
  intro k hk z hz
  have hkn : (k + 1 : ℕ∞ω) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hk 1
  apply (norm_iteratedFDeriv_rootHamiltonField_le hD (hh.of_le hkn) (hKD hz)).trans
  exact add_le_add_right (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun z hz ↦ hh.contDiffAt (hD.mem_nhds (hKD hz))) hz
    (Nat.add_le_add_right hk 1)) 1

end JanetCartan.RegularSector.Characteristic
