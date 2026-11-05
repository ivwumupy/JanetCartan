module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.Coercivity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CurrentTransfer

/-! # Local and global bounds for a perturbation of the same measured row -/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.ContinuumNormal.ActualConstruction
open ContinuumRow AmplitudeBound

/-- Transfer the row norm, the local adjoint gap and the global augmented gap
when the two physical normals differ by at most half the smaller gap. Using
the same inner cutoff cancels the exterior square exactly. This is the common
last step of the source and finite-history comparisons
(`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-global-bound`). -/
theorem retained_row_half_gaps_of_physical_normal_error {n : ℕ} {ι : Type*} [Fintype ι]
    (image image₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (V V₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {rInner : ℝ} (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2)
    {g G M : ℝ} (hg : 0 < g) (hG : 0 < G)
    (hzeroM : ‖physicalRow image₀ V₀‖ ≤ M)
    (hzeroLocal : ∀ w : OutputL2 n,
      (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
      g * ‖w‖ ^ 2 ≤ ‖(physicalRow image₀ V₀).adjoint w‖ ^ 2)
    (hzeroGlobal : ∀ w : OutputL2 n, G * ‖w‖ ^ 2 ≤
      inner ℝ (augmentedNormal image₀ V₀ (innerCutoff hrInner hInnerCell) w) w)
    (hcomparison : ‖NormalPerturbation.normal (physicalRow image V) -
      NormalPerturbation.normal (physicalRow image₀ V₀)‖ ≤ min g G / 2) :
    ‖physicalRow image V‖ ≤ Real.sqrt (M ^ 2 + min g G / 2) ∧
    (∀ w : OutputL2 n,
      (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
      g / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2) ∧
    (∀ w : OutputL2 n, G / 2 * ‖w‖ ^ 2 ≤
      inner ℝ (augmentedNormal image V (innerCutoff hrInner hInnerCell) w) w) ∧
    (∀ w : OutputL2 n, G / 2 * ‖w‖ ^ 2 ≤
      ‖(augmentedRow image V (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
    (∀ w : OutputL2 n, ∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
      exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) := by
  let κ := min g G
  have hκ : 0 < κ := lt_min hg hG
  let Acurrent := physicalRow image V
  let Azero := physicalRow image₀ V₀
  have hcurrentBound : ‖Acurrent‖ ≤ Real.sqrt (M ^ 2 + κ / 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    have hnorm := norm_le_norm_add_norm_sub
      (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)
    rw [NormalPerturbation.norm_normal, NormalPerturbation.norm_normal] at hnorm
    rw [norm_sub_rev (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)] at hnorm
    have hsq : ‖Azero‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzeroM 2
    linarith only [hnorm, hcomparison, hsq]
  have hlocal (w : OutputL2 n)
      (hw : ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) :
      g / 2 * ‖w‖ ^ 2 ≤ ‖Acurrent.adjoint w‖ ^ 2 := by
    have hgapNormal : ∀ f ∈ {f : OutputL2 n | ∀ᵐ x ∂volume,
        x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → f x = 0},
        g * ‖f‖ ^ 2 ≤ RCLike.re (inner ℝ (NormalPerturbation.normal Azero f) f) := by
      intro f hf
      apply (hzeroLocal f hf).trans_eq
      simpa only [ContinuousLinearMap.adjoint_adjoint, NormalPerturbation.normal] using
        Azero.adjoint.apply_norm_sq_eq_inner_adjoint_left f
    have h := NormalPerturbation.quadratic_lower_bound_of_norm_sub_le
      (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)
      {f | ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → f x = 0}
      (g := g) (ε := g / 2) hgapNormal
      (hcomparison.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) w hw
    have heq := Acurrent.adjoint.apply_norm_sq_eq_inner_adjoint_left w
    simp only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real,
      ContinuousLinearMap.comp_apply] at heq
    change (g - g / 2) * ‖w‖ ^ 2 ≤ inner ℝ (Acurrent (Acurrent.adjoint w)) w at h
    rw [← heq] at h
    convert h using 1
    ring
  have haugmented : ‖augmentedNormal image V (innerCutoff hrInner hInnerCell) -
      augmentedNormal image₀ V₀ (innerCutoff hrInner hInnerCell)‖ ≤ κ / 2 := by
    have heq : augmentedNormal image V (innerCutoff hrInner hInnerCell) -
        augmentedNormal image₀ V₀ (innerCutoff hrInner hInnerCell) =
        NormalPerturbation.normal Acurrent - NormalPerturbation.normal Azero := by
      rw [augmentedNormal_eq_sum, augmentedNormal_eq_sum]
      simp only [NormalPerturbation.normal, Acurrent, Azero, physicalRow_normal]
      abel
    rw [heq]
    exact hcomparison
  have hcurrentGlobal (w : OutputL2 n) : G / 2 * ‖w‖ ^ 2 ≤
      inner ℝ (augmentedNormal image V (innerCutoff hrInner hInnerCell) w) w :=
    augmented_half_gap_of_normal_comparison image image₀ V V₀
      (innerCutoff hrInner hInnerCell) univ (fun f _ ↦ hzeroGlobal f) haugmented
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) w (mem_univ w)
  refine ⟨hcurrentBound, hlocal, hcurrentGlobal, ?_, inner_exterior_zero_on_core hrInner hInnerCell⟩
  intro w
  have heq := (augmentedRow image V
    (innerCutoff hrInner hInnerCell)).adjoint.apply_norm_sq_eq_inner_adjoint_left w
  apply (hcurrentGlobal w).trans_eq
  simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real, augmentedNormal] using heq.symm

end JanetCartan.ContinuumNormal.ActualConstruction
