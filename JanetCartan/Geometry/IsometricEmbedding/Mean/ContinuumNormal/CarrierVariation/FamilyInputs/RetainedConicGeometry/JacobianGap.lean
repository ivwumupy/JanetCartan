module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.Refinement

/-!
# Persistence of the literal retained Jacobian gap

The determinant is estimated before taking its absolute value. Thus its
positive lower bound is deduced from primitive transport closeness, without
assuming positivity or smoothness of the varying absolute Jacobian.

Consumer: `exists_retained_conic_primitives_sub_tolerance`. Sources:
`app:ch_background:eq:bg-jacobian`, `app:ch_background:prop:bg-frame`, and
`app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol

/-- A positive lower bound for the LITERAL absolute Jacobian persists under
a primitive order-two perturbation. Its smoothness on `interior K` is a
conclusion. Taking `K` to be the outer compact buffer gives one common open
smoothness region for all the varying Jacobians. The reference lower bound
is supplied by `exists_retained_augmented_refinement` (`bg-jacobian`). -/
theorem exists_retained_literal_jacobian_gap
    {n : ℕ} {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {K W B : Set (InputVariables n)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hB : IsCompact B) (hWB : W ⊆ B)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (hY₀ : ContDiffOn ℝ ∞ Y₀ V)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (slice : TransportSliceCoordinates n)
    {gap : ℝ} (hgap : 0 < gap)
    (hgap₀ : ∀ p ∈ K, gap ≤ transportAbsoluteJacobian slice Y₀ p) :
    ∃ δ > (0 : ℝ), ∀ Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1),
      ContDiffOn ℝ ∞ Y V → cNorm L 2 (Y - Y₀) < δ →
      (∀ p ∈ K, gap / 2 ≤ transportAbsoluteJacobian slice Y p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice Y) (interior K) := by
  have hg₀ := transportAveragedGradient_contDiffOn hW hV hIt hIIt hsegT hY₀
  let D₀ := transportSliceDifferential slice Y₀
  have hD₀ := transportSliceDifferential_contDiffOn slice Y₀ hW hg₀
  have hD₀at : ∀ p ∈ K, ContDiffAt ℝ 0 D₀ p := fun p hp ↦
    (hD₀.contDiffAt (hW.mem_nhds (hKW hp))).of_le (by simp)
  let M := cNorm K 0 D₀ + 1
  let S := closedBall (0 : Euclidean n →L[ℝ] Euclidean n) M
  have hS : IsCompact S := isCompact_closedBall _ _
  have hrange₀ : MapsTo D₀ K S := by
    intro p hp
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hD₀at hp (le_refl 0)
    rw [norm_iteratedFDeriv_zero] at hh
    exact mem_closedBall_zero_iff.mpr (hh.trans (by dsimp [M]; linarith))
  obtain ⟨C, hC, hdet⟩ := ForwardJacobian.exists_compact_comp_sub_le hK hS
    (fun _ _ ↦ NormalComparison.contDiff_normalJacobianDet.contDiffAt)
    0 hD₀at hrange₀
  obtain ⟨F, hF, hforward⟩ := exists_transportForward_sub_le
    hKW hW hB hWB hV hL hLV hIt hIIt hsegT hseg A 1
  let E := ‖transportDifferentialRestriction slice‖ * F
  have hE : 0 ≤ E := mul_nonneg (norm_nonneg (transportDifferentialRestriction slice)) hF.le
  let Ctot := 1 + E + C * E
  have hCtot : 0 < Ctot := by dsimp [Ctot]; positivity
  refine ⟨min 1 (gap / 2) / Ctot, div_pos (lt_min zero_lt_one (half_pos hgap)) hCtot, ?_⟩
  intro Y hY hnear
  let D := transportSliceDifferential slice Y
  have hg := transportAveragedGradient_contDiffOn hW hV hIt hIIt hsegT hY
  have hD := transportSliceDifferential_contDiffOn slice Y hW hg
  have hDat : ∀ p ∈ K, ContDiffAt ℝ 0 D p := fun p hp ↦
    (hD.contDiffAt (hW.mem_nhds (hKW hp))).of_le (by simp)
  let d := cNorm L 2 (Y - Y₀)
  have hd : 0 ≤ d := cNorm_nonneg ..
  have htotal : Ctot * d < min 1 (gap / 2) := by
    have hh := (lt_div_iff₀ hCtot).mp hnear
    simpa only [mul_comm] using hh
  have hdiff : cNorm K 0 (D - D₀) ≤ E * d := by
    have hh := cNorm_transportSliceDifferential_sub_le slice hK hW hKW hg hg₀ 0
    simp only [Nat.cast_one, zero_add, one_mul] at hh
    calc
      _ ≤ ‖transportDifferentialRestriction slice‖ *
          cNorm K 1 (transportAveragedGradient Y - transportAveragedGradient Y₀) := hh
      _ ≤ ‖transportDifferentialRestriction slice‖ * (F * d) :=
        mul_le_mul_of_nonneg_left (hforward Y Y₀ hY hY₀).1
          (norm_nonneg (transportDifferentialRestriction slice))
      _ = E * d := by dsimp only [E]; rw [mul_assoc]
  have hsmall : cNorm K 0 (D - D₀) ≤ 1 := hdiff.trans
    ((mul_le_mul_of_nonneg_right (show E ≤ Ctot by
      dsimp [Ctot]; linarith only [mul_nonneg hC.le hE]) hd).trans
      (htotal.le.trans (min_le_left _ _)))
  have hrange : MapsTo D K S := by
    intro p hp
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun p hp ↦ (hDat p hp).sub (hD₀at p hp)) hp (le_refl 0)
    have h₀ := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hD₀at hp (le_refl 0)
    simp only [norm_iteratedFDeriv_zero] at hh h₀
    change ‖D p - D₀ p‖ ≤ cNorm K 0 (D - D₀) at hh
    apply mem_closedBall_zero_iff.mpr
    have ht := norm_le_norm_sub_add (D p) (D₀ p)
    dsimp only [M]
    linarith only [hh, h₀, ht, hsmall]
  have hdetdiff := hdet D hDat hrange hsmall
  have hdetat : ∀ p ∈ K, ContDiffAt ℝ 0
      ((fun p ↦ (D p).det) - (fun p ↦ (D₀ p).det)) p := fun p hp ↦
    ((NormalComparison.contDiff_normalJacobianDet.contDiffAt.of_le (by simp)).comp p
      (hDat p hp)).sub
      ((NormalComparison.contDiff_normalJacobianDet.contDiffAt.of_le (by simp)).comp p
        (hD₀at p hp))
  have hbound (p) (hp : p ∈ K) : gap / 2 ≤ transportAbsoluteJacobian slice Y p := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hdetat hp (le_refl 0)
    simp only [norm_iteratedFDeriv_zero, Pi.sub_apply] at hh
    have hcontrol : C * cNorm K 0 (D - D₀) < gap / 2 :=
      (mul_le_mul_of_nonneg_left hdiff hC.le).trans_lt
        ((show C * (E * d) ≤ Ctot * d by
          have hCE : C * E ≤ Ctot := by dsimp [Ctot]; linarith only [hE]
          exact (mul_assoc C E d).symm.trans_le (mul_le_mul_of_nonneg_right hCE hd)).trans_lt
            (htotal.trans_le (min_le_right _ _)))
    have habs : |(D₀ p).det| ≤ |(D p).det| + |(D p).det - (D₀ p).det| := by
      simpa only [Real.norm_eq_abs] using norm_le_norm_add_norm_sub (D p).det (D₀ p).det
    have h₀ := hgap₀ p hp
    change gap ≤ |(D₀ p).det| at h₀
    change gap / 2 ≤ |(D p).det|
    have hhd : |(D p).det - (D₀ p).det| < gap / 2 :=
      hh.trans (hdetdiff) |>.trans_lt hcontrol
    linarith only [hhd, habs, h₀]
  refine ⟨hbound, ?_⟩
  apply (NormalComparison.contDiff_normalJacobianDet.comp_contDiffOn
    (hD.mono (interior_subset.trans hKW))).abs
  intro p hp
  exact abs_pos.mp ((half_pos hgap).trans_le (hbound p (interior_subset hp)))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
