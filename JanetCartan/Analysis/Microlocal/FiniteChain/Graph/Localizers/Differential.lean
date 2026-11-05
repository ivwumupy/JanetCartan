module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic

/-!
# The packed joint derivative

Identification of the derivative used by the joint-kernel integration by parts
with all five equations of `app:ch_regular:eq:joint-stationary`. Differentiability
is required only at the actual graph point, hence on its conic chart.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiniteChain.Graph
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem fderiv_jointPhase_forward_apply_raw (φ : E → E → ℝ) (x y : E) (p v : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    fderiv ℝ (jointPhase false φ x y) p v =
      fderiv ℝ (Function.uncurry φ) (p.1.1, p.2.1) (v.1.1, v.2.1) -
      (inner ℝ p.1.2 v.2.1 + inner ℝ v.1.2 p.2.1) +
      (inner ℝ (p.1.2-y) v.2.2.1 + inner ℝ v.1.2 p.2.2.1) +
      (inner ℝ (x-p.1.1) v.2.2.2 - inner ℝ v.1.1 p.2.2.2) := by
  let U : JointVariables E →L[ℝ] E := (fst ℝ E E).comp (fst ℝ (E × E) (E × E × E))
  let Z : JointVariables E →L[ℝ] E := (snd ℝ E E).comp (fst ℝ (E × E) (E × E × E))
  let X : JointVariables E →L[ℝ] E := (fst ℝ E (E × E)).comp (snd ℝ (E × E) (E × E × E))
  let H : JointVariables E →L[ℝ] E := (fst ℝ E E).comp ((snd ℝ E (E × E)).comp (snd ℝ (E × E) (E × E × E)))
  let O : JointVariables E →L[ℝ] E := (snd ℝ E E).comp ((snd ℝ E (E × E)).comp (snd ℝ (E × E) (E × E × E)))
  have h := (((hφ.hasFDerivAt.comp p (U.hasFDerivAt.prodMk X.hasFDerivAt)).sub
    (Z.hasFDerivAt.inner ℝ X.hasFDerivAt)).add
    ((Z.hasFDerivAt.sub_const y).inner ℝ H.hasFDerivAt)).add
    ((U.hasFDerivAt.const_sub x).inner ℝ O.hasFDerivAt)
  change fderiv ℝ (fun q : JointVariables E => φ q.1.1 q.2.1 - inner ℝ q.1.2 q.2.1 +
    inner ℝ (q.1.2-y) q.2.2.1 + inner ℝ (x-q.1.1) q.2.2.2) p v = _
  simpa [U, Z, X, H, O, fderivInnerCLM_apply, Function.comp_def, Function.uncurry_def,
    Pi.add_def, Pi.sub_def, sub_eq_add_neg] using congrArg (fun L : JointVariables E →L[ℝ] ℝ => L v) h.fderiv
private theorem fderiv_jointPhase_reverse_apply_raw (φ : E → E → ℝ) (x y : E) (p v : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    fderiv ℝ (jointPhase true φ x y) p v =
      (inner ℝ p.1.2 v.2.1 + inner ℝ v.1.2 p.2.1) -
      fderiv ℝ (Function.uncurry φ) (p.1.1, p.2.1) (v.1.1, v.2.1) +
      (inner ℝ (p.1.1-y) v.2.2.1 + inner ℝ v.1.1 p.2.2.1) +
      (inner ℝ (x-p.1.2) v.2.2.2 - inner ℝ v.1.2 p.2.2.2) := by
  let U : JointVariables E →L[ℝ] E := (fst ℝ E E).comp (fst ℝ (E × E) (E × E × E))
  let Z : JointVariables E →L[ℝ] E := (snd ℝ E E).comp (fst ℝ (E × E) (E × E × E))
  let X : JointVariables E →L[ℝ] E := (fst ℝ E (E × E)).comp (snd ℝ (E × E) (E × E × E))
  let H : JointVariables E →L[ℝ] E := (fst ℝ E E).comp ((snd ℝ E (E × E)).comp (snd ℝ (E × E) (E × E × E)))
  let O : JointVariables E →L[ℝ] E := (snd ℝ E E).comp ((snd ℝ E (E × E)).comp (snd ℝ (E × E) (E × E × E)))
  have h := (((Z.hasFDerivAt.inner ℝ X.hasFDerivAt).sub
    (hφ.hasFDerivAt.comp p (U.hasFDerivAt.prodMk X.hasFDerivAt))).add
    ((U.hasFDerivAt.sub_const y).inner ℝ H.hasFDerivAt)).add
    ((Z.hasFDerivAt.const_sub x).inner ℝ O.hasFDerivAt)
  change fderiv ℝ (fun q : JointVariables E => inner ℝ q.1.2 q.2.1 - φ q.1.1 q.2.1 +
    inner ℝ (q.1.1-y) q.2.2.1 + inner ℝ (x-q.1.2) q.2.2.2) p v = _
  simpa [U, Z, X, H, O, fderivInnerCLM_apply, Function.comp_def, Function.uncurry_def,
    Pi.add_def, Pi.sub_def, sub_eq_add_neg] using congrArg (fun L : JointVariables E →L[ℝ] ℝ => L v) h.fderiv

private theorem fderiv_uncurry_apply_split (φ : E → E → ℝ) (u ξ du dξ : E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (u, ξ)) :
    fderiv ℝ (Function.uncurry φ) (u, ξ) (du, dξ) =
      fderiv ℝ (fun v => φ v ξ) u du + fderiv ℝ (φ u) ξ dξ := by
  have hu := (hφ.hasFDerivAt.comp u (hasFDerivAt_prodMk_left (𝕜 := ℝ) u ξ)).fderiv
  have hξ := (hφ.hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right (𝕜 := ℝ) u ξ)).fderiv
  have he : (du, dξ) = (du, (0 : E)) + (0, dξ) := by simp
  rw [he, map_add]
  exact congrArg₂ (· + ·) (congrArg (fun L : E →L[ℝ] ℝ => L du) hu.symm)
    (congrArg (fun L : E →L[ℝ] ℝ => L dξ) hξ.symm)


/-- The five forward covectors packed in the actual integration-variable order
(`app:ch_regular:eq:joint-stationary`). -/
def forwardJointDifferential (φ : E → E → ℝ) (x y : E) (p : JointVariables E) :
    JointVariables E →L[ℝ] ℝ :=
  ((fderiv ℝ (fun u => φ u p.2.1) p.1.1 - innerSL ℝ p.2.2.2).coprod
    (innerSL ℝ (p.2.2.1 - p.2.1))).coprod
    ((fderiv ℝ (φ p.1.1) p.2.1 - innerSL ℝ p.1.2).coprod
      ((innerSL ℝ (p.1.2-y)).coprod (innerSL ℝ (x-p.1.1))))

/-- The five literal reverse covectors, including `u-y` and `x-z`
(`app:ch_regular:lem:finite-chain`). -/
def reverseJointDifferential (φ : E → E → ℝ) (x y : E) (p : JointVariables E) :
    JointVariables E →L[ℝ] ℝ :=
  ((innerSL ℝ p.2.2.1 - fderiv ℝ (fun u => φ u p.2.1) p.1.1).coprod
    (innerSL ℝ (p.2.1 - p.2.2.2))).coprod
    ((innerSL ℝ p.1.2 - fderiv ℝ (φ p.1.1) p.2.1).coprod
      ((innerSL ℝ (p.1.1-y)).coprod (innerSL ℝ (x-p.1.2))))

/-- The forward residual is exactly the packed Fréchet derivative, not just
an algebraic stationary test (`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_jointPhase_forward (φ : E → E → ℝ) (x y : E) (p : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    fderiv ℝ (jointPhase false φ x y) p = forwardJointDifferential φ x y p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_jointPhase_forward_apply_raw φ x y p v hφ,
    fderiv_uncurry_apply_split φ _ _ _ _ hφ]
  simp only [forwardJointDifferential, coprod_apply, sub_apply, innerSL_apply_apply,
    inner_sub_left]
  rw [real_inner_comm v.1.2 p.2.1, real_inner_comm v.1.2 p.2.2.1,
    real_inner_comm v.1.1 p.2.2.2]
  ring

/-- The same identification for the literal inverse graph phase
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_jointPhase_reverse (φ : E → E → ℝ) (x y : E) (p : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    fderiv ℝ (jointPhase true φ x y) p = reverseJointDifferential φ x y p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_jointPhase_reverse_apply_raw φ x y p v hφ,
    fderiv_uncurry_apply_split φ _ _ _ _ hφ]
  simp only [reverseJointDifferential, coprod_apply, sub_apply, innerSL_apply_apply,
    inner_sub_left]
  rw [real_inner_comm v.1.2 p.2.1, real_inner_comm v.1.1 p.2.2.1,
    real_inner_comm v.1.2 p.2.2.2]
  ring

private theorem coprod_eq_zero_iff {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : A →L[ℝ] ℝ) (g : B →L[ℝ] ℝ) :
    f.coprod g = 0 ↔ f = 0 ∧ g = 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun L => L.comp (inl ℝ A B)) h,
      by simpa using congrArg (fun L => L.comp (inr ℝ A B)) h⟩
  · rintro ⟨rfl, rfl⟩
    ext <;> simp

private theorem innerSL_eq_zero_iff (v : E) : innerSL ℝ v = 0 ↔ v = 0 := by
  rw [← norm_eq_zero, innerSL_apply_norm, norm_eq_zero]

/-- Vanishing of the actual packed forward derivative is equivalent to all
five actual partial derivatives vanishing (`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_jointPhase_forward_eq_zero_iff (φ : E → E → ℝ) (x y : E)
    (p : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    fderiv ℝ (jointPhase false φ x y) p = 0 ↔
      ForwardStationary φ x y p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 := by
  have hu := (hφ.hasFDerivAt.comp p.1.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1.1 p.2.1)).differentiableAt
  have hξ := (hφ.hasFDerivAt.comp p.2.1
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1.1 p.2.1)).differentiableAt
  rw [fderiv_jointPhase_forward φ x y p hφ,
    forwardStationary_iff φ x y _ _ _ _ _ hu hξ]
  simp only [forwardJointDifferential, coprod_eq_zero_iff, innerSL_eq_zero_iff,
    sub_eq_zero]
  tauto

/-- The packed reverse derivative retains the exchanged base equations
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_jointPhase_reverse_eq_zero_iff (φ : E → E → ℝ) (x y : E)
    (p : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    fderiv ℝ (jointPhase true φ x y) p = 0 ↔
      ReverseStationary φ x y p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 := by
  have hu := (hφ.hasFDerivAt.comp p.1.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1.1 p.2.1)).differentiableAt
  have hξ := (hφ.hasFDerivAt.comp p.2.1
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1.1 p.2.1)).differentiableAt
  rw [fderiv_jointPhase_reverse φ x y p hφ,
    reverseStationary_iff φ x y _ _ _ _ _ hu hξ]
  simp only [reverseJointDifferential, coprod_eq_zero_iff, innerSL_eq_zero_iff,
    sub_eq_zero]
  tauto

private theorem norm_coprod_left_le {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : A →L[ℝ] ℝ) (g : B →L[ℝ] ℝ) : ‖f‖ ≤ ‖f.coprod g‖ := by
  apply f.opNorm_le_bound (norm_nonneg _)
  intro v
  simpa using (f.coprod g).le_opNorm (v, 0)

private theorem norm_coprod_right_le {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : A →L[ℝ] ℝ) (g : B →L[ℝ] ℝ) : ‖g‖ ≤ ‖f.coprod g‖ := by
  apply g.opNorm_le_bound (norm_nonneg _)
  intro v
  simpa using (f.coprod g).le_opNorm (0, v)

omit [InnerProductSpace ℝ E] in
private theorem five_norms_le [NormedSpace ℝ E] (a b c d e : E →L[ℝ] ℝ) :
    let D := (a.coprod b).coprod (c.coprod (d.coprod e))
    ‖a‖ ≤ ‖D‖ ∧ ‖b‖ ≤ ‖D‖ ∧ ‖c‖ ≤ ‖D‖ ∧ ‖d‖ ≤ ‖D‖ ∧ ‖e‖ ≤ ‖D‖ := by
  have hab := norm_coprod_left_le (a.coprod b) (c.coprod (d.coprod e))
  have hcde := norm_coprod_right_le (a.coprod b) (c.coprod (d.coprod e))
  have hde := (norm_coprod_right_le c (d.coprod e)).trans hcde
  exact ⟨(norm_coprod_left_le a b).trans hab, (norm_coprod_right_le a b).trans hab,
    (norm_coprod_left_le c (d.coprod e)).trans hcde,
    (norm_coprod_left_le d e).trans hde, (norm_coprod_right_le d e).trans hde⟩

/-- Every forward stationary equation is quantitatively controlled by the
actual packed derivative (`app:ch_regular:eq:joint-stationary`). -/
theorem forward_joint_derivative_bounds (φ : E → E → ℝ) (x y : E)
    (p : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    let G := ‖fderiv ℝ (jointPhase false φ x y) p‖
    ‖fderiv ℝ (fun u => φ u p.2.1) p.1.1 - innerSL ℝ p.2.2.2‖ ≤ G ∧
    ‖p.2.2.1 - p.2.1‖ ≤ G ∧
    ‖fderiv ℝ (φ p.1.1) p.2.1 - innerSL ℝ p.1.2‖ ≤ G ∧
    ‖p.1.2-y‖ ≤ G ∧ ‖x-p.1.1‖ ≤ G := by
  rw [fderiv_jointPhase_forward φ x y p hφ]
  simpa only [forwardJointDifferential, innerSL_apply_norm] using
    five_norms_le (fderiv ℝ (fun u => φ u p.2.1) p.1.1 - innerSL ℝ p.2.2.2)
      (innerSL ℝ (p.2.2.1-p.2.1)) (fderiv ℝ (φ p.1.1) p.2.1 - innerSL ℝ p.1.2)
      (innerSL ℝ (p.1.2-y)) (innerSL ℝ (x-p.1.1))

/-- Every literal reverse equation is controlled by the actual packed
reverse derivative (`app:ch_regular:lem:finite-chain`). -/
theorem reverse_joint_derivative_bounds (φ : E → E → ℝ) (x y : E)
    (p : JointVariables E)
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1)) :
    let G := ‖fderiv ℝ (jointPhase true φ x y) p‖
    ‖innerSL ℝ p.2.2.1 - fderiv ℝ (fun u => φ u p.2.1) p.1.1‖ ≤ G ∧
    ‖p.2.1 - p.2.2.2‖ ≤ G ∧
    ‖innerSL ℝ p.1.2 - fderiv ℝ (φ p.1.1) p.2.1‖ ≤ G ∧
    ‖p.1.1-y‖ ≤ G ∧ ‖x-p.1.2‖ ≤ G := by
  rw [fderiv_jointPhase_reverse φ x y p hφ]
  simpa only [reverseJointDifferential, innerSL_apply_norm] using
    five_norms_le (innerSL ℝ p.2.2.1 - fderiv ℝ (fun u => φ u p.2.1) p.1.1)
      (innerSL ℝ (p.2.1-p.2.2.2)) (innerSL ℝ p.1.2 - fderiv ℝ (φ p.1.1) p.2.1)
      (innerSL ℝ (p.1.1-y)) (innerSL ℝ (x-p.1.2))

end JanetCartan.FiniteChain.Graph
