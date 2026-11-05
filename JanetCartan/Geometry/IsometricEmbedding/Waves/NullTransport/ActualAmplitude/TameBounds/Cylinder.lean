module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.BallImage

/-!
# Characteristic exponentials on the retained cylinder

The producer bounds the forward and inverse maps on a time--label cylinder,
not an isotropic ball. A fixed dilation of time identifies that cylinder with
a ball in the original product norm. This proves the literal exponential
estimate on that same cylinder at every order (`app:ch_waves:eq:joint-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed dilation of time, leaving all physical and carrier labels unchanged
(`app:ch_waves:eq:joint-tame`). -/
def timeDilation (l : ℝ) (hl : l ≠ 0) : (ℝ × E) ≃L[ℝ] ℝ × E :=
  (LinearEquiv.smulOfNeZero ℝ ℝ l hl).toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ E)

/-- The literal coordinate formula for the fixed time dilation
(`app:ch_waves:eq:joint-tame`). -/
@[simp] theorem timeDilation_apply (l : ℝ) (hl : l ≠ 0) (q : ℝ × E) :
    timeDilation l hl q = (l * q.1, q.2) := rfl

/-- A product-norm ball becomes the precise closed cylinder used in the
coefficient/flow handoff (`app:ch_waves:eq:joint-tame`). -/
theorem timeDilation_image_closedBall (p : E) {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) :
    timeDilation (τ / σ) (div_pos hτ hσ).ne' '' closedBall (0, p) σ =
      Icc (-τ) τ ×ˢ closedBall p σ := by
  ext q
  rw [show q ∈ timeDilation (τ / σ) (div_pos hτ hσ).ne' '' closedBall (0, p) σ ↔
      (timeDilation (τ / σ) (div_pos hτ hσ).ne').symm q ∈ closedBall (0, p) σ from
    Set.mem_image_equiv (f := (timeDilation (τ / σ) (div_pos hτ hσ).ne').toEquiv)]
  have hinv : (timeDilation (E := E) (τ / σ) (div_pos hτ hσ).ne').symm q =
      (q.1 / (τ / σ), q.2) := by
    apply (timeDilation (E := E) (τ / σ) (div_pos hτ hσ).ne').injective
    simp only [ContinuousLinearEquiv.apply_symm_apply, timeDilation_apply]
    ext <;> dsimp
    field_simp
  rw [hinv]
  simp only [mem_closedBall, Prod.dist_eq, Real.dist_eq, sub_zero, max_le_iff,
    mem_prod, mem_Icc, abs_div, abs_of_pos (div_pos hτ hσ)]
  rw [div_le_iff₀ (div_pos hτ hσ)]
  have he : σ * (τ / σ) = τ := by field_simp
  rw [he, abs_le]

/-- The literal characteristic factor respects time dilation, with the
Jacobian absorbed in the coefficient (`app:ch_waves:eq:joint-tame`). -/
theorem transportFactor_timeDilation (c : ℝ × E → ℝ) (l : ℝ) (hl : l ≠ 0)
    (q : ℝ × E) :
    transportFactor (fun s ↦ c (s, (timeDilation l hl q).2)) 0
        (timeDilation l hl q).1 =
      transportFactor (fun s ↦ l * c (timeDilation l hl (s, q.2))) 0 q.1 := by
  simp only [transportFactor, timeDilation_apply, intervalIntegral.integral_const_mul]
  congr 2
  simpa only [mul_zero, zero_add, add_zero, smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_add (fun s ↦ c (s, q.2))
      (a := 0) (b := q.1) l 0).symm

variable [FiniteDimensional ℝ E]

/-- Smoothness near the entire retained cylinder, including its boundary,
is derived from the actual parameter integral (`app:ch_waves:thm:leading`). -/
theorem exists_transportFactor_smooth_near_cylinder (p : E) {τ σ : ℝ}
    (hτ : 0 < τ) (hσ : 0 < σ) {U : Set (ℝ × E)} (hU : IsOpen U)
    (hJU : Icc (-τ) τ ×ˢ closedBall p σ ⊆ U)
    {c : ℝ × E → ℝ} (hc : ContDiffOn ℝ ∞ c U) :
    ∃ W : Set (ℝ × E), IsOpen W ∧ Icc (-τ) τ ×ˢ closedBall p σ ⊆ W ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, q.2)) 0 q.1) W := by
  let e := timeDilation (E := E) (τ / σ) (div_pos hτ hσ).ne'
  have he : e '' closedBall (0, p) σ = Icc (-τ) τ ×ˢ closedBall p σ :=
    timeDilation_image_closedBall p hτ hσ
  have hball : closedBall (0, p) σ ⊆ e ⁻¹' U := by
    intro x hx
    apply hJU
    rw [← he]
    exact mem_image_of_mem e hx
  have hc' : ContDiffOn ℝ ∞ (fun q ↦ (τ / σ) * c (e q)) (e ⁻¹' U) :=
    contDiffOn_const.mul (hc.comp e.contDiff.contDiffOn (fun _ hx ↦ hx))
  obtain ⟨W, hW, hKW, hi⟩ := exists_timeIntegral_smooth_near_ball p hσ
    (hU.preimage e.continuous) hball hc'
  refine ⟨e.symm ⁻¹' W, hW.preimage e.symm.continuous, ?_, ?_⟩
  · rw [← he]
    rintro _ ⟨q, hq, rfl⟩
    simpa using hKW hq
  · have hexp := (Real.contDiff_exp.comp_contDiffOn hi.neg).comp
      e.symm.contDiff.contDiffOn (fun _ hx ↦ hx)
    apply hexp.congr
    intro q _
    have hh := transportFactor_timeDilation c (τ / σ) (div_pos hτ hσ).ne' (e.symm q)
    simpa only [ContinuousLinearEquiv.apply_symm_apply, e, transportFactor, Function.comp_apply] using hh

/-- One high norm for the literal exponential on the fixed cylinder. The low
budget is on the coefficient alone, and constants precede the coefficient,
its smoothness neighborhood and every high norm (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_transportFactor_le_cylinder (p : E) {τ σ : ℝ}
    (hτ : 0 < τ) (hσ : 0 < σ) (m : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (ℝ × E)), IsOpen U →
      Icc (-τ) τ ×ˢ closedBall p σ ⊆ U → ∀ c : ℝ × E → ℝ,
      ContDiffOn ℝ ∞ c U → cNorm (Icc (-τ) τ ×ˢ closedBall p σ) 0 c ≤ M →
      cNorm (Icc (-τ) τ ×ˢ closedBall p σ) m
          (fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, q.2)) 0 q.1) ≤
        C * (1 + cNorm (Icc (-τ) τ ×ˢ closedBall p σ) m c) := by
  let e := timeDilation (E := E) (τ / σ) (div_pos hτ hσ).ne'
  let A := fun j ↦ ‖τ / σ‖ * linearNormCost e.toContinuousLinearMap j
  let B := linearNormCost e.symm.toContinuousLinearMap m
  have hA j : 0 ≤ A j := mul_nonneg (norm_nonneg _) (linearNormCost_pos _ _).le
  have hB : 0 < B := linearNormCost_pos _ _
  obtain ⟨C, hC, hb⟩ := exists_cNorm_transportFactor_le_same_ball p hσ m (A 0 * M)
  refine ⟨B * C * (1 + A m), mul_pos (mul_pos hB hC) (by linarith [hA m]), ?_⟩
  intro U hU hJU c hc hlow
  let J := Icc (-τ) τ ×ˢ closedBall p σ
  have he : e '' closedBall (0, p) σ = J := timeDilation_image_closedBall p hτ hσ
  have hm : MapsTo e (closedBall (0, p) σ) J := by
    intro q hq
    rw [← he]
    exact mem_image_of_mem e hq
  have hball : closedBall (0, p) σ ⊆ e ⁻¹' U := fun _ hx ↦ hJU (hm hx)
  let c' := fun q ↦ (τ / σ) * c (e q)
  have hc' : ContDiffOn ℝ ∞ c' (e ⁻¹' U) :=
    contDiffOn_const.mul (hc.comp e.contDiff.contDiffOn (fun _ hx ↦ hx))
  have hn (j) : cNorm (closedBall (0, p) σ) j c' ≤ A j * cNorm J j c := by
    have heq : c' = (τ / σ) • (c ∘ e) := rfl
    rw [heq, cNorm_smul_of_contDiffAt _ (fun x hx ↦
      ((hc.contDiffAt (hU.mem_nhds (hball hx))).comp x e.contDiff.contDiffAt).of_le (by simp))]
    exact (mul_le_mul_of_nonneg_left (cNorm_comp_linear_le e.toContinuousLinearMap
      (isCompact_Icc.prod (isCompact_closedBall p σ)) hU hJU hc hm j)
      (norm_nonneg _)).trans_eq (by dsimp [A]; ring)
  have hh := hb _ (hU.preimage e.continuous) hball c' hc'
    ((hn 0).trans (mul_le_mul_of_nonneg_left hlow (hA 0)))
  obtain ⟨W, hW, hJW, hf⟩ := exists_transportFactor_smooth_near_cylinder p hτ hσ hU hJU hc
  have hr := cNorm_image_le_pullback e (0, p) σ hW (he ▸ hJW) hf m
  rw [he] at hr
  have heq : (fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, q.2)) 0 q.1) ∘ e =
      (fun q : ℝ × E ↦ transportFactor (fun s ↦ c' (s, q.2)) 0 q.1) :=
    funext (transportFactor_timeDilation c _ _)
  rw [heq] at hr
  apply (hr.trans (mul_le_mul_of_nonneg_left hh hB.le)).trans
  have hi : 1 + cNorm (closedBall (0, p) σ) m c' ≤ (1 + A m) * (1 + cNorm J m c) := by
    nlinarith [hn m, hA m, cNorm_nonneg J m c]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (mul_nonneg hB.le hC.le)

end JanetCartan.NullTransport.AmplitudeTame
