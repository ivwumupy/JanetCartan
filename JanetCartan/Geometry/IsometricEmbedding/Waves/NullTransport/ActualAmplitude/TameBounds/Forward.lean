module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Domains

/-!
# Coefficient along the constructed forward flow

This is the first varying composition in `app:ch_waves:eq:joint-tame`.
Its low budget is derived from the physical coefficient and forward map,
and its high bound is additive. The physical smoothness hypothesis is exactly
pointwise smoothness on the coefficient ball, as retained by the producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame
open FullPhaseCharts.InverseEstimates

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ X] in
/-- The actual composed coefficient is smooth near the whole closed forward
cylinder; its range is proved using the strict half-radius buffer
(`app:ch_waves:eq:joint-tame`). -/
theorem exists_forwardCoefficient_smooth_near
    (C : X ≃L[ℝ] ℝ × E) (a : X) (p : E) {ρ τ R : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hR : 0 < R) (hτR : τ ≤ R / 16)
    (hcenter : C.symm (0, p) = a)
    (hbuffer : MapsTo C.symm (closedBall (0, p) R) (closedBall a ρ))
    {Φ : ℝ × E → E} {c : X → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)))
    (hc : ∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ c x)
    (hmap : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball p (R / 8)) (Ioo (-τ) τ ×ˢ ball p (R / 4))) :
    ∃ W, IsOpen W ∧ Icc (-τ) τ ×ˢ closedBall p (R / 8) ⊆ W ∧
      ContDiffOn ℝ ∞ (flowTransportCoefficient (c ∘ C.symm) Φ) W := by
  let U := Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)
  let Z := fun q : ℝ × E ↦ C.symm (q.1, Φ q)
  have hZ : ContDiffOn ℝ ∞ Z U := C.symm.contDiff.comp_contDiffOn (contDiffOn_fst.prodMk hΦ)
  have hmaps := forwardGraph_mapsTo_half_ball p hτ hR hτR hΦ hmap
  have hhalf := mapsTo_half_closedBall C.symm.toContinuousLinearMap (0, p) a hcenter hbuffer
  refine ⟨U ∩ Z ⁻¹' ball a ρ, hZ.continuousOn.isOpen_inter_preimage
    (isOpen_Ioo.prod isOpen_ball) isOpen_ball, ?_, ?_⟩
  · intro q hq
    exact ⟨coefficientCylinder_subset_buffer p hτ hR hq,
      closedBall_subset_ball (by linarith) (hhalf (hmaps hq))⟩
  · have hcball : ContDiffOn ℝ ∞ c (ball a ρ) :=
      fun x hx ↦ (hc x (ball_subset_closedBall hx)).contDiffWithinAt
    exact hcball.comp (hZ.mono inter_subset_left) (fun _ hx ↦ hx.2)

/-- One high physical coefficient or forward-flow norm controls the literal
coefficient along the characteristic, with reserve two. The fixed `C¹`
budgets precede all functions (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_forwardCoefficient_bounds
    (C : X ≃L[ℝ] ℝ × E) (a : X) (p : E) {ρ τ R : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hR : 0 < R) (hτR : τ ≤ R / 16)
    (hcenter : C.symm (0, p) = a)
    (hbuffer : MapsTo C.symm (closedBall (0, p) R) (closedBall a ρ))
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧ ∀ (Φ : ℝ × E → E) (c : X → ℝ),
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ c x) →
      MapsTo (fun q ↦ (q.1, Φ q))
        (Ioo (-τ) τ ×ˢ ball p (R / 8)) (Ioo (-τ) τ ×ˢ ball p (R / 4)) →
      cNorm (Icc (-τ) τ ×ˢ closedBall p (R / 8)) 1 Φ ≤ M →
      cNorm (closedBall a ρ) 1 c ≤ M →
      ∀ j, cNorm (Icc (-τ) τ ×ˢ closedBall p (R / 8)) j
          (flowTransportCoefficient (c ∘ C.symm) Φ) ≤
        B j * (1 + cNorm (Icc (-τ) τ ×ˢ closedBall p (R / 8)) (j + 2) Φ +
          cNorm (closedBall a ρ) (j + 2) c) := by
  let J := Icc (-τ) τ ×ˢ closedBall p (R / 8)
  let e := timeDilation (E := E) (τ / (R / 8)) (div_pos hτ (by positivity)).ne'
  have he : e '' closedBall (0, p) (R / 8) = J :=
    timeDilation_image_closedBall p hτ (by positivity)
  let T := fun j ↦ cNorm J j (Prod.fst : ℝ × E → ℝ)
  let D := ‖C.symm.toContinuousLinearMap‖
  have hT j : 0 ≤ T j := cNorm_nonneg _ _ _
  have hD : 0 ≤ D := norm_nonneg _
  choose A hA hb using fun j ↦ exists_cNorm_comp_le_ballImage (G := ℝ)
    e (ContinuousLinearEquiv.refl ℝ X) (0, p) a (by positivity : 0 < R / 8)
    (by positivity : 0 < ρ / 2) j (mul_nonneg hD (add_nonneg (hT 1) hM)) hM
  let B := fun j ↦ A j * (1 + D * T (j + 2) + D)
  refine ⟨B, fun j ↦ mul_pos (hA j) (by nlinarith [hT (j + 2)]), ?_⟩
  intro Φ c hΦ hc hm hΦlow hclow j
  let U := Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)
  let Z := fun q : ℝ × E ↦ C.symm (q.1, Φ q)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_ball
  have hJU : J ⊆ U := coefficientCylinder_subset_buffer p hτ hR
  have hZ : ContDiffOn ℝ ∞ Z U := C.symm.contDiff.comp_contDiffOn (contDiffOn_fst.prodMk hΦ)
  have hzn (i) : cNorm J i Z ≤ D * (T i + cNorm J i Φ) := by
    have hpair := cNorm_prodMk_le_on J (isCompact_Icc.prod (isCompact_closedBall _ _)) i
      (fun _ _ ↦ contDiffAt_fst) (fun x hx ↦ (hΦ.contDiffAt (hU.mem_nhds (hJU hx))).of_le (by simp))
    exact (cNorm_postLinear_le_on (isCompact_Icc.prod (isCompact_closedBall _ _)) i
      C.symm.toContinuousLinearMap (fun x hx ↦
        ((contDiffOn_fst.prodMk hΦ).contDiffAt (hU.mem_nhds (hJU hx))).of_le (by simp))).trans
      (mul_le_mul_of_nonneg_left hpair hD)
  have hcn (i) : cNorm (closedBall a (ρ / 2)) i c ≤ cNorm (closedBall a ρ) i c :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall (by linarith))
      (isCompact_closedBall _ _) (fun x hx ↦ (hc x hx).of_le (by simp))
  have hmaps : MapsTo Z J (closedBall a (ρ / 2)) :=
    (mapsTo_half_closedBall C.symm.toContinuousLinearMap (0, p) a hcenter hbuffer).comp
      (forwardGraph_mapsTo_half_ball p hτ hR hτR hΦ hm)
  have hh := hb j U (ball a ρ) hU isOpen_ball (he ▸ hJU)
    (by simpa using closedBall_subset_ball (by linarith : ρ / 2 < ρ)) Z c hZ
    (fun x hx ↦ (hc x (ball_subset_closedBall hx)).contDiffWithinAt)
    (by simpa only [he, ContinuousLinearEquiv.refl_apply, image_id'] using hmaps)
    (he ▸ (hzn 1).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hΦlow) hD))
    (by simpa using (hcn 1).trans hclow)
  simp only [he, ContinuousLinearEquiv.refl_apply, image_id'] at hh
  apply hh.trans
  have hz := hzn (j + 2)
  have hcc := hcn (j + 2)
  have hf0 := cNorm_nonneg J (j + 2) Φ
  have hc0 := cNorm_nonneg (closedBall a ρ) (j + 2) c
  have hi : 1 + cNorm J (j + 2) Z + cNorm (closedBall a (ρ / 2)) (j + 2) c ≤
      (1 + D * T (j + 2) + D) * (1 + cNorm J (j + 2) Φ + cNorm (closedBall a ρ) (j + 2) c) := by
    nlinarith [hT (j + 2), mul_nonneg hD hc0,
      mul_nonneg (mul_nonneg hD (hT (j + 2))) hf0,
      mul_nonneg (mul_nonneg hD (hT (j + 2))) hc0]
  exact (mul_le_mul_of_nonneg_left hi (hA j).le).trans_eq (by dsimp [B]; ring)

end JanetCartan.NullTransport.AmplitudeTame
