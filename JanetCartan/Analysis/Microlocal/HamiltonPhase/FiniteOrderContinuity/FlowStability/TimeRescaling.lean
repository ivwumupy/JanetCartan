module

public import JanetCartan.Analysis.ODE.TimeRescaling.Norms

/-!
# Difference estimates for autonomous time augmentation

The time-augmentation step in the finite-order flow continuity assertion of
`app:lem:common-hamilton-phase`. The field estimate is homogeneous in the field
difference, with no additive baseline and no derivative loss. Recovery of the
joint flow difference uses only the prescribed local smoothness and buffers.
Both estimates are inputs to the parent flow-continuity assembly; neither
assumes a spatial stability estimate.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Set Metric

namespace JanetCartan.TimeRescaling

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cNorm_lift_fst_zero_le [FiniteDimensional ℝ E]
    (x₀ : E) (R : ℝ) (m : ℕ) {f : E → E} (hf : ContDiff ℝ m f) :
    cNorm (closedBall (x₀, (0 : ℝ)) R) m (fun x : E × ℝ ↦ (f x.1, (0 : ℝ))) ≤
      cNorm (closedBall x₀ R) m f := by
  let L := ContinuousLinearMap.fst ℝ E ℝ
  change _ ≤ ∑ j ∈ Finset.range (m + 1),
    sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' closedBall x₀ R)
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg (closedBall x₀ R) j f)
  intro j hj x hx
  change ‖iteratedFDeriv ℝ j ((LinearIsometry.inl ℝ E ℝ) ∘ (f ∘ L)) x‖ ≤ _
  rw [(LinearIsometry.inl ℝ E ℝ).norm_iteratedFDeriv_comp_left
    (hf.comp L.contDiff).contDiffAt (by exact_mod_cast hj),
    L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  apply ((iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow : ‖L‖ ^ j ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg L) (ContinuousLinearMap.norm_fst_le ℝ E ℝ) j
  apply (mul_le_of_le_one_right (norm_nonneg _) hpow).trans
  apply le_csSup (bddAbove_norm_iteratedFDeriv (isCompact_closedBall x₀ R) hf hj)
  apply mem_image_of_mem
  exact (show dist x.1 x₀ ≤ dist x (x₀, 0) by
    rw [Prod.dist_eq]; exact le_max_left _ _).trans hx

/-- `app:lem:common-hamilton-phase`: time augmentation is uniformly bounded
on field differences in the same finite-order seminorm. The constant is fixed
before both fields and their common open neighborhood; there is no additive
constant and no perturbation derivative above `m`. This supplies the field
perturbation input for the parent's augmented spatial-flow comparison. -/
theorem exists_cNorm_field_sub_bound [FiniteDimensional ℝ E]
    (x₀ : E) {R : ℝ} (hR : 0 < R) (l c : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V V₀ : E → E) (W : Set E), IsOpen W →
      closedBall x₀ R ⊆ W → ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ V₀ W →
      cNorm (closedBall (x₀, 0) R) m (field l c V - field l c V₀) ≤
        C * cNorm (closedBall x₀ R) m (V - V₀) := by
  let s := closedBall (x₀, (0 : ℝ)) R
  let a : E × ℝ → ℝ := fun x ↦ l / c * x.2
  let A := (2 : ℝ) ^ m * cNorm s m a
  have hA : 0 ≤ A := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  refine ⟨1 + A, by positivity, ?_⟩
  intro V V₀ W hW hball hV hV₀
  obtain ⟨f, hf, _, _, hfg⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall x₀ hR hW hball
      (hV.sub hV₀)
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq hfg m
  have heq : cNorm s m (field l c f) =
      cNorm s m (field l c V - field l c V₀) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    have hx₁ : x.1 ∈ closedBall x₀ R :=
      (show dist x.1 x₀ ≤ dist x (x₀, 0) by
        rw [Prod.dist_eq]; exact le_max_left _ _).trans hx
    filter_upwards [(hfg x.1 hx₁).comp_tendsto continuous_fst.continuousAt] with y hy
    change f y.1 = V y.1 - V₀ y.1 at hy
    simp only [Pi.sub_apply, field, hy, smul_sub, Prod.mk_sub_mk, sub_self]
  have hf' : ContDiff ℝ m f := hf.of_le (by simp)
  have ha : ContDiff ℝ m a := contDiff_const.mul contDiff_snd
  have hprod := cNorm_smul_le (isCompact_closedBall (x₀, (0 : ℝ)) R)
    ha ((hf'.comp contDiff_fst).prodMk (contDiff_const (c := (0 : ℝ))))
  have hb : cNorm s m (field l c f) ≤ A * cNorm (closedBall x₀ R) m f := by
    calc
      _ ≤ A * cNorm s m (fun x : E × ℝ ↦ (f x.1, (0 : ℝ))) := by
        change cNorm s m (fun x ↦ ((l / c * x.2) • f x.1, (0 : ℝ))) ≤ _
        simpa only [s, a, A, Function.comp_apply, Prod.smul_mk, smul_zero] using hprod
      _ ≤ _ := mul_le_mul_of_nonneg_left (cNorm_lift_fst_zero_le x₀ R m hf') hA
  rw [heq, hnorm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
    (cNorm_nonneg (closedBall x₀ R) m (V - V₀)))

/-- `app:lem:common-hamilton-phase`: recover joint flow differences from the
augmented flows at auxiliary time one. The stationary extra coordinate cancels,
and affine pullback costs only `(max 1 |l⁻¹|)^m`, with no derivative loss.
This transfers the parent's spatial continuity estimate to the joint cylinder. -/
theorem cNorm_flow_sub_recover_le [FiniteDimensional ℝ P]
    (z : P) {ρ Rp q l : ℝ} (hρ : 0 < ρ) (hρRp : ρ < Rp) (hq : 1 < q)
    (hl : 0 < l) (t₀ c : ℝ) (m : ℕ) {Φ Φ₀ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ
      (ball z Rp ×ˢ Ioo (t₀ - l * q * Rp) (t₀ + l * q * Rp)))
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀
      (ball z Rp ×ˢ Ioo (t₀ - l * q * Rp) (t₀ + l * q * Rp))) :
    cNorm (closedBall z ρ ×ˢ Icc (t₀ - l * ρ) (t₀ + l * ρ)) m (Φ - Φ₀) ≤
      (max 1 |l⁻¹|) ^ m * cNorm (closedBall (z, 0) ρ) m
        (fun p ↦ flow t₀ l c Φ (p, 1) - flow t₀ l c Φ₀ (p, 1)) := by
  have hs : ∀ Ψ : P × ℝ → E, ContDiffOn ℝ ∞ Ψ
      (ball z Rp ×ˢ Ioo (t₀ - l * q * Rp) (t₀ + l * q * Rp)) →
      ContDiffOn ℝ ∞ (fun p ↦ flow t₀ l c Ψ (p, 1)) (ball (z, 0) Rp) := by
    intro Ψ hΨ
    apply (contDiffOn_flow hl (zero_lt_one.trans hq) hΨ).comp
      (contDiffOn_id.prodMk contDiffOn_const)
    intro p hp
    exact ⟨hp, by constructor <;> linarith⟩
  have hb := cNorm_pullback_fst_le z hρ hl t₀ m isOpen_ball
    (closedBall_subset_ball hρRp) ((hs Φ hΦ).sub (hs Φ₀ hΦ₀))
  simpa only [Pi.sub_def, pullback, Prod.fst_sub, flow_recover t₀ c hl.ne' Φ,
    flow_recover t₀ c hl.ne' Φ₀] using hb

end JanetCartan.TimeRescaling
