module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.JointFlow
public import JanetCartan.Analysis.ODE.SmoothDependence.FlowRegularity

/-!
# Regularity with the retained initial section

The retained Hamilton flow starts from a smooth section, rather than the
identity map of phase space. For `app:lem:common-hamilton-phase`, the first
variation is the fundamental linear evolution composed with the derivative
of this section. Bootstrapping that equation preserves the given time strip.
The consumer is the original-source forward comparison; its actual section
is the retained root constructed in `RootContinuity`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ P] in
private theorem section_uniform_remainder
    {f : E → E} {W : Set E} {s : Set P} {Φ : P × ℝ → E}
    {I : Set ℝ} {x : P} {K : ℝ≥0}
    (hW : IsOpen W) (hf : ContDiffOn ℝ 1 f W) (hs : s ∈ 𝓝 x)
    (hI : IsCompact I) (hΦ : ContinuousOn (fun t ↦ Φ (x, t)) I)
    (hrange : ∀ t ∈ I, Φ (x, t) ∈ W)
    (hlip : ∀ t ∈ I, LipschitzOnWith K (fun y ↦ Φ (y, t)) s)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ I,
      ‖f (Φ (y, t)) - f (Φ (x, t)) -
        fderiv ℝ f (Φ (x, t)) (Φ (y, t) - Φ (x, t))‖ ≤ ε * ‖y - x‖ := by
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_fderiv_remainder hW hf
    (hI.image_of_continuousOn hΦ) (by rintro _ ⟨t, ht, rfl⟩; exact hrange t ht)
    (div_pos hε hK)
  filter_upwards [hs, ball_mem_nhds x (div_pos hδ hK)] with y hy hxy
  intro t ht
  have hd : ‖Φ (y, t) - Φ (x, t)‖ ≤ (K : ℝ) * ‖y - x‖ := by
    simpa only [dist_eq_norm] using (hlip t ht).dist_le_mul y hy x (mem_of_mem_nhds hs)
  have hd' : ‖Φ (y, t) - Φ (x, t)‖ ≤ ((K : ℝ) + 1) * ‖y - x‖ :=
    hd.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hsmall : dist (Φ (y, t)) (Φ (x, t)) < δ := by
    rw [dist_eq_norm]
    apply hd'.trans_lt
    have hh := (lt_div_iff₀ hK).mp (show ‖y - x‖ < δ / ((K : ℝ) + 1) from
      by simpa only [mem_ball, dist_eq_norm] using hxy)
    simpa only [mul_comm] using hh
  calc
    _ ≤ (ε / ((K : ℝ) + 1)) * ‖Φ (y, t) - Φ (x, t)‖ :=
      hb _ (mem_image_of_mem _ ht) _ hsmall
    _ ≤ (ε / ((K : ℝ) + 1)) * (((K : ℝ) + 1) * ‖y - x‖) := by gcongr
    _ = ε * ‖y - x‖ := by field_simp

private theorem section_flow_hasFDerivAt
    {f : E → E} {W : Set E} {s : Set P} {Φ : P × ℝ → E}
    {σ : P → E} {x : P} {t₀ t : ℝ} {K : ℝ≥0}
    {J : ℝ → E →L[ℝ] E} {Dσ : P →L[ℝ] E}
    (hW : IsOpen W) (hf : ContDiffOn ℝ 1 f W) (hs : IsOpen s) (hx : x ∈ s)
    (hΦ : ContinuousOn (fun τ ↦ Φ (x, τ)) (uIcc t₀ t))
    (hrange : ∀ τ ∈ uIcc t₀ t, Φ (x, τ) ∈ W)
    (hinit : ∀ y ∈ s, Φ (y, t₀) = σ y) (hσ : HasFDerivAt σ Dσ x)
    (hode : ∀ y ∈ s, ∀ τ ∈ uIcc t₀ t,
      HasDerivAt (fun r ↦ Φ (y, r)) (f (Φ (y, τ))) τ)
    (hlip : ∀ τ ∈ uIcc t₀ t, LipschitzOnWith K (fun y ↦ Φ (y, τ)) s)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ E)
    (hJ : ∀ τ ∈ uIcc t₀ t,
      HasDerivAt J ((fderiv ℝ f (Φ (x, τ))).comp (J τ)) τ) :
    HasFDerivAt (fun y ↦ Φ (y, t)) ((J t).comp Dσ) x := by
  have hA : ContinuousOn (fun τ ↦ fderiv ℝ f (Φ (x, τ))) (uIcc t₀ t) :=
    (hf.continuousOn_fderiv_of_isOpen hW le_rfl).comp hΦ hrange
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA
  let L := max M 1
  have hL : 0 ≤ L := le_trans zero_le_one (le_max_right _ _)
  let C := gronwallBound 1 L 1 |t - t₀|
  have hC : 0 ≤ C := gronwallBound_nonneg zero_le_one hL zero_le_one (abs_nonneg _)
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let ε := c / (C + 1)
  have hε : 0 < ε := div_pos hc (by positivity)
  have hi : ∀ᶠ y in 𝓝 x, ‖σ y - σ x - Dσ (y - x)‖ ≤ ε * ‖y - x‖ := by
    simpa only using (Asymptotics.isLittleO_iff.mp
      (hasFDerivAt_iff_isLittleO.mp hσ) hε)
  filter_upwards [hs.mem_nhds hx, hi,
    section_uniform_remainder hW hf (hs.mem_nhds hx) isCompact_uIcc
      hΦ hrange hlip hε] with y hy hyinit hrem
  have hb := norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ Φ (y, τ) - Φ (x, τ) - J τ (Dσ (y - x)))
    (R' := fun τ ↦ f (Φ (y, τ)) - f (Φ (x, τ)) -
      fderiv ℝ f (Φ (x, τ)) (J τ (Dσ (y - x))))
    (δ := ε * ‖y - x‖) (L := L) (ε := ε * ‖y - x‖)
    (fun τ hτ ↦ by
      simpa only [Pi.sub_def, ContinuousLinearMap.comp_apply, map_zero, add_zero] using
        ((hode y hy τ hτ).sub (hode x hx τ hτ)).sub
        ((hJ τ hτ).clm_apply (hasDerivAt_const τ (Dσ (y - x)))))
    (by simpa [hinit y hy, hinit x hx, hJinit] using hyinit) (by
      intro τ hτ
      let A := fderiv ℝ f (Φ (x, τ))
      calc
        _ = ‖A (Φ (y, τ) - Φ (x, τ) - J τ (Dσ (y - x))) +
            (f (Φ (y, τ)) - f (Φ (x, τ)) - A (Φ (y, τ) - Φ (x, τ)))‖ := by
          congr 1
          dsimp only [A]
          simp only [map_sub]
          abel
        _ ≤ ‖A (Φ (y, τ) - Φ (x, τ) - J τ (Dσ (y - x)))‖ +
            ‖f (Φ (y, τ)) - f (Φ (x, τ)) - A (Φ (y, τ) - Φ (x, τ))‖ := norm_add_le _ _
        _ ≤ ‖A‖ * ‖Φ (y, τ) - Φ (x, τ) - J τ (Dσ (y - x))‖ + ε * ‖y - x‖ :=
          add_le_add (A.le_opNorm _) (hrem τ hτ)
        _ ≤ L * ‖Φ (y, τ) - Φ (x, τ) - J τ (Dσ (y - x))‖ + ε * ‖y - x‖ := by
          gcongr
          exact (hM τ hτ).trans (le_max_left _ _))
  have hεC : C * ε ≤ c := by
    calc
      C * ε ≤ (C + 1) * ε := by gcongr; linarith
      _ = c := mul_div_cancel₀ _ (by positivity)
  calc
    _ ≤ gronwallBound (ε * ‖y - x‖) L (ε * ‖y - x‖) |t - t₀| := hb
    _ = C * (ε * ‖y - x‖) := by
      simpa only [one_mul] using gronwallBound_mul 1 L 1 (ε * ‖y - x‖) |t - t₀|
    _ = (C * ε) * ‖y - x‖ := by ring
    _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right hεC (norm_nonneg _)

variable [CompleteSpace E]

/-- Joint smoothness on the original strip for solutions with a smooth initial
section. The section derivative is proved to evolve by the actual linearized
equation. This supplies the regularity premise of
`exists_retained_joint_flow_tolerance` for the retained Hamilton section
(`app:lem:common-hamilton-phase`). -/
theorem contDiffOn_retained_section_flow
    {f : E → E} {W : Set E} {s : Set P} {Φ : P × ℝ → E} {σ : P → E}
    {a b t₀ : ℝ} {K : ℝ≥0}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ p ∈ s, ∀ t ∈ Ioo a b, Φ (p, t) ∈ W)
    (hσ : ContDiffOn ℝ ∞ σ s) (hinit : ∀ p ∈ s, Φ (p, t₀) = σ p)
    (hode : ∀ p ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (p, τ)) (f (Φ (p, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun p ↦ Φ (p, t)) s) :
    ContDiffOn ℝ ∞ Φ (s ×ˢ Ioo a b) := by
  have hA : ContinuousOn (fun q ↦ fderiv ℝ f (Φ q)) (s ×ˢ Ioo a b) :=
    (hf.continuousOn_fderiv_of_isOpen hW (by simp)).comp hΦ
      (fun q hq ↦ hrange q.1 hq.1 q.2 hq.2)
  obtain ⟨J, hJcont, hJinit, hJ⟩ := exists_continuous_linearEvolution ht₀ hA
  have hdx (p) (hp : p ∈ s) (t) (ht : t ∈ Ioo a b) :
      HasFDerivAt (fun y ↦ Φ (y, t)) ((J (p, t)).comp (fderiv ℝ σ p)) p := by
    have hsub := ordConnected_Ioo.uIcc_subset ht₀ ht
    exact section_flow_hasFDerivAt hW (hf.of_le (by simp)) hs hp
      (hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun τ hτ ↦ ⟨hp, hsub hτ⟩))
      (fun τ hτ ↦ hrange p hp τ (hsub hτ)) hinit
      ((hσ.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      (fun y hy τ hτ ↦ hode y hy τ (hsub hτ))
      (fun τ hτ ↦ hlip τ (hsub hτ)) (hJinit p hp)
      (fun τ hτ ↦ hJ p hp τ (hsub hτ))
  have hall (m : ℕ) : ContDiffOn ℝ m Φ (s ×ˢ Ioo a b) := by
    induction m with
    | zero => exact contDiffOn_zero.mpr hΦ
    | succ m ih =>
      have hAm : ContDiffOn ℝ m (fun q ↦ fderiv ℝ f (Φ q)) (s ×ˢ Ioo a b) :=
        (hf.fderiv_of_isOpen (m := (m : ℕ∞ω)) hW (by simp)).comp ih
          (fun q hq ↦ hrange q.1 hq.1 q.2 hq.2)
      have hJm := LinearEvolutionRegularity.contDiffOn_linearEvolution m hs ht₀
        hAm hJcont hJinit hJ
      have hσm : ContDiffOn ℝ m (fun q : P × ℝ ↦ fderiv ℝ σ q.1) (s ×ˢ Ioo a b) :=
        (hσ.fderiv_of_isOpen (m := (m : ℕ∞ω)) hs (by simp)).comp contDiffOn_fst
          (fun _ hq ↦ hq.1)
      simpa only [Nat.cast_add, Nat.cast_one] using
        contDiffOn_succ_of_contDiffOn_partials hs isOpen_Ioo (hJm.clm_comp hσm)
          ((hf.of_le (by simp)).comp ih (fun q hq ↦ hrange q.1 hq.1 q.2 hq.2))
          (fun q hq ↦ hdx q.1 hq.1 q.2 hq.2) (fun q hq ↦ hode q.1 hq.1 q.2 hq.2)
  exact contDiffOn_infty.mpr hall

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
