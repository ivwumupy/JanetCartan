module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.Forward
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily.Buffered

/-!
# Fixed local target for the augmented transport family

The local inverse part of `app:ch_osc:prop:osc-normal`, Step 4'. A central
seed differential and joint forward smoothness produce a genuine inverse on
one fixed target, its range in a compact convex input ball, the full augmented
half-gap and a positive normalized determinant bound. The inverse is constructed
by `phaseChartInverse`; none of its properties is assumed.

This local result does not yet assert conic support containment. In particular,
the original uncut frequency support is not contained in these compact balls.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter Metric
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts

variable {n : ℕ}

private theorem contDiffOn_scale_fderiv
    {f : ℝ → InputVariables n → InputVariables n} {I : Set ℝ} {W : Set (InputVariables n)}
    (hI : IsOpen I) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ W)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦ fderiv ℝ (f q.1) q.2) (I ×ˢ W) := by
  have hs : ContDiffOn ℝ ∞ (fun q : InputVariables n × ℝ ↦ f q.2 q.1) (W ×ˢ I) :=
    hf.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  exact (contDiffOn_parameterFDeriv hW hI hs).comp
    (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq ↦ ⟨hq.2, hq.1⟩)

/-- Local common inverse construction from joint forward smoothness and the
central seed differential. `A` is to be supplied by the seed incidence
calculation, not by any inverse regularity assumption. The whole augmented
map is normalized, including both positions and spectator. This is the local
input to `CarrierVariation.exists_inverseCoordinates_sub_le`; conic extension
and containment of the original masks remain separate obligations
(`app:ch_background:eq:bg-Psi`, `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_local_common_transport_inverse
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {I : Set ℝ} {W : Set (InputVariables n)} {p₀ : InputVariables n}
    (hI : IsOpen I) (hW : IsOpen W) (h0 : (0 : ℝ) ∈ I) (hp₀ : p₀ ∈ W)
    (hF : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ W))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hA : fderiv ℝ (augmentedTransportGradient (Y 0)) p₀ = A.toContinuousLinearMap) :
    ∃ ρ > (0 : ℝ), closedBall p₀ ρ ⊆ W ∧
    ∃ ε > (0 : ℝ), Ioo (-ε) ε ⊆ I ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ interior Q ∧
    ∃ c > (0 : ℝ), ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
        augmentedTransportGradient (Y q.1) q.2) (Ioo (-ε) ε ×ˢ W) ∧
      ∀ σ ∈ Ioo (-ε) ε,
        ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W ∧
        ContDiffOn ℝ ∞ (u σ) Ω ∧
        MapsTo (inverseCoordinates (u σ)) Ω (ball p₀ ρ) ∧
        MapsTo (inverseCoordinates (u σ)) Q (closedBall p₀ ρ) ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) =
          q.1.2.2) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ closedBall p₀ ρ,
          c ≤ |(A.symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (Y σ)) p)).det|) ∧
        InjOn (augmentedTransportGradient (Y σ)) (closedBall p₀ ρ) := by
  let f : ℝ → InputVariables n → InputVariables n := fun σ p ↦
    A.symm (augmentedTransportGradient (Y σ) p)
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ W) :=
    A.symm.contDiff.comp_contDiffOn hF
  have hslice (σ : ℝ) (hσ : σ ∈ I) :
      ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hσ, hp⟩)
  have hdf (σ : ℝ) (hσ : σ ∈ I) (p : InputVariables n) (hp : p ∈ W) :
      fderiv ℝ (f σ) p = A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (Y σ)) p) :=
    (A.symm.hasFDerivAt.comp p
      (((hslice σ hσ).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦ fderiv ℝ (f q.1) q.2)
      (I ×ˢ W) := contDiffOn_scale_fderiv hI hW hf
  have hdf0 : fderiv ℝ (f 0) p₀ = ContinuousLinearMap.id ℝ (InputVariables n) := by
    rw [hdf 0 h0 p₀ hp₀, hA]
    apply ContinuousLinearMap.ext
    intro x
    exact A.symm_apply_apply x
  have hnear : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀),
      q ∈ I ×ˢ W ∧ ‖fderiv ℝ (f q.1) q.2 -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ < 1 / 4 := by
    have hdc : ContinuousAt (fun q : ℝ × InputVariables n ↦ fderiv ℝ (f q.1) q.2)
        (0, p₀) := hd.continuousOn.continuousAt ((hI.prod hW).mem_nhds ⟨h0, hp₀⟩)
    have hc : ContinuousAt (fun q : ℝ × InputVariables n ↦
        ‖fderiv ℝ (f q.1) q.2 - ContinuousLinearMap.id ℝ (InputVariables n)‖) (0, p₀) :=
      (hdc.sub continuousAt_const).norm
    have hmem : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀), q ∈ I ×ˢ W :=
      (hI.prod hW).mem_nhds ⟨h0, hp₀⟩
    exact hmem.and
      (hc.eventually (gt_mem_nhds (by
        change ‖fderiv ℝ (f 0) p₀ - ContinuousLinearMap.id ℝ (InputVariables n)‖ < 1 / 4
        rw [hdf0, sub_self, norm_zero]
        norm_num)))
  obtain ⟨d, hdpos, hdball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let ρ := d / 2
  have hρ : 0 < ρ := half_pos hdpos
  have hρW : closedBall p₀ ρ ⊆ W := by
    intro p hp
    exact (hdball (0, p) (by
      rw [mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
      exact ⟨hdpos, (mem_closedBall.mp hp).trans_lt (half_lt_self hdpos)⟩)).1.2
  let a := f 0 p₀
  let ref : InputVariables n → InputVariables n := fun p ↦ p + (a - p₀)
  have href (p : InputVariables n) : HasFDerivAt ref (ContinuousLinearMap.id ℝ _) p :=
    (hasFDerivAt_id p).add_const _
  obtain ⟨c, hc, δ, hδ, V, L, hV, hVc, _, _, hstable⟩ :=
    exists_common_smooth_phase_inverses (P := ℝ)
      (K := {p₀}) (D₁ := ball p₀ ρ) (D := closedBall p₀ ρ)
      isCompact_singleton isOpen_ball (by
        intro p hp
        rw [mem_singleton_iff] at hp
        exact hp ▸ mem_ball_self hρ)
      ball_subset_closedBall (convex_closedBall _ _) (ContinuousLinearEquiv.refl ℝ _)
      (fun p _ ↦ (href p).differentiableAt)
      (by intro p _; rw [(href p).fderiv]; simp)
  have hvalue : ∀ᶠ σ in 𝓝 (0 : ℝ), ‖f σ p₀ - a‖ < δ := by
    have hv : ContinuousAt (fun σ ↦ f σ p₀) 0 :=
      (hf.continuousOn.continuousAt ((hI.prod hW).mem_nhds ⟨h0, hp₀⟩)).comp
        (continuousAt_id.prodMk continuousAt_const)
    simpa [a] using (hv.sub continuousAt_const).norm.eventually
      (gt_mem_nhds (show ‖f 0 p₀ - f 0 p₀‖ < δ by simpa using hδ))
  obtain ⟨e, he, heball⟩ := Metric.eventually_nhds_iff_ball.mp hvalue
  let ε := min e ρ / 2
  have hε : 0 < ε := half_pos (lt_min he hρ)
  have hεe : ε < e := by dsimp [ε]; linarith [min_le_left e ρ]
  have hεd : ε < d := by dsimp [ε, ρ]; linarith [min_le_right e (d / 2)]
  have hparam (σ : ℝ) (hσ : σ ∈ Ioo (-ε) ε) : dist σ 0 < d := by
    rw [Real.dist_eq, sub_zero]
    exact (abs_lt.mpr hσ).trans hεd
  have hpair (σ : ℝ) (hσ : σ ∈ Ioo (-ε) ε) (p : InputVariables n)
      (hp : p ∈ closedBall p₀ ρ) :
      (σ, p) ∈ I ×ˢ W ∧ ‖fderiv ℝ (f σ) p - ContinuousLinearMap.id ℝ _‖ < 1 / 4 :=
    hdball (σ, p) (by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨hparam σ hσ, (mem_closedBall.mp hp).trans_lt (half_lt_self hdpos)⟩)
  have hεI : Ioo (-ε) ε ⊆ I := fun σ hσ ↦
    (hpair σ hσ p₀ (mem_closedBall_self hρ.le)).1.1
  have hInv : BufferedPhaseInverse f (Ioo (-ε) ε) {p₀} (ball p₀ ρ) (closedBall p₀ ρ)
      V L δ c (ContinuousLinearEquiv.refl ℝ _) := by
    apply hstable f (Ioo (-ε) ε) W isOpen_Ioo hW hρW
      (hf.mono (prod_mono hεI Subset.rfl))
    · intro σ hσ p hp
      change ‖fderiv ℝ (f σ) p - fderiv ℝ ref p‖ ≤ 1 / 4
      rw [(href p).fderiv]
      exact (hpair σ hσ p hp).2.le
    · intro σ hσ p hp
      have hpp : p = p₀ := mem_singleton_iff.mp hp
      subst p
      have hv := heball σ (by
        rw [mem_ball, Real.dist_eq, sub_zero]
        exact (abs_lt.mpr hσ).trans hεe)
      rw [show ref p₀ = a by dsimp [ref]; abel]
      exact hv.le
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have haimage : a ∈ f 0 '' ({p₀} : Set (InputVariables n)) := ⟨p₀, rfl, rfl⟩
  have hsmall : closedBall a (δ / 2) ⊆ V := by
    intro v hv
    apply hInv.inner_buffer 0 hzero
    apply closedBall_subset_cthickening haimage δ
    exact closedBall_subset_closedBall (by linarith) hv
  let Q := A '' closedBall a (δ / 2)
  let Ω := A.symm ⁻¹' V
  have hQΩ : Q ⊆ Ω := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [Ω] using hsmall hv
  let g : ℝ → (Variables n × Euclidean 2) → InputVariables n := fun σ q ↦
    phaseChartInverse f (ball p₀ ρ) σ (A.symm q)
  let u : ℝ → (Variables n × Euclidean 2) → ℝ × Euclidean (n - 1) :=
    fun σ q ↦ ((g σ q).2.1.1, (g σ q).2.2)
  have hg (σ : ℝ) (hσ : σ ∈ Ioo (-ε) ε) : ContDiffOn ℝ ∞ (g σ) Ω :=
    hInv.smooth.comp (f := fun q ↦ (σ, A.symm q))
      (contDiffOn_const.prodMk A.symm.contDiff.contDiffOn)
      (fun _ hq ↦ ⟨hσ, hq⟩)
  have heq (σ : ℝ) (hσ : σ ∈ Ioo (-ε) ε) (q : Variables n × Euclidean 2) (hq : q ∈ Ω) :
      augmentedTransportGradient (Y σ) (g σ q) = q := by
    apply A.symm.injective
    exact hInv.right_inv σ hσ _ hq
  have hcoords (σ : ℝ) (hσ : σ ∈ Ioo (-ε) ε) (q : Variables n × Euclidean 2) (hq : q ∈ Ω) :
      inverseCoordinates (u σ) q = g σ q := by
    have hh := heq σ hσ q hq
    have hx := congrArg (fun a : Variables n × Euclidean 2 ↦ a.1.1) hh
    have hy := congrArg (fun a : Variables n × Euclidean 2 ↦ a.1.2.1) hh
    have hv := congrArg (fun a : Variables n × Euclidean 2 ↦ a.2) hh
    dsimp only [augmentedTransportGradient] at hx hy hv
    exact Prod.ext (Prod.ext hx.symm hy.symm) (Prod.ext (Prod.ext rfl hv.symm) rfl)
  refine ⟨ρ, hρ, hρW, ε, hε, hεI, Q, Ω,
    (isCompact_closedBall a (δ / 2)).image A.continuous,
    hV.preimage A.symm.continuous, hQΩ, ?_, c, hc, u,
    hF.mono (prod_mono hεI Subset.rfl), ?_⟩
  · apply mem_interior_iff_mem_nhds.mpr
    have hh := A.isOpenMap.image_mem_nhds (closedBall_mem_nhds a (half_pos hδ))
    simpa only [a, f, ContinuousLinearEquiv.apply_symm_apply] using hh
  · intro σ hσ
    have hrange : MapsTo (inverseCoordinates (u σ)) Ω (ball p₀ ρ) := by
      intro q hq
      rw [hcoords σ hσ q hq]
      exact hInv.inverse_mem σ hσ _ hq
    refine ⟨hslice σ (hεI hσ), (hg σ hσ).snd.fst.fst.prodMk (hg σ hσ).snd.snd,
      hrange, fun _ hq ↦ ball_subset_closedBall (hrange (hQΩ hq)), ?_, ?_, ?_, ?_⟩
    · intro q hq
      rw [hcoords σ hσ q hq]
      exact congrArg (fun a : Variables n × Euclidean 2 ↦ a.1.2.2) (heq σ hσ q hq)
    · intro p hp
      rw [← hdf σ (hεI hσ) p (hρW hp)]
      exact (hpair σ hσ p hp).2.le.trans (by norm_num)
    · intro p hp
      rw [← hdf σ (hεI hσ) p (hρW hp)]
      exact (hInv.differential_bounds σ hσ p hp).2.2
    · intro p hp q hq he
      exact hInv.injective σ hσ hp hq (congrArg A.symm he)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
