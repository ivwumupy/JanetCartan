module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.SectionFlows

/-!
# Common Hamilton-flow records with finite-order projection continuity

For `app:lem:common-hamilton-phase`, package the actual root-initialized
trajectories as `HamiltonFlow` records. The consumer is the buffered-chart
assembly: it needs one reference flow, a common open domain, and projection
continuity measured on its fixed compact closure.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] in
private theorem cNorm_sectionProjection_sub_le
    (j : U →ₗᵢ[ℝ] E) (ν : E) (g g₀ : InitialData U → ℝ)
    (Ψ Ψ₀ : (E × E) × ℝ → E × E)
    {K : Set (ℝ × InitialData U)} (hK : IsCompact K) (m : ℕ)
    (hf : ∀ q ∈ K, ContDiffAt ℝ m (sectionFlowState j ν g Ψ) q)
    (hf₀ : ∀ q ∈ K, ContDiffAt ℝ m (sectionFlowState j ν g₀ Ψ₀) q) :
    cNorm K m (sectionAugmentedProjection j ν g Ψ - sectionAugmentedProjection j ν g₀ Ψ₀) ≤
      (m + 1 : ℝ) * cNorm K m (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀) := by
  let L : (E × E) →L[ℝ] E × (ℝ × U) := (ContinuousLinearMap.fst ℝ E E).prod 0
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [L] using norm_fst_le z
  have he : sectionAugmentedProjection j ν g Ψ - sectionAugmentedProjection j ν g₀ Ψ₀ =
      L ∘ (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀) := by
    funext q
    simp [sectionAugmentedProjection, L]
  rw [he]
  apply (cNorm_le_sum_of_bounds (C := fun _ ↦
    cNorm K m (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀))
    (fun _ _ ↦ cNorm_nonneg _ _ _) ?_).trans_eq (by simp)
  intro k hk q hq
  apply (L.norm_iteratedFDeriv_comp_left ((hf q hq).sub (hf₀ q hq))
    (by exact_mod_cast hk)).trans
  apply (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun q hq ↦ (hf q hq).sub (hf₀ q hq)) hq hk) (norm_nonneg L)).trans
  convert! mul_le_mul_of_nonneg_right hL
    (cNorm_nonneg K m (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀)) using 1
  simp only [one_mul]

/-- `app:lem:common-hamilton-phase`: actual Hamilton-flow records with one
reference and common time/parameter domains. The positive tolerance `d m ε hε`
is selected before the perturbed symbol. Each constructed flow satisfies every
finite-order comparison simultaneously. Its scalar input order is `m + 1`;
the separate `C³` neighborhood only supplies existence on the common domain. -/
theorem exists_common_finiteOrder_hamiltonFlows
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r T δ : ℝ) (d : (m : ℕ) → (ε : ℝ) → 0 < ε → ℝ) (Φ₀ : HamiltonFlow H₀ U),
      0 < r ∧ 0 < T ∧ 0 < δ ∧ (∀ m ε hε, 0 < d m ε hε) ∧
      Φ₀.time = Ioo (-T) T ∧ Φ₀.parameters = ball s₀ r ∧
      Φ₀.sectionMap = j.toContinuousLinearMap ∧
      Φ₀.momentum (0, s₀) = z₀.2 ∧
      ContDiffOn ℝ ∞ Φ₀.position (Φ₀.time ×ˢ Φ₀.parameters) ∧
      (∀ q ∈ Icc (-T) T ×ˢ closedBall s₀ r, ContDiffAt ℝ ∞ Φ₀.augmentedProjection q) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ Φ : HamiltonFlow H U,
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters, (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          (∀ q ∈ Icc (-T) T ×ˢ closedBall s₀ r, ContDiffAt ℝ ∞ Φ.augmentedProjection q) ∧
          (∀ m ε hε, cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.h z - H₀.h z) < d m ε hε →
            cNorm (Icc (-T) T ×ˢ closedBall s₀ r) m
              (Φ.augmentedProjection - Φ₀.augmentedProjection) < ε) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨r, a, ρ, T, δ, g₀, Ψ₀, hr, _ha, hρ, hT, hδ, hgbase, hΨ₀,
      hmap, hg₀, hroot₀, hstable, hfamily⟩ :=
    exists_common_finiteOrder_rootedFlows H₀ hD hDH₀ hH₀ j ν hR hRD henergy htrans
  let Q := Icc (-(T / 2)) (T / 2) ×ˢ closedBall s₀ r
  let O := Ioo (-T) T ×ˢ ball s₀ (2 * r)
  have hQ : IsCompact Q := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hQO : Q ⊆ O := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      closedBall_subset_ball (by linarith) hq.2⟩
  have hrr : ball s₀ r ⊆ ball s₀ (2 * r) := ball_subset_ball (by linarith)
  have hinit (g : InitialData U → ℝ)
      (hg : ∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a)) :
      ∀ s ∈ ball s₀ (2 * r), transverseSectionState j ν (s, g s) ∈ ball z₀ ρ :=
    fun s hs ↦ ball_subset_ball (by linarith : ρ / 2 ≤ ρ)
      (hmap ⟨ball_subset_closedBall hs, Ioo_subset_Icc_self (hg s hs)⟩)
  have hfield (H : HomogeneousSymbol E) (hDH : D ⊆ H.domain) (hH : ContDiffOn ℝ ∞ H.h D) :
      ∀ z ∈ closedBall z₀ R, DifferentiableAt ℝ H.vectorField z := fun z hz ↦
    ((H.contDiffOn_vectorField_of_subset hD hDH (n := ∞) (by simpa using hH)).contDiffAt
      (hD.mem_nhds (hRD hz))).differentiableAt (by simp)
  obtain ⟨Φ₀, ht₀, hp₀, hj₀, hx₀, hm₀, hc₀, _hmc₀⟩ :=
    exists_hamiltonFlow_of_sectionFlow H₀ j ν horth isOpen_ball (half_pos hT)
      (by linarith : T / 2 ≤ T) hΨ₀ (hfield H₀ hDH₀ hH₀) (hRD.trans hDH₀)
      (hg₀.mono hrr) (fun s hs ↦ hinit g₀ (fun s hs ↦ (hroot₀ s hs).1) s (hrr hs))
      (fun s hs ↦ (hroot₀ s (hrr hs)).2)
  have hsmooth₀ : ContDiffOn ℝ ∞ (sectionFlowState j ν g₀ Ψ₀) O :=
    (sectionFlowState_properties H₀ j ν hΨ₀ hg₀ (hinit g₀ (fun s hs ↦ (hroot₀ s hs).1))).1
  have he₀ : Φ₀.augmentedProjection = sectionAugmentedProjection j ν g₀ Ψ₀ := by
    funext q
    simp only [HamiltonFlow.augmentedProjection, hx₀, sectionAugmentedProjection]
  have hproj₀ : ∀ q ∈ Q, ContDiffAt ℝ ∞ Φ₀.augmentedProjection q := by
    intro q hq
    rw [he₀]
    exact ((hsmooth₀.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds (hQO hq))).fst.prodMk
      contDiff_snd.snd.contDiffAt)
  have htolerance : ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ),
      ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ) (Ψ : (E × E) × ℝ → E × E),
        D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        ODE.IsSmoothFlowOn H.vectorField z₀ R ρ T Ψ →
        ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
        (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
          H.h (transverseSectionState j ν (s, g s)) = s.2.1) →
        ContDiffOn ℝ ∞ (sectionFlowState j ν g Ψ) O →
        cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.h z - H₀.h z) < d →
        cNorm Q m (sectionAugmentedProjection j ν g Ψ - sectionAugmentedProjection j ν g₀ Ψ₀) < ε := by
    intro m ε hε
    have hm : 0 < (m + 1 : ℝ) := by positivity
    obtain ⟨d, hd, hb⟩ := hstable m (ε / (m + 1)) (div_pos hε hm)
    refine ⟨d, hd, ?_⟩
    intro H g Ψ hDH hH hΨ hg hroot hsmooth hsmall
    have hh := hb H g Ψ hDH hH hΨ hg
      (fun s hs ↦ ⟨Ioo_subset_Icc_self (hroot s hs).1, (hroot s hs).2⟩) hsmall
    have hc : cNorm Q m (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀) < ε / (m + 1) := by
      linarith [cNorm_nonneg (closedBall s₀ r) m (g - g₀),
        cNorm_nonneg (closedBall z₀ (ρ / 2) ×ˢ Icc (-(T / 2)) (T / 2)) m (Ψ - Ψ₀)]
    apply (cNorm_sectionProjection_sub_le j ν g g₀ Ψ Ψ₀ hQ m
      (fun q hq ↦ (hsmooth.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds (hQO hq))).of_le (by simp))
      (fun q hq ↦ (hsmooth₀.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds (hQO hq))).of_le (by simp))).trans_lt
    exact (mul_lt_mul_of_pos_left hc hm).trans_eq (mul_div_cancel₀ ε hm.ne')
  choose d hd hcompare using htolerance
  refine ⟨r, T / 2, δ, d, Φ₀, hr, half_pos hT, hδ, hd, ht₀, hp₀, hj₀, ?_, hc₀, hproj₀, ?_⟩
  · rw [hm₀]
    change (Ψ₀ (transverseSectionState j ν (s₀, g₀ s₀), 0)).2 = _
    rw [hΨ₀.initial _ (ball_subset_closedBall
      (hinit g₀ (fun s hs ↦ (hroot₀ s hs).1) s₀ (mem_ball_self (by positivity)))), hgbase]
  · intro H hDH hH hsmall
    obtain ⟨g, Ψ, hΨ, hg, hroot, hsmooth⟩ := hfamily H hDH hH hsmall
    obtain ⟨Φ, ht, hp, hj, hx, hm, hc, hmc⟩ :=
      exists_hamiltonFlow_of_sectionFlow H j ν horth isOpen_ball (half_pos hT)
        (by linarith : T / 2 ≤ T) hΨ (hfield H hDH hH) (hRD.trans hDH)
        (hg.mono hrr) (fun s hs ↦ hinit g (fun s hs ↦ (hroot s hs).1) s (hrr hs))
        (fun s hs ↦ (hroot s (hrr hs)).2)
    have he : Φ.augmentedProjection = sectionAugmentedProjection j ν g Ψ := by
      funext q
      simp only [HamiltonFlow.augmentedProjection, hx, sectionAugmentedProjection]
    refine ⟨Φ, ht.trans ht₀.symm, hp.trans hp₀.symm, hj, hc, hmc, ?_, ?_, ?_⟩
    · intro q hq
      rw [hx, hm]
      apply hΨ.range _ (ball_subset_closedBall (hinit g (fun s hs ↦ (hroot s hs).1) q.2 (hrr (hp ▸ hq.2))))
      have htime := ht ▸ hq.1
      exact ⟨by linarith [htime.1], by linarith [htime.2]⟩
    · intro q hq
      rw [he]
      exact ((hsmooth.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds (hQO hq))).fst.prodMk
        contDiff_snd.snd.contDiffAt)
    · intro m ε hε hn
      rw [he, he₀]
      exact hcompare m ε hε H g Ψ hDH hH hΨ hg hroot hsmooth hn

end JanetCartan.HamiltonPhase
