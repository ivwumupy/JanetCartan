module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameEstimates

/-!
# Actual root and flow families with sharp tame estimates

For `app:lem:common-hamilton-phase`, instantiate the root and joint flow estimates
on the same constructed objects. The cylinder, transverse gap, common time,
state containment and low symbol budget are all produced from the reference
symbol. This is the forward-family input for the common buffered phase assembly.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

local instance tameFamilyNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tameFamilyNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

/-- Actual common root-initialized Hamilton flows with one-high bounds at scalar
symbol order `m + 1` (`app:lem:common-hamilton-phase`). All radii, the transverse
gap, the low neighborhood and the sequence of constants precede the variable
symbol. The same root and flow work at every order. No root, flow or projection
budget, state-containment condition or chosen cylinder is an input.

The retained root uniqueness and initial state identify this family with other
constructions on common subdomains. The final phase assembly must still select
inverse buffers and combine conic geometry and continuity on those charts. -/
theorem exists_commonTameHamiltonFlows
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r a c T δ C : ℝ) (B : ℕ → ℝ) (Φ₀ : HamiltonFlow H₀ U),
      0 < r ∧ 0 < a ∧ 0 < c ∧ 4 * r ≤ T ∧ 0 < δ ∧ 0 < C ∧ (∀ m, 0 < B m) ∧
      Φ₀.time = Ioo (-T) T ∧ Φ₀.parameters = ball s₀ (2 * r) ∧
      Φ₀.sectionMap = j.toContinuousLinearMap ∧ Φ₀.momentum (0, s₀) = z₀.2 ∧
      ContDiffOn ℝ ∞ Φ₀.position (Φ₀.time ×ˢ Φ₀.parameters) ∧
      MapsTo (transverseSectionState j ν)
        (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (closedBall z₀ R) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (g : InitialData U → ℝ) (Φ : HamiltonFlow H U),
          Φ.time = Ioo (-T) T ∧ Φ.parameters = ball s₀ (2 * r) ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
            c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) ∧
          (∀ s ∈ ball s₀ (2 * r), ∀ τ ∈ Icc (τ₀ - a) (τ₀ + a),
            H.h (transverseSectionState j ν (s, τ)) = s.2.1 ↔ g s = τ) ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ s ∈ ball s₀ (2 * r),
            (Φ.position (0, s), Φ.momentum (0, s)) = transverseSectionState j ν (s, g s)) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          (∀ m : ℕ,
            cNorm (closedBall s₀ r ×ˢ Icc (-r) r) m
                (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) +
              cNorm (closedBall ((0 : ℝ), s₀) r) m Φ.augmentedProjection ≤
                B m * (1 + cNorm (closedBall z₀ R) (m + 1) H.h)) ∧
          (∀ q ∈ closedBall ((0 : ℝ), s₀) r,
            ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤
              C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ∧
            ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤
              C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨ρ, hρ, T, hT, Cf, hCf, δf, hδf, Ψ₀, hΨ₀, hflows⟩ :=
    exists_common_symbol_flows H₀ hD hDH₀ hR hRD hH₀
  let D' := D ∩ ball z₀ (min R (ρ / 2))
  have hD' : IsOpen D' := hD.inter isOpen_ball
  have hbase : z₀ ∈ D' :=
    ⟨hRD (mem_closedBall_self hR.le), mem_ball_self (lt_min hR (half_pos hρ))⟩
  obtain ⟨r₀, a, c, Cr, δr, g₀, hr₀, ha, hc, hCr, hδr,
      _hK, _hL, hLD', hgbase, hg₀, hroot₀, hroots⟩ :=
    exists_uniform_C1_stable_sectionRoot H₀ hD' (inter_subset_left.trans hDH₀)
      (hH₀.mono inter_subset_left) j ν hbase henergy htrans
  let L := transverseSectionState j ν ''
    (closedBall s₀ (2 * r₀) ×ˢ Icc (τ₀ - a) (τ₀ + a))
  have hLR : L ⊆ closedBall z₀ R := fun _ hz ↦
    ball_subset_closedBall (ball_subset_ball (min_le_left _ _) (hLD' hz).2)
  have hLρ : L ⊆ ball z₀ ρ := fun _ hz ↦
    ball_subset_ball (by linarith [min_le_right R (ρ / 2)]) (hLD' hz).2
  have hLhalf : L ⊆ ball z₀ (ρ / 2) := fun _ hz ↦
    ball_subset_ball (min_le_right _ _) (hLD' hz).2
  let r := min r₀ (T / 8)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrT : 4 * r ≤ T := by have hh := min_le_right r₀ (T / 8); dsimp [r]; linarith
  have hparams : ball s₀ (2 * r) ⊆ ball s₀ (2 * r₀) :=
    ball_subset_ball (by linarith)
  have hmap : MapsTo (transverseSectionState j ν)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (closedBall z₀ R) := by
    intro q hq
    exact hLR (mem_image_of_mem _ ⟨closedBall_subset_closedBall (by linarith) hq.1, hq.2⟩)
  let M := 1 + cNorm (closedBall z₀ R) 2 H₀.h
  have hM : 0 ≤ M := by
    have hh := cNorm_nonneg (closedBall z₀ R) 2 H₀.h
    dsimp [M]; linarith
  choose F hF hflowBound using fun m ↦ exists_hamiltonFlow_state_cNorm_bound
    j ν s₀ τ₀ z₀ hr ha hc hR hM hD hRD hmap m
  choose P hP hprojection using fun m ↦
    exists_augmentedProjection_cNorm_bound_from_state (E := E) s₀ hr m
  have hinit₀ : ∀ s ∈ ball s₀ (2 * r₀),
      transverseSectionState j ν (s, g₀ s) ∈ ball z₀ (ρ / 2) := fun s hs ↦
    hLhalf (mem_image_of_mem _ ⟨ball_subset_closedBall hs,
      Ioo_subset_Icc_self (hroot₀ s hs).1⟩)
  have hfield₀ : ∀ z ∈ closedBall z₀ R, DifferentiableAt ℝ H₀.vectorField z :=
    fun z hz ↦ ((H₀.contDiffOn_vectorField_of_subset hD hDH₀
      (n := ∞) (by simpa using hH₀)).contDiffAt
        (hD.mem_nhds (hRD hz))).differentiableAt (by simp)
  obtain ⟨Φ₀, ht₀, hp₀, hj₀, hx₀, hm₀, hΦ₀x, _hΦ₀p⟩ :=
    exists_hamiltonFlow_of_sectionFlow H₀ j ν horth isOpen_ball hT le_rfl
      hΨ₀ hfield₀ (hRD.trans hDH₀) (hg₀.mono hparams)
      (fun s hs ↦ ball_subset_ball (by linarith) (hinit₀ s (hparams hs)))
      (fun s hs ↦ (hroot₀ s (hparams hs)).2)
  have hm₀base : Φ₀.momentum (0, s₀) = z₀.2 := by
    rw [hm₀]
    change (Ψ₀ (transverseSectionState j ν (s₀, g₀ s₀), 0)).2 = _
    rw [hΨ₀.initial _ (ball_subset_closedBall
      (ball_subset_ball (by linarith) (hinit₀ s₀ (mem_ball_self (by positivity))))), hgbase]
  obtain ⟨J, hJ, hderivative⟩ := exists_sectionAugmentedProjection_C1_bound j ν hr₀ hρ hT
    (add_pos hCr hCf) hg₀ hΨ₀.smooth hinit₀
  let Q := closedBall z₀ (ρ / 2) ×ˢ Icc (-T / 2) (T / 2)
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hQsub : Q ⊆ ball z₀ ρ ×ˢ Ioo (-T) T := by
    intro q hq
    exact ⟨closedBall_subset_ball (by linarith) hq.1,
      ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  obtain ⟨L₀, hL₀⟩ := (hΨ₀.smooth.mono hQsub).exists_lipschitzOnWith
    (by simp) ((convex_closedBall _ _).prod (convex_Icc _ _)) hQ
  let C := Cf + (L₀ : ℝ) * Cr * ‖ν‖ + J
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, a, c, T, min δf (min δr 1), C, fun m ↦ F m + P m * (1 + F m), Φ₀,
    hr, ha, hc, hrT, lt_min hδf (lt_min hδr zero_lt_one), hC,
    (fun m ↦ add_pos (hF m) (mul_pos (hP m) (by linarith [hF m]))),
    ht₀, hp₀, hj₀, hm₀base, hΦ₀x, hmap, ?_⟩
  intro H hDH hH hsmall
  have hnorm : cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤
      cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) :=
    cNorm_mono_set_of_contDiffAt hLR (isCompact_closedBall _ _)
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp))
  obtain ⟨g, hg, hroot, huniq, hcloseg⟩ := hroots H (inter_subset_left.trans hDH)
    (hH.mono inter_subset_left)
    (hnorm.trans (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))))
  obtain ⟨Ψ, hΨ, hcloseΨ⟩ := hflows H hDH hH (hsmall.trans (min_le_left _ _))
  have hinit : ∀ s ∈ ball s₀ (2 * r), transverseSectionState j ν (s, g s) ∈ ball z₀ ρ :=
    fun s hs ↦ hLρ (hroot s (hparams hs)).2.1
  have hfield : ∀ z ∈ closedBall z₀ R, DifferentiableAt ℝ H.vectorField z :=
    fun z hz ↦ ((H.contDiffOn_vectorField_of_subset hD hDH
      (n := ∞) (by simpa using hH)).contDiffAt
        (hD.mem_nhds (hRD hz))).differentiableAt (by simp)
  obtain ⟨Φ, ht, hp, hj, hx, hm, hΦx, hΦp⟩ :=
    exists_hamiltonFlow_of_sectionFlow H j ν horth isOpen_ball hT le_rfl
      hΨ hfield (hRD.trans hDH) (hg.mono hparams) hinit
      (fun s hs ↦ (hroot s (hparams hs)).2.2.1)
  have hstart : ∀ s ∈ ball s₀ (2 * r),
      (Φ.position (0, s), Φ.momentum (0, s)) = transverseSectionState j ν (s, g s) := by
    intro s hs
    rw [hx, hm]
    exact hΨ.initial _ (ball_subset_closedBall (hinit s hs))
  have hrange : ∀ q ∈ Φ.time ×ˢ Φ.parameters,
      (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R := by
    intro q hq
    rw [hx, hm]
    exact hΨ.range _ (ball_subset_closedBall (hinit q.2 (hp ▸ hq.2))) q.1
      (Ioo_subset_Icc_self (ht ▸ hq.1))
  have hlow : cNorm (closedBall z₀ R) 2 H.h ≤ M := by
    have hh := cNorm_add_le_of_contDiffAt (isCompact_closedBall z₀ R)
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
      (fun z hz ↦ (hH₀.contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
    have he : (fun z ↦ H.h z - H₀.h z) + H₀.h = H.h := by funext z; simp
    rw [he] at hh
    have hsmall₁ := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmono := cNorm_mono_order (s := closedBall z₀ R)
      (f := fun z ↦ H.h z - H₀.h z) (by omega : 2 ≤ 3)
    dsimp [M]
    linarith
  have htime : Ioo (-(4 * r)) (4 * r) ⊆ Φ.time := by
    rw [ht]
    intro t ht'
    exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  refine ⟨g, Φ, ht, hp, hj, hg.mono hparams, ?_, ?_, hΦx, hΦp, hstart, hrange, ?_, ?_⟩
  · intro s hs
    exact ⟨(hroot s (hparams hs)).1, (hroot s (hparams hs)).2.2⟩
  · intro s hs τ hτ
    exact huniq s (hparams hs) τ hτ
  · intro m
    have hf := hflowBound m H g Φ hDH hH hlow (hg.mono hparams)
      (fun s hs ↦ ⟨Ioo_subset_Icc_self (hroot s (hparams hs)).1,
        (hroot s (hparams hs)).2.2⟩) (by rw [hp]) htime hΦx hΦp hstart
      (fun s hs t ht' ↦ hrange (t, s) ⟨htime ht', hp.symm ▸
        closedBall_subset_ball (by linarith : r < 2 * r) hs⟩)
    have hproj := hprojection m H Φ (by rw [hp]) htime hΦx hΦp
    have hn := cNorm_nonneg (closedBall z₀ R) (m + 1) H.h
    have hbudget : 1 + cNorm (closedBall s₀ r ×ˢ Icc (-r) r) m
        (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) ≤
        (1 + F m) * (1 + cNorm (closedBall z₀ R) (m + 1) H.h) := by nlinarith
    have hb := hproj.trans (mul_le_mul_of_nonneg_left hbudget (hP m).le)
    nlinarith only [hf, hb]
  · intro q hq
    have hdist := mem_closedBall.mp hq
    rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_le_iff] at hdist
    have hs : q.2 ∈ closedBall s₀ r₀ := closedBall_subset_closedBall hrr hdist.2
    have hs' : q.2 ∈ ball s₀ (2 * r₀) := closedBall_subset_ball (by linarith) hs
    have hq' : q ∈ Icc (-T / 2) (T / 2) ×ˢ closedBall s₀ r₀ := by
      have hh := min_le_right r₀ (T / 8)
      have ht' := abs_le.mp hdist.1
      exact ⟨⟨by dsimp [r] at ht'; linarith [ht'.1],
        by dsimp [r] at ht'; linarith [ht'.2]⟩, hs⟩
    let ε := cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)
    have hε : 0 ≤ ε := cNorm_nonneg _ _ _
    have hε₁ : ε ≤ 1 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hgclose : ∀ s ∈ closedBall s₀ r₀,
        |g s - g₀ s| ≤ (Cr + Cf) * ε ∧
        ‖fderiv ℝ g s - fderiv ℝ g₀ s‖ ≤ (Cr + Cf) * ε := by
      intro s hs
      have hb' : Cr * cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤ (Cr + Cf) * ε :=
        mul_le_mul (by linarith) hnorm (cNorm_nonneg _ _ _) (by linarith)
      exact ⟨((hcloseg s hs).1).trans hb', ((hcloseg s hs).2).trans hb'⟩
    have hd := hderivative g Ψ ε hε hε₁ hg hΨ.smooth
      (fun s hs ↦ hLhalf (hroot s hs).2.1) hgclose
      (fun q hq ↦ ((hcloseΨ q hq).2).trans
        (mul_le_mul_of_nonneg_right (by linarith : Cf ≤ Cr + Cf) hε)) q hq'
    have he : Φ.augmentedProjection = sectionAugmentedProjection j ν g Ψ := by
      funext q; simp only [HamiltonFlow.augmentedProjection, hx, sectionAugmentedProjection]
    have he₀ : Φ₀.augmentedProjection = sectionAugmentedProjection j ν g₀ Ψ₀ := by
      funext q; simp only [HamiltonFlow.augmentedProjection, hx₀, sectionAugmentedProjection]
    refine ⟨?_, ?_⟩
    · let x := (transverseSectionState j ν (q.2, g q.2), q.1)
      let y := (transverseSectionState j ν (q.2, g₀ q.2), q.1)
      have hxQ : x ∈ Q := ⟨ball_subset_closedBall (hLhalf (hroot q.2 hs').2.1), hq'.1⟩
      have hyQ : y ∈ Q := ⟨ball_subset_closedBall (hinit₀ q.2 hs'), hq'.1⟩
      have hxy : ‖x - y‖ = |g q.2 - g₀ q.2| * ‖ν‖ := by
        change max ‖transverseSectionState j ν (q.2, g q.2) -
          transverseSectionState j ν (q.2, g₀ q.2)‖ ‖q.1 - q.1‖ = _
        rw [sub_self, norm_zero, max_eq_left (norm_nonneg _), norm_transverseSectionState_root_sub]
      have hlip : ‖Ψ₀ x - Ψ₀ y‖ ≤ (L₀ : ℝ) * (|g q.2 - g₀ q.2| * ‖ν‖) := by
        simpa only [dist_eq_norm, hxy] using hL₀.dist_le_mul x hxQ y hyQ
      have hbroot := (hcloseg q.2 hs).1.trans (mul_le_mul_of_nonneg_left hnorm hCr.le)
      have htstate := norm_add_le (Ψ x - Ψ₀ x) (Ψ₀ x - Ψ₀ y)
      rw [sub_add_sub_cancel] at htstate
      have hstate : ‖Ψ x - Ψ₀ y‖ ≤ C * ε := by
        have hh := hlip.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbroot (norm_nonneg ν)) L₀.coe_nonneg)
        have hf := (hcloseΨ x hxQ).1
        dsimp [C]
        nlinarith [mul_nonneg hJ.le hε]
      rw [he, he₀]
      change max ‖(Ψ x).1 - (Ψ₀ y).1‖ ‖q.2.2 - q.2.2‖ ≤ _
      rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)]
      exact (norm_fst_le (Ψ x - Ψ₀ y)).trans hstate
    · rw [he, he₀]
      apply hd.trans
      apply mul_le_mul_of_nonneg_right _ hε
      have hh : 0 ≤ (L₀ : ℝ) * Cr * ‖ν‖ := by positivity
      dsimp [C]
      linarith

end JanetCartan.HamiltonPhase
