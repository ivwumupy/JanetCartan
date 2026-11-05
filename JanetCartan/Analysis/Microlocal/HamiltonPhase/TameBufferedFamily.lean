module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameFamily

/-!
# Common buffered Hamilton phases with sharp tame estimates

For `app:lem:common-hamilton-phase`, choose the inverse buffers inside the
working ball of the actual tame flow family. This instantiates the inverse
estimate on the same flow and chart, with scalar-symbol order `m + 1`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

local instance tameBufferedFamilyNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tameBufferedFamilyNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

set_option maxHeartbeats 800000 in
/-- Common actual phases with sharp one-high inverse and phase bounds
(`app:lem:common-hamilton-phase`). The source balls, target, compact physical
and canonical boxes, symbol tolerance and constants are chosen before the
symbol. The implicit section, flow, normalized inverse gap and all analytic
budgets are constructed. Scalar-symbol order `m + 1` gives coefficient order
`m + 3` when the scalar symbol costs two coefficient derivatives.

This constructs the tame local family. Identifying it with the separately
constructed conic and finite-order continuous families on compatible buffers
remains a separate obligation; no such identification is asserted here. -/
theorem exists_commonTameBufferedHamiltonPhases
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r b ρ δ r₀ a c T : ℝ) (V : Set (E × (ℝ × U))) (B : ℕ → ℝ)
      (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < δ ∧ 0 < r₀ ∧ 0 < a ∧ 0 < c ∧
      4 * r₀ ≤ T ∧ 2 * r < r₀ ∧ (∀ m, 0 < B m) ∧
      MapsTo (transverseSectionState j ν)
        (closedBall s₀ (2 * r₀) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (closedBall z₀ R) ∧
      IsOpen V ∧ IsCompact (closure V) ∧
      closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ ⊆ V ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (g : InitialData U → ℝ) (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.sectionMap = j.toContinuousLinearMap ∧
          Φ.time = Ioo (-T) T ∧ Φ.parameters = ball s₀ (2 * r₀) ∧
          ContDiffOn ℝ ∞ g (ball s₀ (2 * r₀)) ∧
          (∀ s ∈ ball s₀ (2 * r₀), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
            c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) ∧
          (∀ s ∈ ball s₀ (2 * r₀), ∀ τ ∈ Icc (τ₀ - a) (τ₀ + a),
            H.h (transverseSectionState j ν (s, τ)) = s.2.1 ↔ g s = τ) ∧
          (∀ s ∈ ball s₀ (2 * r₀),
            (Φ.position (0, s), Φ.momentum (0, s)) = transverseSectionState j ν (s, g s)) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧ ContDiffOn ℝ ∞ (phase C.coordinates) V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ Φ.augmentedProjection q) -
              ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) ∧
          (∀ z ∈ V,
            HasFDerivAt (phase C.coordinates)
              (phaseDifferential (Φ.momentum (chartLift C.coordinates z)) (C.coordinates z)) z ∧
            H.h (z.1, gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1) = z.2.1) ∧
          (∀ u η, (0, (u, η)) ∈ C.source → phase C.coordinates (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          (∀ m : ℕ,
            cNorm (closedBall s₀ r ×ˢ Icc (-r) r) m
                (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) +
              cNorm (closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ) m C.coordinates +
              cNorm (closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ) m (phase C.coordinates) ≤
                B m * (1 + cNorm (closedBall z₀ R) (m + 1) H.h)) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨r₀, a, c, T, δ₀, L, F, Φ₀, hr₀, _ha, _hc, hrT, hδ₀, hL, hF,
      ht₀, hp₀, hj₀, hm₀, hΦ₀, _hmap, hfamily⟩ :=
    exists_commonTameHamiltonFlows H₀ hD hDH₀ hH₀ j ν horth hR hRD henergy htrans
  have hs₀ : s₀ ∈ Φ₀.parameters := hp₀.symm ▸ mem_ball_self (by positivity)
  have hv : ⟪ν, H₀.hp (j s₀.1, Φ₀.momentum (0, s₀))⟫_ℝ ≠ 0 := by
    rw [hm₀, real_inner_comm]
    exact htrans
  obtain ⟨A, _hA, d, hd, _hadmd, hgapd⟩ :=
    Φ₀.exists_augmentedProjection_derivative_gap j hj₀ ν horth hspan hs₀ hv
      ((hΦ₀.contDiffAt ((Φ₀.isOpen_time.prod Φ₀.isOpen_parameters).mem_nhds
        ⟨Φ₀.zero_mem_time, hs₀⟩)).of_le (by simp))
  let r := min d r₀ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : 3 * r ≤ d := by have hh := min_le_left d r₀; dsimp [r]; linarith
  have hrr : 3 * r < r₀ := by have hh := min_le_right d r₀; dsimp [r]; linarith
  let W := ball ((0 : ℝ), s₀) (3 * r)
  have hW : IsOpen W := isOpen_ball
  have hWr : W ⊆ closedBall ((0 : ℝ), s₀) r₀ :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hrr.le)
  have hadm : closedBall ((0 : ℝ), s₀) r₀ ⊆ Φ₀.time ×ˢ Φ₀.parameters := by
    intro q hq
    have hh := mem_closedBall.mp hq
    rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_le_iff] at hh
    have ht := abs_le.mp hh.1
    rw [ht₀, hp₀]
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      closedBall_subset_ball (by linarith) hh.2⟩
  have hgap : ∀ q ∈ W,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ₀.augmentedProjection q - (A : _ →L[ℝ] _))‖ ≤ 1 / 4 :=
    fun q hq ↦ hgapd q (closedBall_subset_closedBall hrd (ball_subset_closedBall hq))
  have hinner : closure (ball ((0 : ℝ), s₀) r) ⊆ ball ((0 : ℝ), s₀) (2 * r) :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  have hmid : ball ((0 : ℝ), s₀) (2 * r) ⊆ W := ball_subset_ball (by linarith)
  have hdiff₀ : ∀ q ∈ W, DifferentiableAt ℝ Φ₀.augmentedProjection q :=
    fun q hq ↦ (Φ₀.hasFDerivAt_augmentedProjection (hadm (hWr hq))).differentiableAt
  obtain ⟨ε, hε, b, hb, V, hV, hVc, hstable⟩ :=
    common_buffered_inverse_domains_of_c1_close
      ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
      isOpen_ball hinner hmid (convex_ball _ _) A hdiff₀ hgap
  have hzV : (j s₀.1, s₀.2) ∈ V := by
    obtain ⟨_, _, _, hi, _⟩ := hstable Φ₀.augmentedProjection hdiff₀
      (fun _ _ ↦ by simpa using hε.le) (fun _ _ ↦ by simpa using hε.le)
    have hh := hi (self_subset_cthickening _
      (mem_image_of_mem Φ₀.augmentedProjection (subset_closure (mem_ball_self hr))))
    simpa [HamiltonFlow.augmentedProjection, Φ₀.initial_position s₀ hs₀, hj₀] using hh
  obtain ⟨e, he, heV⟩ := Metric.isOpen_iff.mp hV _ hzV
  let K := closedBall (j s₀.1) (e / 2) ×ˢ closedBall s₀.2 (e / 2)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKV : K ⊆ V := by
    intro z hz
    apply heV
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hz.1).trans_lt (by linarith),
      (mem_closedBall.mp hz.2).trans_lt (by linarith)⟩
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  have hN : 0 ≤ N := norm_nonneg _
  let η := min ε (1 / (4 * (N + 1)))
  have hη : 0 < η := lt_min hε (by positivity)
  have hNη : N * η ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * (N + 1) by positivity)).mp
      (show η ≤ 1 / (4 * (N + 1)) from min_le_right _ _)
    nlinarith [hη.le]
  let M := F 1 * (2 + cNorm (closedBall z₀ R) 2 H₀.h)
  have hM : 0 ≤ M := mul_nonneg (hF 1).le
    (by have hh := cNorm_nonneg (closedBall z₀ R) 2 H₀.h; linarith)
  have hclosedW : closedBall ((0 : ℝ), s₀) (2 * r) ⊆ W :=
    closedBall_subset_ball (by linarith)
  choose I hI hinverse using fun m ↦ exists_coordinates_phase_cNorm_bound
    ((0 : ℝ), s₀) (by positivity : 0 < 2 * r) hW hclosedW hK A hM m
  refine ⟨r, b, e / 2, min δ₀ (min 1 (η / L)), r₀, a, c, T, V,
    (fun m ↦ F m + I m * (1 + F m)), A, hr, hb, half_pos he,
    lt_min hδ₀ (lt_min zero_lt_one (div_pos hη hL)),
    hr₀, _ha, _hc, hrT, (by linarith),
    (fun m ↦ add_pos (hF m) (mul_pos (hI m) (by linarith [hF m]))),
    _hmap, hV, hVc, hKV, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨g, Φ, ht, hp, hj, _hg, _hroot, _huniq, hx, hm, _hstart, _hrange, hbound, hclose⟩ :=
    hfamily H hDH hH (hsmall.trans (min_le_left _ _))
  have hadm' : closedBall ((0 : ℝ), s₀) r₀ ⊆ Φ.time ×ˢ Φ.parameters := by
    simpa only [ht, hp, ht₀, hp₀] using hadm
  have hproj : ContDiffOn ℝ ∞ Φ.augmentedProjection (Φ.time ×ˢ Φ.parameters) :=
    hx.prodMk contDiff_snd.snd.contDiffOn
  have hdiff : ∀ q ∈ W, DifferentiableAt ℝ Φ.augmentedProjection q :=
    fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection (hadm' (hWr hq))).differentiableAt
  have hsmallη : L * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ η := by
    have hh := (le_div_iff₀ hL).mp
      (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have hderiv : ∀ q ∈ W, ‖fderiv ℝ Φ.augmentedProjection q -
      fderiv ℝ Φ₀.augmentedProjection q‖ ≤ η :=
    fun q hq ↦ ((hclose q (hWr hq)).2).trans hsmallη
  obtain ⟨hinj, _hlip, _hcompact, hi, ho⟩ := hstable Φ.augmentedProjection hdiff
    (fun q hq ↦ (hderiv q hq).trans (min_le_left _ _))
    (fun q hq ↦ ((hclose q (hWr (hmid (hinner hq)))).1.trans hsmallη).trans (min_le_left _ _))
  have hpre : Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩ W ⊆
      ball ((0 : ℝ), s₀) (2 * r) := by
    intro q hq
    obtain ⟨q', hq', heq⟩ := ho hq.1
    exact (hinj hq.2 (hmid hq') heq.symm).symm ▸ hq'
  have hhalf : ∀ q ∈ W,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
          ≤ 1 / 2 := by
    intro q hq
    apply normalized_derivative_gap_of_perturbation A (A := fderiv ℝ Φ₀.augmentedProjection q)
    · have heq : (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ₀.augmentedProjection q - (A : _ →L[ℝ] _)) =
          (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
            (fderiv ℝ Φ₀.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U) := by
        apply ContinuousLinearMap.ext
        intro v
        simp
      exact heq ▸ hgap q hq
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (hderiv q hq) hN).trans hNη)
  have himage : V ⊆ Φ.augmentedProjection '' W := fun z hz ↦
    image_mono hmid (ho (self_subset_cthickening _ (subset_closure hz)))
  obtain ⟨C, hCt, hCs, hC⟩ := Φ.exists_smoothBufferedProjectionChart
    hW (convex_ball _ _) hV (hWr.trans hadm') himage hx A hhalf
  have hbuffer : C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) := by
    intro q hq
    rw [hCs] at hq
    exact hpre ⟨self_subset_cthickening _ (subset_closure hq.2), hq.1⟩
  have hforward : ∀ m, cNorm (closedBall ((0 : ℝ), s₀) (2 * r)) m Φ.augmentedProjection ≤
      F m * (1 + cNorm (closedBall z₀ R) (m + 1) H.h) := by
    intro m
    have hmono := cNorm_mono_set_of_contDiffAt
      (closedBall_subset_closedBall (by linarith : 2 * r ≤ r₀)) (isCompact_closedBall _ _)
      (fun q hq ↦ (hproj.contDiffAt
        ((Φ.isOpen_time.prod Φ.isOpen_parameters).mem_nhds (hadm' hq))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    exact hmono.trans ((le_add_of_nonneg_left (cNorm_nonneg _ _ _)).trans (hbound m))
  have hlow : cNorm (closedBall z₀ R) 2 H.h ≤ 1 + cNorm (closedBall z₀ R) 2 H₀.h := by
    have hh := cNorm_add_le_of_contDiffAt (isCompact_closedBall z₀ R)
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
      (fun z hz ↦ (hH₀.contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
    have heq : (fun z ↦ H.h z - H₀.h z) + H₀.h = H.h := by funext z; simp
    rw [heq] at hh
    have hsmall₁ := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hmono := cNorm_mono_order (s := closedBall z₀ R)
      (f := fun z ↦ H.h z - H₀.h z) (by omega : 2 ≤ 3)
    linarith
  have hlowproj : cNorm (closedBall ((0 : ℝ), s₀) (2 * r)) 1 Φ.augmentedProjection ≤ M := by
    apply (hforward 1).trans
    apply mul_le_mul_of_nonneg_left _ (hF 1).le
    linarith
  refine ⟨g, Φ, C, hj, ht, hp, _hg, _hroot, _huniq, _hstart, _hrange, hx, hm, hCt, hCs, hbuffer, hC,
    hCt ▸ C.contDiffOn_phase (hCt.symm ▸ hC), hi, ho, hpre, hhalf, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨C.hasFDerivAt_phase (hCt.symm ▸ hz), C.eikonal (hCt.symm ▸ hz)⟩
  · intro u η hs
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using C.initial_value hs
  · intro m
    have hb := hinverse m H Φ C (by rw [hCt]; exact hKV)
      (hproj.mono (hWr.trans hadm')) (hCt.symm ▸ hC) hlowproj
      (fun z hz ↦ ball_subset_closedBall (hbuffer (C.maps_to_source z (hCt.symm ▸ hKV hz))))
      (fun q hq ↦ hhalf q (hclosedW hq))
    have hn := cNorm_nonneg (closedBall z₀ R) (m + 1) H.h
    have hbudget : 1 + cNorm (closedBall ((0 : ℝ), s₀) (2 * r)) m Φ.augmentedProjection ≤
        (1 + F m) * (1 + cNorm (closedBall z₀ R) (m + 1) H.h) := by nlinarith [hforward m]
    have hi' := hb.trans (mul_le_mul_of_nonneg_left hbudget (hI m).le)
    have hzero := cNorm_nonneg K m (chartLift C.coordinates)
    have hsmallState : cNorm (closedBall s₀ r ×ˢ Icc (-r) r) m
        (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) ≤
        F m * (1 + cNorm (closedBall z₀ R) (m + 1) H.h) := by
      have hsub : closedBall s₀ r ×ˢ Icc (-r) r ⊆ closedBall s₀ r₀ ×ˢ Icc (-r₀) r₀ := by
        intro q hq
        exact ⟨closedBall_subset_closedBall (by linarith) hq.1,
          ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
      have hmono := cNorm_mono_set_of_contDiffAt hsub
        ((isCompact_closedBall _ _).prod isCompact_Icc)
        (f := fun q : InitialData U × ℝ ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1)))
        (by
          intro q hq
          have hq' : (q.2, q.1) ∈ Φ.time ×ˢ Φ.parameters := by
            rw [ht, hp]
            exact ⟨⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩,
              closedBall_subset_ball (by linarith) hq.1⟩
          exact (((hx.prodMk hm).contDiffAt
            ((Φ.isOpen_time.prod Φ.isOpen_parameters).mem_nhds hq')).comp q
              (contDiff_snd.prodMk contDiff_fst).contDiffAt).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
      exact hmono.trans ((le_add_of_nonneg_right (cNorm_nonneg _ _ _)).trans (hbound m))
    dsimp only [K] at hi' hzero
    nlinarith only [hi', hzero, hsmallState]

end JanetCartan.HamiltonPhase
