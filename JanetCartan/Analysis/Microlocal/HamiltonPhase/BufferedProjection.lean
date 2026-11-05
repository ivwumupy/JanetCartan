module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Construction
public import JanetCartan.Analysis.Calculus.BufferedInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Buffered Hamilton projection domains

For `app:lem:common-hamilton-phase`, transversality gives the central
isomorphism and continuity of the actual augmented-projection derivative gives
the quarter gap on a smaller neighborhood. The quantitative inverse theorem
`app:lem:buffered-inverse-stability` then supplies common target buffers.

The perturbation hypotheses below are explicit C¹ bounds on the projections.
Deriving these bounds from a neighborhood of symbols, and constructing the
common smooth phase charts, remain the responsibility of the caller.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

/-- The initial transverse Hamilton velocity determines an isomorphism `A`.
Continuity of the actual derivative, rather than an assumed gap, gives a closed
ball on which the normalized gap is at most one quarter
(`app:lem:common-hamilton-phase`, `app:lem:buffered-inverse-stability`). -/
theorem HamiltonFlow.exists_augmentedProjection_derivative_gap
    (j : U →ₗᵢ[ℝ] E) (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (ν : E) (horth : ∀ u : U, ⟪ν, j u⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} (hs₀ : s₀ ∈ Φ.parameters)
    (hv : ⟪ν, H.hp (j s₀.1, Φ.momentum ((0 : ℝ), s₀))⟫_ℝ ≠ 0)
    (hc : ContDiffAt ℝ 1 Φ.position ((0 : ℝ), s₀)) :
    ∃ A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)),
      HasFDerivAt Φ.augmentedProjection (A : _ →L[ℝ] _) ((0 : ℝ), s₀) ∧
      ∃ ρ > 0, closedBall ((0 : ℝ), s₀) ρ ⊆ Φ.time ×ˢ Φ.parameters ∧
        ∀ q ∈ closedBall ((0 : ℝ), s₀) ρ,
          ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
            (fderiv ℝ Φ.augmentedProjection q - (A : _ →L[ℝ] _))‖ ≤ 1 / 4 := by
  obtain ⟨A, hA⟩ := Φ.exists_initialAugmentedProjectionEquiv j hj ν horth hspan hs₀ hv
  have haug : ContDiffAt ℝ 1 Φ.augmentedProjection ((0 : ℝ), s₀) :=
    hc.prodMk contDiffAt_snd.snd
  have hn : ContinuousAt (fun q ↦ ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
      (fderiv ℝ Φ.augmentedProjection q - (A : _ →L[ℝ] _))‖) ((0 : ℝ), s₀) :=
    (continuousAt_const.clm_comp
      ((haug.continuousAt_fderiv one_ne_zero).sub continuousAt_const)).norm
  have hsmall := hn.eventually (gt_mem_nhds (show
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection ((0 : ℝ), s₀) - (A : _ →L[ℝ] _))‖ < (1 / 4 : ℝ) by
    rw [hA.fderiv, sub_self, ContinuousLinearMap.comp_zero]
    rw [ContinuousLinearMap.opNorm_zero]
    norm_num))
  have hadm : Φ.time ×ˢ Φ.parameters ∈ 𝓝 ((0 : ℝ), s₀) :=
    (Φ.isOpen_time.prod Φ.isOpen_parameters).mem_nhds ⟨Φ.zero_mem_time, hs₀⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (Filter.Eventually.and hadm hsmall)
  have hsub : closedBall ((0 : ℝ), s₀) (R / 2) ⊆ ball ((0 : ℝ), s₀) R :=
    closedBall_subset_ball (by linarith)
  exact ⟨A, hA, R / 2, by positivity,
    fun q hq ↦ (hball q (hsub hq)).1,
    fun q hq ↦ (hball q (hsub hq)).2.le⟩

/-- Explicit nested source balls and a common target for C¹-close augmented
projections (`app:lem:common-hamilton-phase`, `app:lem:buffered-inverse-stability`).
The inner, buffered, and outer source radii are `r`, `2 * r`, and `3 * r`.
All closures are compact, and even the outer closure lies in the flow domain.

The stability conclusion is stated for arbitrary maps `f`, so it applies in
particular to every perturbed Hamilton flow's augmented projection on these
fixed domains. The entire preimage of the buffered target, restricted only to
the outer source ball, lies in the middle ball. No inverse-domain conclusion or
reference derivative-gap assumption is an input. -/
theorem HamiltonFlow.exists_bufferedProjection_domains
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
    (j : U →ₗᵢ[ℝ] E) (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (ν : E) (horth : ∀ u : U, ⟪ν, j u⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} (hs₀ : s₀ ∈ Φ.parameters)
    (hv : ⟪ν, H.hp (j s₀.1, Φ.momentum ((0 : ℝ), s₀))⟫_ℝ ≠ 0)
    (hc : ContDiffAt ℝ 1 Φ.position ((0 : ℝ), s₀)) :
    ∃ A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)),
      HasFDerivAt Φ.augmentedProjection (A : _ →L[ℝ] _) ((0 : ℝ), s₀) ∧
      ∃ r > 0,
        IsCompact (closure (ball ((0 : ℝ), s₀) r)) ∧
        IsCompact (closure (ball ((0 : ℝ), s₀) (2 * r))) ∧
        IsCompact (closure (ball ((0 : ℝ), s₀) (3 * r))) ∧
        closure (ball ((0 : ℝ), s₀) r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
        closure (ball ((0 : ℝ), s₀) (2 * r)) ⊆ ball ((0 : ℝ), s₀) (3 * r) ∧
        closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
        Convex ℝ (ball ((0 : ℝ), s₀) (3 * r)) ∧
        (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
          ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
            (fderiv ℝ Φ.augmentedProjection q - (A : _ →L[ℝ] _))‖ ≤ 1 / 4) ∧
        ∃ ε > 0, ∃ δ > 0, ∃ V : Set (E × (ℝ × U)),
          IsOpen V ∧ IsCompact (closure V) ∧ (j s₀.1, s₀.2) ∈ V ∧
          ∀ f : (ℝ × InitialData U) → (E × (ℝ × U)),
            (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r), DifferentiableAt ℝ f q) →
            (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
              ‖fderiv ℝ f q - fderiv ℝ Φ.augmentedProjection q‖ ≤ ε) →
            (∀ q ∈ closure (ball ((0 : ℝ), s₀) r),
              ‖f q - Φ.augmentedProjection q‖ ≤ ε) →
            InjOn f (ball ((0 : ℝ), s₀) (3 * r)) ∧
            (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r), ∀ q' ∈ ball ((0 : ℝ), s₀) (3 * r),
              ‖q - q'‖ ≤
                (2 * (‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ + 1)) *
                  ‖f q - f q'‖) ∧
            IsCompact (f '' closure (ball ((0 : ℝ), s₀) r)) ∧
            cthickening δ (f '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
            cthickening δ (closure V) ⊆ f '' ball ((0 : ℝ), s₀) (2 * r) ∧
            f ⁻¹' cthickening δ (closure V) ∩ ball ((0 : ℝ), s₀) (3 * r) ⊆
              ball ((0 : ℝ), s₀) (2 * r) ∧
            f ⁻¹' V ∩ ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) := by
  obtain ⟨A, hA, ρ, hρ, hadm, hgap⟩ :=
    Φ.exists_augmentedProjection_derivative_gap j hj ν horth hspan hs₀ hv hc
  let r := ρ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have houter : closedBall ((0 : ℝ), s₀) (3 * r) ⊆ closedBall ((0 : ℝ), s₀) ρ :=
    closedBall_subset_closedBall (by dsimp [r]; linarith)
  have hK : IsCompact (closure (ball ((0 : ℝ), s₀) r)) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hK₁ : closure (ball ((0 : ℝ), s₀) r) ⊆ ball ((0 : ℝ), s₀) (2 * r) :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  have h₁D : ball ((0 : ℝ), s₀) (2 * r) ⊆ ball ((0 : ℝ), s₀) (3 * r) :=
    ball_subset_ball (by linarith)
  have hDadm : ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ.time ×ˢ Φ.parameters :=
    ball_subset_closedBall.trans (houter.trans hadm)
  have hdiff : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      DifferentiableAt ℝ Φ.augmentedProjection q :=
    fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection (hDadm hq)).differentiableAt
  have hgapD : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q - (A : _ →L[ℝ] _))‖ ≤ 1 / 4 :=
    fun q hq ↦ hgap q (houter (ball_subset_closedBall hq))
  obtain ⟨ε, hε, δ, hδ, V, hV, hVc, hstable⟩ :=
    common_buffered_inverse_domains_of_c1_close hK isOpen_ball hK₁ h₁D
      (convex_ball _ _) A hdiff hgapD
  have hz : (j s₀.1, s₀.2) ∈ V := by
    obtain ⟨_, _, _, hinner, _⟩ := hstable Φ.augmentedProjection hdiff
      (fun _ _ ↦ by simpa using hε.le) (fun _ _ ↦ by simpa using hε.le)
    have hmem : Φ.augmentedProjection ((0 : ℝ), s₀) ∈ V :=
      hinner (self_subset_cthickening _
        (mem_image_of_mem _ (subset_closure (mem_ball_self hr))))
    simpa [HamiltonFlow.augmentedProjection, Φ.initial_position s₀ hs₀, hj] using hmem
  refine ⟨A, hA, r, hr, hK,
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
    hK₁, closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith)),
    closure_ball_subset_closedBall.trans (houter.trans hadm), convex_ball _ _, hgapD,
    ε, hε, δ, hδ, V, hV, hVc, hz, ?_⟩
  intro f hf hderiv hvalue
  obtain ⟨hinj, hlower, hcompact, hinner, htarget⟩ := hstable f hf hderiv hvalue
  have hpre : f ⁻¹' cthickening δ (closure V) ∩ ball ((0 : ℝ), s₀) (3 * r) ⊆
      ball ((0 : ℝ), s₀) (2 * r) := by
    intro q hq
    obtain ⟨q', hq', heq⟩ := htarget hq.1
    have hqq' : q = q' := hinj hq.2 (h₁D hq') heq.symm
    exact hqq'.symm ▸ hq'
  exact ⟨hinj, hlower, hcompact, hinner, htarget, hpre,
    fun q hq ↦ hpre ⟨self_subset_cthickening _ (subset_closure hq.1), hq.2⟩⟩

end JanetCartan.HamiltonPhase
