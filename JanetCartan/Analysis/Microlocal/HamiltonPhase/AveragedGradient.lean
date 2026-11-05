module

public import JanetCartan.Analysis.Calculus.PhaseQuotient
public import JanetCartan.Analysis.Calculus.BufferedInverse
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.BufferedConstruction
public import JanetCartan.Analysis.ODE.PositiveTransport.ParametricIntegral

/-!
# Averaged Hamilton gradients on buffered charts

The local, single-symbol averaged-gradient construction of
`app:lem:common-hamilton-phase` and `app:ch_regular_base:eq:averaged-gradient`.
The phase and its gradient are those of the actual Hamilton projection chart.
-/

@[expose] public noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.HamiltonPhase.ProjectionChart

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)

/-- The integrand in `app:ch_regular_base:eq:averaged-gradient` is actual
transported Hamilton momentum along the physical segment. -/
theorem averagedPhaseGradient_eq_integral_chartMomentum {x y : E} {η : ℝ × U}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (y + t • (x - y), η) ∈ C.target) :
    averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y =
      ∫ t in (0 : ℝ)..1, C.chartMomentum (y + t • (x - y), η) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact C.gradient_phase_eq_chartMomentum (hseg t (by simpa using ht))

variable [FiniteDimensional ℝ U]

/-- Differentiate `app:ch_regular_base:eq:averaged-gradient` in the canonical
variable on an open domain whose physical segments lie in the actual chart.
Compactness of the integration interval supplies domination. -/
theorem hasFDerivAt_averagedPhaseGradient
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {V : Set (ℝ × U)} (hV : IsOpen V) {x y : E}
    (hseg : ∀ η ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C.target) {η : ℝ × U} (hη : η ∈ V) :
    HasFDerivAt
      (fun η ↦ averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y)
      (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative (y + t • (x - y), η)) η := by
  let F : ℝ × (ℝ × U) → E := fun q ↦ C.chartMomentum (y + q.1 • (x - y), q.2)
  have hF : ∀ q ∈ uIcc (0 : ℝ) 1 ×ˢ V, ContDiffAt ℝ ∞ F q := by
    intro q hq
    exact ((C.contDiffOn_chartMomentum hp hC).contDiffAt
      (C.isOpen_target.mem_nhds (hseg q.2 hq.2 q.1 (by simpa using hq.1)))).comp
        (g := C.chartMomentum) (f := fun q : ℝ × (ℝ × U) ↦
          (y + q.1 • (x - y), q.2)) q
        ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk contDiffAt_snd)
  have hd := hasFDerivAt_fixedIntervalIntegral hV hF hη
  have he : (∫ t in (0 : ℝ)..1,
      (fderiv ℝ F (t, η)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × U))) =
      ∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative (y + t • (x - y), η) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hm := hseg η hη t ht'
    have h₁ := ((hF (t, η) ⟨ht, hη⟩).differentiableAt (by simp)).hasFDerivAt.comp η
      (hasFDerivAt_prodMk_right t η)
    have h₂ := (((C.contDiffOn_chartMomentum hp hC).contDiffAt
      (C.isOpen_target.mem_nhds hm)).differentiableAt (by simp)).hasFDerivAt.comp η
        (hasFDerivAt_prodMk_right (y + t • (x - y)) η)
    exact h₁.unique h₂ |>.trans (C.mixedMomentumDerivative_eq hp hC hm).symm
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hη] with θ hθ
  exact C.averagedPhaseGradient_eq_integral_chartMomentum (hseg θ hθ)

/-- The normalized derivative gap survives averaging along a physical segment
(`app:lem:common-hamilton-phase`). -/
theorem averagedPhaseGradient_derivative_gap
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {V : Set (ℝ × U)} (hV : IsOpen V) {x y : E}
    (hseg : ∀ η ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C.target)
    (A : (ℝ × U) ≃L[ℝ] E) {η : ℝ × U} (hη : η ∈ V)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (C.mixedMomentumDerivative (y + t • (x - y), η)) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ)) :
    ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (fderiv ℝ (fun η ↦ averagedPhaseGradient
        (fun η x ↦ phase C.coordinates (x, η)) η x y) η) -
      ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ) := by
  let : NormedSpace ℝ (ℝ × U) := inferInstance
  let : NormedAddCommGroup ((ℝ × U) →L[ℝ] E) := inferInstance
  let : NormedAddCommGroup ((ℝ × U) →L[ℝ] (ℝ × U)) := inferInstance
  rw [(C.hasFDerivAt_averagedPhaseGradient hp hC hV hseg hη).fderiv]
  have hc : ContinuousOn (fun t : ℝ ↦ C.mixedMomentumDerivative
      (y + t • (x - y), η)) (Icc 0 1) :=
    (C.continuousOn_mixedMomentumDerivative hp hC).comp (by fun_prop) (hseg η hη)
  let L := (ContinuousLinearMap.compL ℝ (ℝ × U) E (ℝ × U))
    (A.symm : E →L[ℝ] (ℝ × U))
  have hi : IntervalIntegrable (fun t : ℝ ↦ C.mixedMomentumDerivative
      (y + t • (x - y), η)) volume 0 1 := hc.intervalIntegrable_of_Icc zero_le_one
  change ‖L (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative
    (y + t • (x - y), η)) - ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ _
  have hL : (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
      (y + t • (x - y), η))) = L (∫ t in (0 : ℝ)..1,
        C.mixedMomentumDerivative (y + t • (x - y), η)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) L hi
  rw [← hL]
  have hiL : IntervalIntegrable (fun t ↦ L (C.mixedMomentumDerivative
      (y + t • (x - y), η))) volume 0 1 :=
    ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
  have he : (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
      (y + t • (x - y), η)) - ContinuousLinearMap.id ℝ (ℝ × U)) =
      (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
        (y + t • (x - y), η))) - ContinuousLinearMap.id ℝ (ℝ × U) := by
    rw [intervalIntegral.integral_sub hiL intervalIntegrable_const]
    simp
  rw [← he]
  simpa [L] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := (1 / 4 : ℝ))
    (fun t ht ↦ hgap t (by simpa using uIoc_subset_uIcc ht))

variable [FiniteDimensional ℝ E]

/-- Joint smoothness in both endpoints and the canonical parameter on a convex
physical chart (`app:ch_regular_base:eq:averaged-gradient`). -/
theorem contDiffOn_averagedPhaseGradient
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {V : Set (ℝ × U)} (hB : IsOpen B) (hconv : Convex ℝ B)
    (hV : IsOpen V) (hBV : B ×ˢ V ⊆ C.target) :
    ContDiffOn ℝ ∞ (fun q : (E × E) × (ℝ × U) ↦
      averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) q.2 q.1.1 q.1.2)
      ((B ×ˢ B) ×ˢ V) := by
  let F : ℝ × ((E × E) × (ℝ × U)) → E := fun q ↦
    C.chartMomentum (q.2.1.2 + q.1 • (q.2.1.1 - q.2.1.2), q.2.2)
  have hF : ∀ q ∈ uIcc (0 : ℝ) 1 ×ˢ ((B ×ˢ B) ×ˢ V), ContDiffAt ℝ ∞ F q := by
    intro q hq
    have hm := hBV (a := (q.2.1.2 + q.1 • (q.2.1.1 - q.2.1.2), q.2.2))
      ⟨hconv.add_smul_sub_mem hq.2.1.2 hq.2.1.1
      (by simpa using hq.1), hq.2.2⟩
    exact ((C.contDiffOn_chartMomentum hp hC).contDiffAt (C.isOpen_target.mem_nhds hm)).comp
      (g := C.chartMomentum) (f := fun q : ℝ × ((E × E) × (ℝ × U)) ↦
        (q.2.1.2 + q.1 • (q.2.1.1 - q.2.1.2), q.2.2)) q (by fun_prop)
  apply (contDiffOn_fixedIntervalIntegral ((hB.prod hB).prod hV) hF).congr
  intro q hq
  exact C.averagedPhaseGradient_eq_integral_chartMomentum
    (fun t ht ↦ hBV ⟨hconv.add_smul_sub_mem hq.1.2 hq.1.1 ht, hq.2⟩)

/-- Shrink the mixed-Hessian neighborhood to positive physical and canonical
balls, with closed outer balls still inside that neighborhood. Every segment
between points in the physical ball therefore remains admissible
(`app:lem:common-hamilton-phase`). -/
theorem exists_mixedMomentumDerivative_balls
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    ∃ (A : (ℝ × U) ≃L[ℝ] E) (r : ℝ), 0 < r ∧
      (A : (ℝ × U) →L[ℝ] E) = C.mixedMomentumDerivative z ∧
      closedBall z.1 (3 * r) ×ˢ closedBall z.2 (3 * r) ⊆ C.target ∧
      ∀ x ∈ closedBall z.1 (3 * r), ∀ η ∈ closedBall z.2 (3 * r),
        ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative (x, η)) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨A, V, hA, hV, hzV, hVT, hgap⟩ :=
    C.exists_mixedMomentumDerivative_neighborhood hp hC hz
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV z hzV
  have hsub : closedBall z.1 (3 * (ε / 4)) ×ˢ closedBall z.2 (3 * (ε / 4)) ⊆ V := by
    intro w hw
    apply hεV
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · exact (mem_closedBall.mp hw.1).trans_lt (by linarith)
    · exact (mem_closedBall.mp hw.2).trans_lt (by linarith)
  exact ⟨A, ε / 4, by positivity, hA, hsub.trans hVT,
    fun x hx η hη ↦ hgap (x, η) (hsub ⟨hx, hη⟩)⟩

/-- The canonical derivative is jointly continuous in both physical endpoints
and the canonical variable (`app:ch_regular_base:eq:averaged-gradient`). -/
theorem continuousOn_canonicalFDeriv_averagedPhaseGradient
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {V : Set (ℝ × U)} (hB : IsOpen B) (hconv : Convex ℝ B)
    (hV : IsOpen V) (hBV : B ×ˢ V ⊆ C.target) :
    ContinuousOn (fun q : (E × E) × (ℝ × U) ↦ fderiv ℝ
      (fun η ↦ averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η q.1.1 q.1.2)
      q.2) ((B ×ˢ B) ×ˢ V) := by
  let F : (E × E) × (ℝ × U) → E := fun q ↦
    averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) q.2 q.1.1 q.1.2
  have hs : ContDiffOn ℝ ∞ F ((B ×ˢ B) ×ˢ V) :=
    C.contDiffOn_averagedPhaseGradient hp hC hB hconv hV hBV
  have ho := (hB.prod hB).prod hV
  apply ((hs.continuousOn_fderiv_of_isOpen ho (by simp)).clm_comp
    (continuousOn_const (c := ContinuousLinearMap.inr ℝ (E × E) (ℝ × U)))).congr
  intro q hq
  exact (((hs.contDiffAt (ho.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp
    (g := F) (f := fun η ↦ (q.1, η)) q.2 (hasFDerivAt_prodMk_right q.1 q.2)).fderiv

/-- Local single-symbol form of `app:lem:common-hamilton-phase`: one physical
ball and three nested canonical balls support all averaged gradients, with a
uniform normalized derivative gap, injectivity, and a common buffered inverse
domain. The entire preimage in the outer canonical ball of the buffered target
lies in the middle ball. The derivative formula and all perturbation bounds
are proved from smooth chart momentum, rather than assumed. -/
theorem exists_averagedPhaseGradient_buffered_domains
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    let Ξ : E → E → (ℝ × U) → E := fun x y η ↦
      averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y
    ∃ (A : (ℝ × U) ≃L[ℝ] E) (ρ r δ : ℝ) (V : Set E),
      0 < ρ ∧ 0 < r ∧ 0 < δ ∧ IsOpen V ∧ IsCompact (closure V) ∧
      (A : (ℝ × U) →L[ℝ] E) = C.mixedMomentumDerivative z ∧
      ∀ x ∈ ball z.1 ρ, ∀ y ∈ ball z.1 ρ,
        (∀ η ∈ ball z.2 (3 * r), ∀ t ∈ Icc (0 : ℝ) 1,
          (y + t • (x - y), η) ∈ C.target) ∧
        (∀ η ∈ ball z.2 (3 * r), HasFDerivAt (Ξ x y)
          (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative (y + t • (x - y), η)) η) ∧
        (∀ η ∈ ball z.2 (3 * r),
          ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
            ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ)) ∧
        InjOn (Ξ x y) (ball z.2 (3 * r)) ∧
        (∀ η ∈ ball z.2 (3 * r), ∀ θ ∈ ball z.2 (3 * r),
          ‖η - θ‖ / 2 ≤ ‖A.symm (Ξ x y η - Ξ x y θ)‖) ∧
        IsCompact (Ξ x y '' closedBall z.2 r) ∧
        cthickening δ (Ξ x y '' closedBall z.2 r) ⊆ V ∧
        cthickening δ (closure V) ⊆ Ξ x y '' ball z.2 (2 * r) ∧
        (Ξ x y) ⁻¹' cthickening δ (closure V) ∩ ball z.2 (3 * r) ⊆
          ball z.2 (2 * r) := by
  let Ξ : E → E → (ℝ × U) → E := fun x y η ↦
    averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y
  obtain ⟨A, R, hR, hA, hsub, hgap⟩ := C.exists_mixedMomentumDerivative_balls hp hC hz
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : closedBall z.2 (3 * r) ⊆ ball z.2 (3 * R) :=
    closedBall_subset_ball (by dsimp [r]; linarith)
  have hBB : ball z.1 (3 * R) ×ˢ ball z.2 (3 * R) ⊆ C.target :=
    (Set.prod_mono ball_subset_closedBall ball_subset_closedBall).trans hsub
  have hseg (x) (hx : x ∈ ball z.1 (3 * R)) (y) (hy : y ∈ ball z.1 (3 * R)) :
      ∀ η ∈ ball z.2 (3 * R), ∀ t ∈ Icc (0 : ℝ) 1,
        (y + t • (x - y), η) ∈ C.target :=
    fun η hη t ht ↦ hBB ⟨(convex_ball _ _).add_smul_sub_mem hy hx ht, hη⟩
  have hd (x) (hx : x ∈ ball z.1 (3 * R)) (y) (hy : y ∈ ball z.1 (3 * R))
      (η) (hη : η ∈ ball z.2 (3 * R)) :=
    C.hasFDerivAt_averagedPhaseGradient hp hC isOpen_ball (hseg x hx y hy) hη
  have hg (x) (hx : x ∈ ball z.1 (3 * R)) (y) (hy : y ∈ ball z.1 (3 * R))
      (η) (hη : η ∈ ball z.2 (3 * R)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ) := by
    apply C.averagedPhaseGradient_derivative_gap hp hC isOpen_ball (hseg x hx y hy) A hη
    intro t ht
    exact hgap _ (ball_subset_closedBall ((convex_ball _ _).add_smul_sub_mem hy hx ht))
      η (ball_subset_closedBall hη)
  have hzB : z.1 ∈ ball z.1 (3 * R) := mem_ball_self (by positivity)
  have h₁D : ball z.2 (2 * r) ⊆ ball z.2 (3 * r) := ball_subset_ball (by linarith)
  have hDR : ball z.2 (3 * r) ⊆ ball z.2 (3 * R) := ball_subset_closedBall.trans hsmall
  obtain ⟨δ, hδ, V, hV, hVc, hstable⟩ := common_buffered_inverse_domains
    (isCompact_closedBall z.2 r) isOpen_ball
    (closedBall_subset_ball (by linarith : r < 2 * r)) h₁D (convex_ball _ _) A
    (fun η hη ↦ (hd z.1 hzB z.1 hzB η (hDR hη)).differentiableAt)
    (fun η hη ↦ hg z.1 hzB z.1 hzB η (hDR hη))
  let F : (E × E) × (ℝ × U) → E := fun q ↦ Ξ q.1.1 q.1.2 q.2
  let D : (E × E) × (ℝ × U) → (ℝ × U) →L[ℝ] E :=
    fun q ↦ fderiv ℝ (Ξ q.1.1 q.1.2) q.2
  have hcF : ContinuousOn F
      ((ball z.1 (3 * R) ×ˢ ball z.1 (3 * R)) ×ˢ ball z.2 (3 * R)) :=
    (C.contDiffOn_averagedPhaseGradient hp hC isOpen_ball (convex_ball _ _) isOpen_ball hBB).continuousOn
  have hcD : ContinuousOn D
      ((ball z.1 (3 * R) ×ˢ ball z.1 (3 * R)) ×ˢ ball z.2 (3 * R)) :=
    C.continuousOn_canonicalFDeriv_averagedPhaseGradient hp hC
      isOpen_ball (convex_ball _ _) isOpen_ball hBB
  have hnear : ∀ᶠ p : E × E in 𝓝 (z.1, z.1), ∀ η ∈ closedBall z.2 (3 * r),
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (D (p, η) - D ((z.1, z.1), η))‖ ≤ (1 / 4 : ℝ) ∧
      ‖F (p, η) - F ((z.1, z.1), η)‖ ≤ δ := by
    apply (isCompact_closedBall z.2 (3 * r)).eventually_forall_of_forall_eventually
    intro η hη
    have hm : ((z.1, z.1), η) ∈
        ((ball z.1 (3 * R) ×ˢ ball z.1 (3 * R)) ×ˢ ball z.2 (3 * R)) :=
      ⟨⟨hzB, hzB⟩, hsmall hη⟩
    have hn := ((isOpen_ball.prod isOpen_ball).prod isOpen_ball).mem_nhds hm
    have hc₁ := hcD.continuousAt hn
    have hc₂ := hcF.continuousAt hn
    have hproj : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦ ((z.1, z.1), q.2))
        ((z.1, z.1), η) := continuousAt_const.prodMk continuousAt_snd
    have hdN : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦
        ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (D q - D ((z.1, z.1), q.2))‖)
        ((z.1, z.1), η) :=
      (continuousAt_const.clm_comp
        (hc₁.sub (hc₁.comp (g := D) (f := fun q : (E × E) × (ℝ × U) ↦
          ((z.1, z.1), q.2)) hproj))).norm
    have hfN : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦
        ‖F q - F ((z.1, z.1), q.2)‖) ((z.1, z.1), η) :=
      (hc₂.sub (hc₂.comp (g := F) (f := fun q : (E × E) × (ℝ × U) ↦
        ((z.1, z.1), q.2)) hproj)).norm
    have heD := hdN.eventually (gt_mem_nhds (show
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (D ((z.1, z.1), η) - D ((z.1, z.1), η))‖ < (1 / 4 : ℝ) by
          rw [sub_self, ContinuousLinearMap.comp_zero]
          rw [norm_zero (E := ((ℝ × U) →L[ℝ] (ℝ × U)))]
          norm_num))
    have heF := hfN.eventually (gt_mem_nhds (show
      ‖F ((z.1, z.1), η) - F ((z.1, z.1), η)‖ < δ by simpa using hδ))
    filter_upwards [heD, heF] with q hdq hfq using ⟨hdq.le, hfq.le⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min R ε
  have hρ : 0 < ρ := lt_min hR hε
  refine ⟨A, ρ, r, δ, V, hρ, hr, hδ, hV, hVc, hA, ?_⟩
  intro x hx y hy
  have hxR : x ∈ ball z.1 (3 * R) :=
    ball_subset_ball (show ρ ≤ 3 * R from (min_le_left _ _).trans (by linarith)) hx
  have hyR : y ∈ ball z.1 (3 * R) :=
    ball_subset_ball (show ρ ≤ 3 * R from (min_le_left _ _).trans (by linarith)) hy
  have hxy : (x, y) ∈ ball (z.1, z.1) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hx).trans_le (min_le_right _ _),
      (mem_ball.mp hy).trans_le (min_le_right _ _)⟩
  have hclose := hεsub hxy
  obtain ⟨hinj, hlower, hcompact, hinner, houter⟩ := hstable (Ξ x y)
    (fun η hη ↦ (hd x hxR y hyR η (hDR hη)).differentiableAt)
    (fun η hη ↦ (hclose η (ball_subset_closedBall hη)).1)
    (fun η hη ↦ (hclose η (closedBall_subset_closedBall (by linarith) hη)).2)
  refine ⟨fun η hη ↦ hseg x hxR y hyR η (hDR hη),
    fun η hη ↦ hd x hxR y hyR η (hDR hη),
    fun η hη ↦ hg x hxR y hyR η (hDR hη),
    hinj, hlower, hcompact, hinner, houter, ?_⟩
  intro η hη
  obtain ⟨θ, hθ, heq⟩ := houter hη.1
  have he : θ = η := hinj (h₁D hθ) hη.2 heq
  exact he ▸ hθ

end JanetCartan.HamiltonPhase.ProjectionChart
