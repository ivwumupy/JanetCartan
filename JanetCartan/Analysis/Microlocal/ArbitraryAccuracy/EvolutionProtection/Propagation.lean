module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ComparisonPropagation

/-!
# Comparison graphs along signed scalar multiples of the Hamilton field

The direct root field is a nonzero scalar multiple of the normalized pencil's
field. ODE uniqueness propagates the SAME comparison graphs with that scalar
speed, without requiring the speed to be positive. Consumer: the whole direct
root segments in `app:ch_regular:thm:no-return` and finite chains in
`app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology NNReal

namespace JanetCartan.ArbitraryAccuracy
open ProtectedFlow HamiltonPhase PhaseCover ActualCarriers

/-- The graph uniqueness argument with a continuous signed speed along the
actual curve. The uniform Lipschitz bound is obtained from compactness of the
time interval (`app:ch_regular:thm:no-return`). -/
theorem scaled_characteristic_stays_on_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W D : Set E} {A B : E → E → E} {g : E → E} {dg : E → E →L[ℝ] E}
    {x p : ℝ → E} {c : ℝ → ℝ} {a b t₀ : ℝ} {K : ℝ≥0}
    (ht₀ : t₀ ∈ Icc a b) (hc : ContinuousOn c (Icc a b))
    (hgraph : ∀ y ∈ W, HasFDerivAt g (dg y) y)
    (htangent : ∀ y ∈ W, B y (g y) = dg y (A y (g y)))
    (hlip : ∀ y ∈ W, LipschitzOnWith K (fun z ↦ B y z - dg y (A y z)) D)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (c t • A (x t) (p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (c t • B (x t) (p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ W) (hpD : ∀ t ∈ Icc a b, p t ∈ D)
    (hgD : ∀ y ∈ W, g y ∈ D) (hinit : p t₀ = g (x t₀)) :
    ∀ t ∈ Icc a b, p t = g (x t) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let v : ℝ → E → E := fun t z ↦
    c t • (B (x t) z - dg (x t) (A (x t) z)) + dg (x t) (c t • A (x t) (p t))
  apply solution_eqOn_of_initial_mem_Icc (v := v) (D := fun _ ↦ D) ht₀
    (K := Real.toNNReal M * K) _ _ _ hpD (fun t ht ↦ hgD _ (hxW t ht)) hinit
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    dsimp only [v]
    rw [dist_add_right, dist_eq_norm, ← smul_sub, norm_smul]
    have hL := (hlip _ (hxW t ht)).dist_le_mul z hz w hw
    rw [dist_eq_norm] at hL
    calc
      _ ≤ ‖c t‖ * (K * dist z w) := mul_le_mul_of_nonneg_left hL (norm_nonneg _)
      _ ≤ (Real.toNNReal M * K : ℝ≥0) * dist z w := by
        simp only [NNReal.coe_mul]
        calc
          _ ≤ (Real.toNNReal M : ℝ) * (K * dist z w) := by
            gcongr
            exact (hM t ht).trans (Real.le_coe_toNNReal M)
          _ = _ := by ring
  · intro t ht
    simpa [v, smul_sub, map_smul] using hp t ht
  · intro t ht
    simpa [v, htangent _ (hxW t ht), Function.comp_def] using
      (hgraph _ (hxW t ht)).comp_hasDerivAt t (hx t ht)

/-- The retained comparison chart propagates along a signed scalar multiple
of its actual Hamilton field. All intermediate physical points and nonzero
covectors are retained; neither graph invariance nor a covector buffer is
assumed (`app:ch_regular:thm:no-return`). -/
theorem comparisonChart_preserves_scaled_segment {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)}
    (hdomain : H.domain = normalizedSymbolDomain (univ : Set (Euclidean n)))
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    {g : ComparisonGeometry (Euclidean n)} (C : ComparisonChart H g)
    {η : ℝ × g.tangentSpace} (hη : η ∈ g.parameters)
    {x p : ℝ → Euclidean n} {c : ℝ → ℝ} {a b t₀ scale : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hscale : 0 < scale) (hc : ContinuousOn c (Icc a b))
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (c t • H.hp (x t, p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (c t • -H.hx (x t, p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ ball 0 g.radius)
    (hdom : ∀ t ∈ Icc a b, (x t, p t) ∈ H.domain)
    (hinit : p t₀ = scale • C.gradientMap η (x t₀)) :
    ∀ t ∈ Icc a b, p t = scale • C.gradientMap η (x t) := by
  let Y := closedBall (0 : Euclidean n) g.radius
  let W := ball (0 : Euclidean n) g.radius
  have hXY : W ⊆ Y := ball_subset_closedBall
  have hlarge (y : Euclidean n) (hy : y ∈ ball 0 (2 * g.radius)) :
      (y, η) ∈ g.domain :=
    g.outer_product_subset_domain ⟨ball_subset_closedBall hy, hη⟩
  have hgrad : ContDiffOn ℝ ∞ (C.gradientMap η) (ball 0 (2 * g.radius)) := by
    intro y hy
    exact ((C.gradient_smooth.contDiffAt (g.isOpen_domain.mem_nhds (hlarge y hy))).comp y
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hderiv : ContDiffOn ℝ ∞ (fderiv ℝ (C.gradientMap η)) (ball 0 (2 * g.radius)) := by
    intro y hy
    exact ((hgrad.contDiffAt (isOpen_ball.mem_nhds hy)).fderiv_right (by simp)).contDiffWithinAt
  obtain ⟨dg, hdg, _, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall 0 g.radius_pos
      isOpen_ball (closedBall_subset_ball (by linarith [g.radius_pos])) hderiv
  have hYlarge : Y ⊆ ball 0 (2 * g.radius) :=
    closedBall_subset_ball (by linarith [g.radius_pos])
  have hgraph : ∀ y ∈ W, HasFDerivAt (C.gradientMap η) (dg y) y := by
    intro y hy
    rw [(heq y (hXY hy)).eq_of_nhds]
    exact ((hgrad.contDiffAt (isOpen_ball.mem_nhds (hYlarge (hXY hy)))).differentiableAt
      (by simp)).hasFDerivAt
  let G := fun y ↦ scale • C.gradientMap η y
  let dG := fun y ↦ scale • dg y
  have hmem : ∀ y ∈ Y, (y, G y) ∈ H.domain := by
    intro y hy
    exact C.homogeneous.scale_mem _
      (C.zero_energy (closedBall_subset_closedBall (by linarith [g.radius_pos]) hy) hη).1
      scale hscale
  have hpc : ContinuousOn p (Icc a b) := fun t ht ↦ (hp t ht).continuousAt.continuousWithinAt
  let D := p '' Icc a b ∪ G '' Y
  have hDc : IsCompact D := (isCompact_Icc.image_of_continuousOn hpc).union
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((hgrad.continuousOn.mono hYlarge).const_smul scale))
  have hDz : ∀ q ∈ D, q ≠ 0 := by
    rintro q (⟨t, ht, rfl⟩ | ⟨y, hy, rfl⟩)
    · have hm := hdom t ht
      rw [hdomain] at hm
      exact hm.2
    · have hm := hmem y hy
      rw [hdomain] at hm
      exact hm.2
  obtain ⟨L, hL⟩ := exists_uniform_defect_lipschitzOnWith_of_smooth H
    (isCompact_closedBall _ _) hDc (Y := Y) (dg := dG)
    (by intro z hz; rw [hdomain]; exact ⟨mem_univ _, hDz z.2 hz.2⟩)
    (hH.of_le (by simp)) ((hdg.const_smul scale).of_le (by simp))
  apply scaled_characteristic_stays_on_graph (W := W) (D := D) (dg := dG)
    ht₀ hc (fun y hy ↦ (hgraph y hy).const_smul scale) _
    (fun y hy ↦ hL y (hXY hy)) hx hp hxW
    (fun t ht ↦ Or.inl ⟨t, ht, rfl⟩) (fun y hy ↦ Or.inr ⟨y, hXY hy, rfl⟩) hinit
  intro y hy
  have hm := (C.zero_energy
    (closedBall_subset_closedBall (by linarith [g.radius_pos]) (hXY hy)) hη).1
  dsimp [G, dG]
  rw [H.hx_smul C.homogeneous hm hscale, H.hp_smul C.homogeneous hm hscale,
    ← smul_neg, C.hamilton_tangent (hlarge y (hYlarge (hXY hy))),
    (hgraph y hy).fderiv]
  rfl

end JanetCartan.ArbitraryAccuracy
