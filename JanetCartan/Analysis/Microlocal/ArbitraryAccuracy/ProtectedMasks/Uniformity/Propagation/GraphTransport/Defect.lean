module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ComparisonPropagation
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.VariationError

/-!
# Quantitative comparison-graph defects

The differential estimate for `app:ch_regular:thm:no-return`, consumed by
the protected finite-chain argument of `app:ch_regular:lem:finite-chain`.
The estimates use the original elapsed time and allow signed Hamilton speeds.
Their quantitative inputs are derivative and vector-field bounds; they do not
assume graph-error persistence or a successful protected neighborhood.

This leaf does not construct uniform constants from the coefficient class.
The comparison-gradient derivative bound must be recovered for the retained
charts from `HamiltonPhase.exists_commonTameContinuousConicHamiltonPhases`;
the field bound must come from the primitive normalized-pencil low jets.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open HamiltonPhase ProtectedFlow PhaseCover

/-- Differential Grönwall estimate for the actual defect of a tangent graph,
with a bounded signed speed. Both endpoint orientations and every intermediate
point are retained (`app:ch_regular:thm:no-return`).
Consumer: `comparisonChart_scaled_graph_error_le`. -/
theorem scaled_characteristic_graph_error_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W D : Set E} {A B : E → E → E} {g : E → E}
    {dg : E → E →L[ℝ] E} {x p : ℝ → E} {c : ℝ → ℝ}
    {a b t₀ t₁ speed K : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (ht₁ : t₁ ∈ Icc a b)
    (hspeed : 0 ≤ speed)
    (hc : ∀ t ∈ Icc a b, |c t| ≤ speed)
    (hgraph : ∀ y ∈ W, HasFDerivAt g (dg y) y)
    (hdefect : ∀ y ∈ W, ∀ v ∈ D,
      ‖B y v - dg y (A y v)‖ ≤ K * ‖v - g y‖)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (c t • A (x t) (p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (c t • B (x t) (p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ W)
    (hpD : ∀ t ∈ Icc a b, p t ∈ D) :
    ‖p t₁ - g (x t₁)‖ ≤
      Real.exp (speed * K * |t₁ - t₀|) * ‖p t₀ - g (x t₀)‖ := by
  have hsub : uIcc t₀ t₁ ⊆ Icc a b := uIcc_subset_Icc ht₀ ht₁
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ p s - g (x s))
        (c t • (B (x t) (p t) - dg (x t) (A (x t) (p t)))) t := by
    simpa only [Function.comp_def, Pi.sub_def, map_smul, smul_sub] using
      (hp t ht).sub ((hgraph _ (hxW t ht)).comp_hasDerivAt t (hx t ht))
  have hb (t : ℝ) (ht : t ∈ Icc a b) :
      ‖c t • (B (x t) (p t) - dg (x t) (A (x t) (p t)))‖ ≤
        (speed * K) * ‖p t - g (x t)‖ + 0 := by
    rw [norm_smul, Real.norm_eq_abs, add_zero]
    calc
      _ ≤ speed * ‖B (x t) (p t) - dg (x t) (A (x t) (p t))‖ :=
        mul_le_mul_of_nonneg_right (hc t ht) (norm_nonneg _)
      _ ≤ speed * (K * ‖p t - g (x t)‖) :=
        mul_le_mul_of_nonneg_left (hdefect _ (hxW t ht) _ (hpD t ht)) hspeed
      _ = _ := (mul_assoc _ _ _).symm
  have he := ODE.norm_le_gronwallBound_of_hasDerivAt_uIcc
    (fun t ht ↦ hd t (hsub ht)) (le_refl ‖p t₀ - g (x t₀)‖)
    (fun t ht ↦ hb t (hsub ht))
  simpa only [gronwallBound_ε0, mul_comm] using he

/-- The primitive Hamilton-field Lipschitz estimate and the graph derivative
bound control the defect. Tangency is used only at the comparison covector;
no bound on the trajectory's distance to the graph is assumed
(`app:ch_regular:thm:no-return`).
Consumer: `comparisonChart_scaled_graph_error_le`. -/
theorem hamilton_graph_defect_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : HomogeneousSymbol E) {y v w : E} {dg : E →L[ℝ] E}
    {J V : ℝ} (hJ : 0 ≤ J)
    (hdg : ‖dg‖ ≤ J)
    (htangent : -H.hx (y, w) = dg (H.hp (y, w)))
    (hfield : ‖H.vectorField (y, v) - H.vectorField (y, w)‖ ≤ V * ‖v - w‖) :
    ‖-H.hx (y, v) - dg (H.hp (y, v))‖ ≤ (1 + J) * V * ‖v - w‖ := by
  have ha : ‖H.hp (y, v) - H.hp (y, w)‖ ≤ V * ‖v - w‖ :=
    (norm_fst_le (H.vectorField (y, v) - H.vectorField (y, w))).trans hfield
  have hb : ‖-H.hx (y, v) - -H.hx (y, w)‖ ≤ V * ‖v - w‖ :=
    (norm_snd_le (H.vectorField (y, v) - H.vectorField (y, w))).trans hfield
  calc
    _ = ‖(-H.hx (y, v) - -H.hx (y, w)) -
        dg (H.hp (y, v) - H.hp (y, w))‖ := by
      rw [map_sub, htangent]
      congr 1
      abel
    _ ≤ ‖-H.hx (y, v) - -H.hx (y, w)‖ +
        ‖dg (H.hp (y, v) - H.hp (y, w))‖ := norm_sub_le _ _
    _ ≤ V * ‖v - w‖ + J * (V * ‖v - w‖) :=
      add_le_add hb ((dg.le_opNorm _).trans (mul_le_mul hdg ha (norm_nonneg _) hJ))
    _ = _ := by ring

/-- A physical derivative bound gives the base-point Lipschitz bound for the
literal retained comparison gradient on the common closed ball
(`app:ch_regular:lem:finite-chain`). The derivative bound is the remaining
producer obligation, not a smoothness/compactness choice after the field.
Consumer: the finite-depth buffered-reachability induction. -/
theorem comparisonChart_gradient_dist_le_of_derivative_bound
    {n : ℕ} {H : HomogeneousSymbol (Euclidean n)}
    {g : ComparisonGeometry (Euclidean n)} (C : ComparisonChart H g)
    {η : ℝ × g.tangentSpace} (hη : η ∈ g.parameters)
    {r Lx : ℝ} (hr : r ≤ 2 * g.radius)
    (hderiv : ∀ x ∈ closedBall (0 : Euclidean n) r,
      ‖fderiv ℝ (C.gradientMap η) x‖ ≤ Lx)
    {x y : Euclidean n} (hx : x ∈ closedBall 0 r) (hy : y ∈ closedBall 0 r) :
    ‖C.gradientMap η x - C.gradientMap η y‖ ≤ Lx * dist x y := by
  have hd (z : Euclidean n) (hz : z ∈ closedBall 0 r) :
      DifferentiableAt ℝ (C.gradientMap η) z := by
    have hm : (z, η) ∈ g.domain :=
      g.outer_product_subset_domain ⟨closedBall_subset_closedBall hr hz, hη⟩
    exact ((C.gradient_smooth.contDiffAt (g.isOpen_domain.mem_nhds hm)).comp z
      (g := fun q : Euclidean n × (ℝ × g.tangentSpace) ↦ C.gradientMap q.2 q.1)
      (f := fun y : Euclidean n ↦ (y, η))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  simpa only [dist_eq_norm] using
    (convex_closedBall (0 : Euclidean n) r).norm_image_sub_le_of_norm_fderiv_le
      hd hderiv hy hx

/-- Quantitative error transport for the literal comparison chart along an
entire signed Hamilton segment (`app:ch_regular:thm:no-return`). The constant
uses only the speed, the physical gradient derivative bound, a radial cap,
and the Hamilton-field Lipschitz bound. All may be fixed before the field.
No local error restriction or persistence premise is used.
Consumer: `physicalDirectRelation_comparison_graph_error_le`. -/
theorem comparisonChart_scaled_graph_error_le
    {n : ℕ} {H : HomogeneousSymbol (Euclidean n)}
    {g : ComparisonGeometry (Euclidean n)} (C : ComparisonChart H g)
    {η : ℝ × g.tangentSpace} (hη : η ∈ g.parameters)
    {r Lx V speed β scale : ℝ}
    (hr : r ≤ 2 * g.radius) (hLx : 0 ≤ Lx)
    (hspeed : 0 ≤ speed) (hscale : 0 < scale) (hscaleβ : scale ≤ β)
    {D : Set (Euclidean n)}
    (hderiv : ∀ y ∈ closedBall (0 : Euclidean n) r,
      ‖fderiv ℝ (C.gradientMap η) y‖ ≤ Lx)
    (hfield : ∀ y ∈ closedBall (0 : Euclidean n) r, ∀ v ∈ D, ∀ w ∈ D,
      ‖H.vectorField (y, v) - H.vectorField (y, w)‖ ≤ V * ‖v - w‖)
    (hgD : ∀ y ∈ closedBall (0 : Euclidean n) r, scale • C.gradientMap η y ∈ D)
    {x p : ℝ → Euclidean n} {c : ℝ → ℝ} {a b t₀ t₁ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (ht₁ : t₁ ∈ Icc a b)
    (hc : ∀ t ∈ Icc a b, |c t| ≤ speed)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (c t • H.hp (x t, p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (c t • -H.hx (x t, p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ closedBall (0 : Euclidean n) r)
    (hpD : ∀ t ∈ Icc a b, p t ∈ D) :
    ‖p t₁ - scale • C.gradientMap η (x t₁)‖ ≤
      Real.exp (speed * ((1 + β * Lx) * V) * |t₁ - t₀|) *
        ‖p t₀ - scale • C.gradientMap η (x t₀)‖ := by
  let dg := fun y ↦ scale • fderiv ℝ (C.gradientMap η) y
  have hβ : 0 ≤ β := hscale.le.trans hscaleβ
  apply scaled_characteristic_graph_error_le
    (W := closedBall (0 : Euclidean n) r) (D := D)
    (g := fun y ↦ scale • C.gradientMap η y) (x := x) (p := p) (c := c)
    (K := (1 + β * Lx) * V)
    (dg := dg) (A := fun y v ↦ H.hp (y, v)) (B := fun y v ↦ -H.hx (y, v))
    ht₀ ht₁ hspeed hc ?_ ?_ hx hp hxW hpD
  · intro y hy
    have hm : (y, η) ∈ g.domain :=
      g.outer_product_subset_domain ⟨closedBall_subset_closedBall hr hy, hη⟩
    have hd : DifferentiableAt ℝ (C.gradientMap η) y :=
      ((C.gradient_smooth.contDiffAt (g.isOpen_domain.mem_nhds hm)).comp y
        (g := fun q : Euclidean n × (ℝ × g.tangentSpace) ↦ C.gradientMap q.2 q.1)
        (f := fun z : Euclidean n ↦ (z, η))
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    exact hd.hasFDerivAt.const_smul scale
  · intro y hy v hv
    have hm : (y, η) ∈ g.domain :=
      g.outer_product_subset_domain ⟨closedBall_subset_closedBall hr hy, hη⟩
    have hzero := C.zero_energy (closedBall_subset_closedBall hr hy) hη
    have htan : -H.hx (y, scale • C.gradientMap η y) =
        dg y (H.hp (y, scale • C.gradientMap η y)) := by
      rw [H.hx_smul C.homogeneous hzero.1 hscale,
        H.hp_smul C.homogeneous hzero.1 hscale, ← smul_neg, C.hamilton_tangent hm]
      rfl
    have hdg : ‖dg y‖ ≤ β * Lx := by
      dsimp only [dg]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      exact mul_le_mul hscaleβ (hderiv y hy) (norm_nonneg _) hβ
    exact hamilton_graph_defect_norm_le H (mul_nonneg hβ hLx) hdg htan
      (hfield y hy v hv _ (hgD y hy))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
