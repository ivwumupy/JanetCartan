module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Compatibility
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ConicExtension

/-!
# Compatibility without an exposed choice of scalar root

The common-family constructions in `app:lem:common-hamilton-phase` all retain
state containment and the initial energy and tangential-momentum identities.
On a sufficiently small state ball, those identities uniquely determine the
initial momentum. This removes the need to recover the hidden scalar root from
each independent construction. ODE uniqueness then identifies the trajectories.
The ball and its transverse gap are produced from the fixed reference symbol.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
local instance transverseCompatibilityNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance transverseCompatibilityNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

/-- Choose a smaller common state ball with a transverse gap for every nearby
symbol (`app:lem:common-hamilton-phase`). The same original compact domain
measures symbol closeness, and no normalization of the normal is required.
The consumer is the root/ODE identification of the tame, conic and continuous
families after constructing them inside this ball. -/
theorem exists_uniform_transverse_stateBall
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    {z₀ : E × E} {R : ℝ} (hR : 0 < R) (hRD : closedBall z₀ R ⊆ D)
    (ν : E) (htrans : ⟪H₀.hp z₀, ν⟫_ℝ ≠ 0) :
    ∃ r δ c : ℝ, 0 < r ∧ r < R ∧ 0 < δ ∧ 0 < c ∧
      closedBall z₀ r ⊆ D ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∀ z ∈ closedBall z₀ r, c ≤ |⟪H.hp z, ν⟫_ℝ| := by
  let v := |⟪H₀.hp z₀, ν⟫_ℝ|
  have hv : 0 < v := abs_pos.mpr htrans
  have hcont : ContinuousAt (fun z ↦ |⟪H₀.hp z, ν⟫_ℝ|) z₀ :=
    ((H₀.hasFDerivAt_hp z₀ (hDH₀ (hRD (mem_closedBall_self hR.le)))).continuousAt.inner
      continuousAt_const).abs
  have hn : {z | v / 2 < |⟪H₀.hp z, ν⟫_ℝ|} ∈ 𝓝 z₀ :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds (half_lt_self hv))
  obtain ⟨b, hb, hball⟩ := Metric.mem_nhds_iff.mp hn
  let r := min R b / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by have hh := min_le_left R b; dsimp [r]; linarith
  have hrb : r < b := by have hh := min_le_right R b; dsimp [r]; linarith
  let δ := v / (4 * (‖ν‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδν : δ * ‖ν‖ ≤ v / 4 := by
    have hh : δ * (4 * (‖ν‖ + 1)) = v := div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg ν]
  refine ⟨r, δ, v / 4, hr, hrR, hδ, by positivity,
    (closedBall_subset_closedBall hrR.le).trans hRD, ?_⟩
  intro H hDH hH hsmall z hz
  have hgap := hball (closedBall_subset_ball hrb hz)
  have hdiff := abs_normal_velocity_sub_le_cNorm_three H H₀ hD hDH hDH₀
    (hH.of_le (by simp)) (hH₀.of_le (by simp)) (isCompact_closedBall _ _) hRD ν
    (closedBall_subset_closedBall hrR.le hz)
  have hdiff' := hdiff.trans ((mul_le_mul_of_nonneg_right hsmall (norm_nonneg ν)).trans hδν)
  have hh := abs_sub_abs_le_abs_sub ⟪H₀.hp z, ν⟫_ℝ ⟪H.hp z, ν⟫_ℝ
  rw [abs_sub_comm] at hh
  change v / 2 < |⟪H₀.hp z, ν⟫_ℝ| at hgap
  linarith

namespace HamiltonFlow
variable {H : HomogeneousSymbol E} (Φ Ψ : HamiltonFlow H U)

omit [FiniteDimensional ℝ E] in
/-- Initial states from two constructions coincide on a convex transverse
state patch (`app:lem:common-hamilton-phase`). The actual energy and tangential
pairing identities suffice; no chosen root or equality of initial data is an
input. This closes the branch-identification premise of ODE uniqueness. -/
theorem initial_state_eq_of_transverse_patch
    {K : Set (E × E)} (hK : Convex ℝ K) (hKH : K ⊆ H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (hj' : Ψ.sectionMap = j.toContinuousLinearMap)
    (hgap : ∀ z ∈ K, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    {s : InitialData U} (hs : s ∈ Φ.parameters) (hs' : s ∈ Ψ.parameters)
    (hrange : (Φ.position (0, s), Φ.momentum (0, s)) ∈ K)
    (hrange' : (Ψ.position (0, s), Ψ.momentum (0, s)) ∈ K) :
    (Φ.position (0, s), Φ.momentum (0, s)) =
      (Ψ.position (0, s), Ψ.momentum (0, s)) := by
  let p := Φ.momentum (0, s)
  let p' := Ψ.momentum (0, s)
  let a := ⟪ν, p⟫_ℝ / ⟪ν, ν⟫_ℝ
  let a' := ⟪ν, p'⟫_ℝ / ⟪ν, ν⟫_ℝ
  have hx : Φ.position (0, s) = j s.1 := by
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_position s hs
  have hx' : Ψ.position (0, s) = j s.1 := by
    simpa only [hj', LinearIsometry.coe_toContinuousLinearMap] using Ψ.initial_position s hs'
  have hp : p = a • ν + j s.2.2 :=
    sectionMomentum_eq_normal_add_tangent j ν p hν horth hspan s.2.2
      (by simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_momentum s hs)
  have hp' : p' = a' • ν + j s.2.2 :=
    sectionMomentum_eq_normal_add_tangent j ν p' hν horth hspan s.2.2
      (by simpa only [hj', LinearIsometry.coe_toContinuousLinearMap] using Ψ.initial_momentum s hs')
  have hdiff : p' - p = (a' - a) • ν := by rw [hp', hp]; module
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (j s.1, p + t • (p' - p)) ∈ K := by
    have hh := hK.add_smul_sub_mem hrange hrange' ht
    simpa [hx, hx', p, p', Prod.mk_add_mk, Prod.mk_sub_mk] using hh
  let f : ℝ → ℝ := fun t ↦ H.h (j s.1, p + t • (p' - p))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f ⟪H.hp (j s.1, p + t • (p' - p)), p' - p⟫_ℝ t := by
    have hh := (H.hasFDerivAt_h _ (hKH (hmem t ht))).comp_hasDerivAt t
      ((hasDerivAt_const t (j s.1)).prodMk
        ((hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const (p' - p))))
    simpa [f, Function.comp_def, hamiltonDifferential_apply] using hh
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f
    (fun t ↦ ⟪H.hp (j s.1, p + t • (p' - p)), p' - p⟫_ℝ) zero_lt_one
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hd t (Ioo_subset_Icc_self ht))
  have hf0 : f 0 = s.2.1 := by
    simpa [f, p, hx] using Φ.initial_energy s hs
  have hf1 : f 1 = s.2.1 := by
    simpa [f, p', hx'] using Ψ.initial_energy s hs'
  rw [hf1, hf0, sub_self, zero_div, hdiff, inner_smul_right] at he
  have hnonzero := hgap _ (hmem t (Ioo_subset_Icc_self ht))
  rw [hdiff] at hnonzero
  have haa : a' - a = 0 := (mul_eq_zero.mp he).resolve_right hnonzero
  have hpp : p' = p := by
    rw [sub_eq_zero.mp haa] at hp'
    exact hp'.trans hp.symm
  exact Prod.ext (hx.trans hx'.symm) hpp.symm

/-- Identifying trajectories of independently constructed phase families on a
common strip, using only their retained section and state-range data
(`app:lem:common-hamilton-phase`). `exists_uniform_transverse_stateBall` produces
the transverse state ball; the common-family constructors produce the flows.
No hidden root choice is needed. -/
theorem state_eq_of_transverse_stateBall
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) {w : E × E} {R T : ℝ}
    (hRD : closedBall w R ⊆ D) (hT : 0 < T)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (hj' : Ψ.sectionMap = j.toContinuousLinearMap)
    (hgap : ∀ z ∈ closedBall w R, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    (htime : Ioo (-T) T ⊆ Φ.time) (htime' : Ioo (-T) T ⊆ Ψ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) (hs' : s ∈ Ψ.parameters)
    (hrange : ∀ t ∈ Ioo (-T) T, (Φ.position (t, s), Φ.momentum (t, s)) ∈ closedBall w R)
    (hrange' : ∀ t ∈ Ioo (-T) T, (Ψ.position (t, s), Ψ.momentum (t, s)) ∈ closedBall w R) :
    ∀ t ∈ Ioo (-T) T, (Φ.position (t, s), Φ.momentum (t, s)) =
      (Ψ.position (t, s), Ψ.momentum (t, s)) := by
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  exact Φ.state_eq_of_initial_eq Ψ hD hDH hH hRD hT htime htime' hs hs' hrange hrange'
    (Φ.initial_state_eq_of_transverse_patch Ψ (convex_closedBall _ _) (hRD.trans hDH)
      j ν hν horth hspan hj hj' hgap hs hs' (hrange 0 hzero) (hrange' 0 hzero))

/-- Root and ODE uniqueness identify the state maps on a common source ball
(`app:lem:common-hamilton-phase`). This transfers the sharp flow estimates to
the actual charts carrying the conic inverse buffers. -/
theorem state_eq_on_transverse_ball
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) {w : E × E} {R d : ℝ}
    (hRD : closedBall w R ⊆ D) (hd : 0 < d)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (hj' : Ψ.sectionMap = j.toContinuousLinearMap)
    (hgap : ∀ z ∈ closedBall w R, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    {s₀ : InitialData U}
    (hadm : ball ((0 : ℝ), s₀) d ⊆ Φ.time ×ˢ Φ.parameters)
    (hadm' : ball ((0 : ℝ), s₀) d ⊆ Ψ.time ×ˢ Ψ.parameters)
    (hrange : ∀ q ∈ Φ.time ×ˢ Φ.parameters,
      (Φ.position q, Φ.momentum q) ∈ closedBall w R)
    (hrange' : ∀ q ∈ Ψ.time ×ˢ Ψ.parameters,
      (Ψ.position q, Ψ.momentum q) ∈ closedBall w R) :
    EqOn (fun q ↦ (Φ.position q, Φ.momentum q))
      (fun q ↦ (Ψ.position q, Ψ.momentum q)) (ball ((0 : ℝ), s₀) d) := by
  have hball (t : ℝ) (s : InitialData U)
      (ht : t ∈ Ioo (-d) d) (hs : s ∈ ball s₀ d) : (t, s) ∈ ball ((0 : ℝ), s₀) d := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro ht (mem_ball.mp hs)
  have ht : Ioo (-d) d ⊆ Φ.time := fun t ht ↦
    (hadm (hball t s₀ ht (mem_ball_self hd))).1
  have ht' : Ioo (-d) d ⊆ Ψ.time := fun t ht ↦
    (hadm' (hball t s₀ ht (mem_ball_self hd))).1
  intro q hq
  have hq' : q.1 ∈ Ioo (-d) d ∧ q.2 ∈ ball s₀ d := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using hq
  exact Φ.state_eq_of_transverse_stateBall Ψ hD hDH hH hRD hd j ν hν horth hspan
    hj hj' hgap ht ht' (hadm hq).2 (hadm' hq).2
    (fun t ht0 ↦ hrange _ ⟨ht ht0, (hadm hq).2⟩)
    (fun t ht0 ↦ hrange' _ ⟨ht' ht0, (hadm' hq).2⟩) q.1 hq'.1

end HamiltonFlow

namespace ProjectionChart
variable {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U}

omit [FiniteDimensional ℝ E] in
/-- Shrinking the target forces the actual inverse lift into any prescribed
ball about the initial source point (`app:lem:common-hamilton-phase`). The
radius depends only on the fixed normalized projection equivalence. This is
the uniform buffer needed to apply `phase_jets_eq_of_state_eq` to independently
chosen charts; inverse-lift containment is proved rather than assumed. -/
theorem chartLift_mem_ball_of_initial_target_ball (C : ProjectionChart Φ)
    {D : Set (ℝ × InitialData U)} (hD : Convex ℝ D)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hadm : D ⊆ Φ.time ×ˢ Φ.parameters) (hsource : C.source ⊆ D)
    (hgap : ∀ q ∈ D,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) -
        ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2)
    {s₀ : InitialData U} (hs₀ : ((0 : ℝ), s₀) ∈ D)
    {a : ℝ} (_ha : 0 < a) {z : E × (ℝ × U)} (hz : z ∈ C.target)
    (hnear : z ∈ ball (Φ.sectionMap s₀.1, s₀.2)
      (a / (2 * (‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ + 1)))) :
    chartLift C.coordinates z ∈ ball ((0 : ℝ), s₀) a := by
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  have hN : 0 ≤ N := norm_nonneg _
  have hright : Φ.augmentedProjection (chartLift C.coordinates z) = z :=
    Prod.ext (C.right_inverse z hz) rfl
  have hstart : Φ.augmentedProjection (0, s₀) = (Φ.sectionMap s₀.1, s₀.2) :=
    Prod.ext (Φ.initial_position s₀ (hadm hs₀).2) rfl
  have hlower := normalized_lower_lipschitz_of_derivative_gap hD A
    (fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection (hadm hq)).differentiableAt)
    hgap (hsource (C.maps_to_source z hz)) hs₀
  rw [hright, hstart] at hlower
  have hupper := (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).le_opNorm
    (z - (Φ.sectionMap s₀.1, s₀.2))
  have hdist : ‖z - (Φ.sectionMap s₀.1, s₀.2)‖ * (2 * (N + 1)) < a :=
    (lt_div_iff₀ (by positivity : 0 < 2 * (N + 1))).mp (by
      simpa only [mem_ball, dist_eq_norm] using hnear)
  have hn := norm_nonneg (z - (Φ.sectionMap s₀.1, s₀.2))
  rw [mem_ball, dist_eq_norm]
  change ‖A.symm (z - (Φ.sectionMap s₀.1, s₀.2))‖ ≤
    N * ‖z - (Φ.sectionMap s₀.1, s₀.2)‖ at hupper
  nlinarith

/-- A uniform overlap for independently constructed charts of the same symbol
(`app:lem:common-hamilton-phase`). Only the first chart's normalized gap is
needed: its inverse lift is forced into the second chart's source ball, where
root and ODE uniqueness identify the projections. The radius depends on the
two source radii and the fixed equivalence, before the choice of symbol/flow.
The consumer is assembly of tame estimates and finite-order continuity. -/
theorem coordinates_eq_on_transverse_overlap {Ψ : HamiltonFlow H U}
    (C : ProjectionChart Φ) (C' : ProjectionChart Ψ)
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) {w : E × E} {R : ℝ}
    (hRD : closedBall w R ⊆ D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (hj' : Ψ.sectionMap = j.toContinuousLinearMap)
    (htrans : ∀ z ∈ closedBall w R, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    {s₀ : InitialData U} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hadm : ball ((0 : ℝ), s₀) a ⊆ Φ.time ×ˢ Φ.parameters)
    (hadm' : ball ((0 : ℝ), s₀) b ⊆ Ψ.time ×ˢ Ψ.parameters)
    (hsource : C.source ⊆ ball ((0 : ℝ), s₀) a)
    (hsource' : C'.source = ball ((0 : ℝ), s₀) b ∩ Ψ.augmentedProjection ⁻¹' C'.target)
    (hgap : ∀ q ∈ ball ((0 : ℝ), s₀) a,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) -
        ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2)
    (hrange : ∀ q ∈ Φ.time ×ˢ Φ.parameters,
      (Φ.position q, Φ.momentum q) ∈ closedBall w R)
    (hrange' : ∀ q ∈ Ψ.time ×ˢ Ψ.parameters,
      (Ψ.position q, Ψ.momentum q) ∈ closedBall w R) :
    EqOn C.coordinates C'.coordinates
      (C.target ∩ C'.target ∩ ball (j s₀.1, s₀.2)
        (min a b / (2 * (‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ + 1)))) := by
  let d := min a b
  have hd : 0 < d := lt_min ha hb
  have hsub : ball ((0 : ℝ), s₀) d ⊆ Φ.time ×ˢ Φ.parameters :=
    (ball_subset_ball (min_le_left _ _)).trans hadm
  have hsub' : ball ((0 : ℝ), s₀) d ⊆ Ψ.time ×ˢ Ψ.parameters :=
    (ball_subset_ball (min_le_right _ _)).trans hadm'
  have hball (t : ℝ) (s : InitialData U)
      (ht : t ∈ Ioo (-d) d) (hs : s ∈ ball s₀ d) : (t, s) ∈ ball ((0 : ℝ), s₀) d := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro ht (mem_ball.mp hs)
  have htime : Ioo (-d) d ⊆ Φ.time := fun t ht ↦
    (hsub (hball t s₀ ht (mem_ball_self hd))).1
  have htime' : Ioo (-d) d ⊆ Ψ.time := fun t ht ↦
    (hsub' (hball t s₀ ht (mem_ball_self hd))).1
  have hzero : (0 : ℝ) ∈ Ioo (-d) d := ⟨by linarith, hd⟩
  have hstate : ∀ q ∈ ball ((0 : ℝ), s₀) d,
      (Φ.position q, Φ.momentum q) = (Ψ.position q, Ψ.momentum q) := by
    intro q hq
    have hq' : q.1 ∈ Ioo (-d) d ∧ q.2 ∈ ball s₀ d := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
        Real.norm_eq_abs, abs_lt, mem_Ioo] using hq
    exact Φ.state_eq_of_transverse_stateBall Ψ hD hDH hH hRD hd j ν hν horth hspan
      hj hj' htrans htime htime' (hsub hq).2 (hsub' hq).2
      (fun t ht ↦ hrange _ ⟨htime ht, (hsub (hball 0 q.2 hzero hq'.2)).2⟩)
      (fun t ht ↦ hrange' _ ⟨htime' ht, (hsub' (hball 0 q.2 hzero hq'.2)).2⟩)
      q.1 hq'.1
  intro z hz
  have hlift := C.chartLift_mem_ball_of_initial_target_ball (convex_ball _ _) A
    hadm hsource hgap (mem_ball_self ha) hd hz.1.1
    (by simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using hz.2)
  have hp : Ψ.position (chartLift C.coordinates z) = z.1 :=
    (congrArg Prod.fst (hstate _ hlift)).symm.trans (C.right_inverse z hz.1.1)
  have hmem : chartLift C.coordinates z ∈ C'.source := by
    rw [hsource']
    refine ⟨ball_subset_ball (min_le_right _ _) hlift, ?_⟩
    change (Ψ.position (chartLift C.coordinates z), z.2) ∈ C'.target
    rw [hp]
    exact hz.1.2
  have he := (C'.left_inverse _ hmem).symm
  rw [hp] at he
  exact he

omit [FiniteDimensional ℝ E] in
/-- On an open overlap of the actual inverse coordinates, all phase seminorms
coincide (`app:lem:common-hamilton-phase`). This transports the sharp tame bound
and the continuity estimates without changing derivative order. -/
theorem cNorm_phase_sub_eq_of_coordinates_eqOn
    {H' : HomogeneousSymbol E} {Ψ : HamiltonFlow H' U}
    (C : ProjectionChart Φ) (C' : ProjectionChart Ψ)
    {V K : Set (E × (ℝ × U))} (hV : IsOpen V) (hK : K ⊆ V)
    (he : EqOn C.coordinates C'.coordinates V)
    (f : E × (ℝ × U) → ℝ) (m : ℕ) :
    cNorm K m (fun z ↦ phase C.coordinates z - f z) =
      cNorm K m (fun z ↦ phase C'.coordinates z - f z) := by
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Set.image_congr
  intro z hz
  have hh : (fun z ↦ phase C.coordinates z - f z) =ᶠ[𝓝 z]
      (fun z ↦ phase C'.coordinates z - f z) :=
    eventuallyEq_of_mem (hV.mem_nhds (hK hz)) (fun w hw ↦ by simp only [phase, he hw])
  exact congrArg norm ((hh.iteratedFDeriv ℝ k).eq_of_nhds)

end ProjectionChart
end JanetCartan.HamiltonPhase
