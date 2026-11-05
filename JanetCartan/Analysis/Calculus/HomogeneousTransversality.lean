module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.Linarith

/-!
# Homogeneous symbols and transverse patches

The differential and compactness steps of `app:ch_regular_base:prop:normalization`
in `paper.tex`. Homogeneity is required only at nonzero vectors and positive scales.
The cover theorem constructs its directions and positive gap from a continuous,
nonvanishing field of linear functionals. Its parameter ball is the common coefficient
neighborhood; its doubled closed balls provide buffers inside prescribed charts.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive degree-one homogeneity on the punctured space, as used in
`app:ch_regular_base:prop:normalization`. No value at the origin is prescribed. -/
def PosHomogeneousOne (q : E → ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ x : E, x ≠ 0 → q (t • x) = t * q x

/-- Euler's identity in `app:ch_regular_base:prop:normalization`.
Only differentiability at the given nonzero point is needed. -/
theorem PosHomogeneousOne.euler {q : E → ℝ} (hq : PosHomogeneousOne q)
    {x : E} (hx : x ≠ 0) (hd : DifferentiableAt ℝ q x) :
    fderiv ℝ q x x = q x := by
  have h := hd.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
    (hasDerivAt_id (1 : ℝ)) (show (fun t : ℝ ↦ q (t • x)) =ᶠ[𝓝 1]
      (fun t ↦ t • q x) from
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).mono
        (fun t ht ↦ hq t ht x hx))
  simpa using h

/-- Euler's identity excludes a zero derivative away from the zero-energy surface
in `app:ch_regular_base:prop:normalization`. -/
theorem PosHomogeneousOne.fderiv_ne_zero {q : E → ℝ} (hq : PosHomogeneousOne q)
    {x : E} (hx : x ≠ 0) (hd : DifferentiableAt ℝ q x) (hqx : q x ≠ 0) :
    fderiv ℝ q x ≠ 0 := by
  intro h
  apply hqx
  rw [← hq.euler hx hd, h]
  rfl

/-- The characteristic nondegeneracy hypothesis and Euler's identity together give
nonvanishing at every protected point (`app:ch_regular_base:prop:normalization`). -/
theorem PosHomogeneousOne.fderiv_ne_zero_of_regular_zero {q : E → ℝ}
    (hq : PosHomogeneousOne q) {x : E} (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ q x) (hzero : q x = 0 → fderiv ℝ q x ≠ 0) :
    fderiv ℝ q x ≠ 0 := by
  by_cases h : q x = 0
  · exact hzero h
  · exact hq.fderiv_ne_zero hx hd h

/-- The differential of a positively degree-one homogeneous symbol is constant on
positive rays (`app:ch_regular_base:prop:normalization`), giving conic patches. -/
theorem PosHomogeneousOne.fderiv_smul {q : E → ℝ} (hq : PosHomogeneousOne q)
    {x : E} (hx : x ≠ 0) (hd : DifferentiableAt ℝ q x)
    {t : ℝ} (ht : 0 < t) : fderiv ℝ q (t • x) = fderiv ℝ q x := by
  have heq : (fun y ↦ q (t • y)) =ᶠ[𝓝 x] t • q :=
    (eventually_ne_nhds hx).mono (fun y hy ↦ hq t ht y hy)
  apply smul_right_injective (E →L[ℝ] ℝ) ht.ne'
  change t • fderiv ℝ q (t • x) = t • fderiv ℝ q x
  rw [← fderiv_comp_smul, heq.fderiv_eq, fderiv_const_smul hd]

/-- Choose an oriented unit transverse direction from a nonzero differential, as in
`app:ch_regular_base:prop:normalization`. -/
theorem exists_unit_direction_apply_pos (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ v : E, ‖v‖ = 1 ∧ 0 < L v := by
  have hw : ∃ w : E, L w ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hw
  have hu : ∃ u : E, 0 < L u := by
    rcases lt_or_gt_of_ne hw with h | h
    · exact ⟨-w, by simpa using neg_pos.mpr h⟩
    · exact ⟨w, h⟩
  obtain ⟨u, hu⟩ := hu
  have hune : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hune
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [norm_smul_of_nonneg (le_of_lt (inv_pos.mpr hn)), inv_mul_cancel₀ hn.ne']
  · simpa only [map_smul, smul_eq_mul] using mul_pos (inv_pos.mpr hn) hu

private theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ c > 0, ∀ i ∈ s, c ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨c, hc, hcf⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) c, lt_min (hf i (Finset.mem_insert_self i s)) hc, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hcf j hj)

variable {A X : Type*} [PseudoMetricSpace A] [PseudoMetricSpace X]

/-- A local buffered patch with a fixed unit direction and a positive gap, including
parameter perturbations (`app:ch_regular_base:prop:normalization`). -/
theorem exists_buffered_transverse_ball (D : A → X → E →L[ℝ] ℝ)
    (a₀ : A) (x : X) (hD : ContinuousAt (Function.uncurry D) (a₀, x))
    (hne : D a₀ x ≠ 0) (O : Set X) (hO : O ∈ 𝓝 x) :
    ∃ (v : E) (r c : ℝ), ‖v‖ = 1 ∧ 0 < r ∧ 0 < c ∧
      closedBall x (2 * r) ⊆ O ∧
      ∀ a ∈ ball a₀ r, ∀ y ∈ closedBall x (2 * r), c ≤ D a y v := by
  obtain ⟨v, hv, hpos⟩ := exists_unit_direction_apply_pos (D a₀ x) hne
  have hgap : {p : A × X | D a₀ x v / 2 < D p.1 p.2 v} ∈ 𝓝 (a₀, x) :=
    (hD.clm_apply continuousAt_const).preimage_mem_nhds
      (Ioi_mem_nhds (by dsimp; linarith))
  have hchart : {p : A × X | p.2 ∈ O} ∈ 𝓝 (a₀, x) :=
    continuousAt_snd.preimage_mem_nhds hO
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hgap hchart)
  refine ⟨v, ε / 4, D a₀ x v / 2, hv, by linarith, by linarith, ?_, ?_⟩
  · intro y hy
    have hp : (a₀, y) ∈ ball (a₀, x) ε := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa using hε, lt_of_le_of_lt hy (by linarith)⟩
    exact (hεsub hp).2
  · intro a ha y hy
    have hp : (a, y) ∈ ball (a₀, x) ε := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨lt_trans ha (by linarith), lt_of_le_of_lt hy (by linarith)⟩
    exact (hεsub hp).1.le

/-- Finite buffered transverse patches with a common positive gap and a common
parameter neighborhood (`app:ch_regular_base:prop:normalization`). The directions,
radii, and gap are constructed, not assumed. The compact set may in particular be
the protected unit set, and each `O x` may be a larger phase chart. -/
theorem exists_finite_buffered_transverse_cover (D : A → X → E →L[ℝ] ℝ)
    (a₀ : A) (K : Set X) (hK : IsCompact K)
    (hD : ∀ x ∈ K, ContinuousAt (Function.uncurry D) (a₀, x))
    (hne : ∀ x ∈ K, D a₀ x ≠ 0)
    (O : X → Set X) (hO : ∀ x ∈ K, O x ∈ 𝓝 x) :
    ∃ (s : Finset K) (v : K → E) (r : K → ℝ) (δ c : ℝ),
      0 < δ ∧ 0 < c ∧
      K ⊆ ⋃ x ∈ s, ball (x : X) (r x) ∧
      ∀ x ∈ s, ‖v x‖ = 1 ∧ 0 < r x ∧
        closedBall (x : X) (2 * r x) ⊆ O x ∧
        ∀ a ∈ ball a₀ δ, ∀ y ∈ closedBall (x : X) (2 * r x), c ≤ D a y (v x) := by
  classical
  have hlocal (x : K) := exists_buffered_transverse_ball D a₀ (x : X)
    (hD x x.property) (hne x x.property) (O x) (hO x x.property)
  choose v r c hv hr hc hchart hgap using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ ball (x : X) (r x))
    (fun _ ↦ isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  obtain ⟨δ, hδ, hδr⟩ := finite_positive_lower_bound s r (fun x _ ↦ hr x)
  obtain ⟨b, hb, hbc⟩ := finite_positive_lower_bound s c (fun x _ ↦ hc x)
  refine ⟨s, v, r, δ, b, hδ, hb, hs, ?_⟩
  intro x hx
  refine ⟨hv x, hr x, hchart x, ?_⟩
  intro a ha y hy
  exact (hbc x hx).trans (hgap x a (lt_of_lt_of_le ha (hδr x hx)) y hy)

/-- The finite-cover differential assertion of
`app:ch_regular_base:prop:normalization`, assembled for scalar symbols.

The inputs are positive degree-one homogeneity and differentiability off the origin,
continuity of the differential in both coefficients and point at the protected compact
set, and nonvanishing of the base differential only on the zero-energy surface.
Euler's identity discharges nonvanishing elsewhere. Each doubled closed ball lies in
the supplied chart and avoids the origin; the common gap persists on all its positive
rays and in one coefficient ball. In particular this applies to a compact unit set.
This statement does not assert the adjugate identities or symbol estimates. -/
theorem exists_finite_homogeneous_transverse_cover (q : A → E → ℝ)
    (a₀ : A) (K : Set E) (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0)
    (hhom : ∀ a, PosHomogeneousOne (q a))
    (hd : ∀ a x, x ≠ 0 → DifferentiableAt ℝ (q a) x)
    (hcont : ∀ x ∈ K,
      ContinuousAt (fun p : A × E ↦ fderiv ℝ (q p.1) p.2) (a₀, x))
    (hregular : ∀ x ∈ K, q a₀ x = 0 → fderiv ℝ (q a₀) x ≠ 0)
    (O : E → Set E) (hO : ∀ x ∈ K, O x ∈ 𝓝 x) :
    ∃ (s : Finset K) (v : K → E) (r : K → ℝ) (δ c : ℝ),
      0 < δ ∧ 0 < c ∧
      K ⊆ ⋃ x ∈ s, ball (x : E) (r x) ∧
      ∀ x ∈ s, ‖v x‖ = 1 ∧ 0 < r x ∧
        closedBall (x : E) (2 * r x) ⊆ O x ∩ {0}ᶜ ∧
        ∀ a ∈ ball a₀ δ, ∀ y ∈ closedBall (x : E) (2 * r x),
          ∀ t : ℝ, 0 < t → c ≤ fderiv ℝ (q a) (t • y) (v x) := by
  have hne (x : E) (hx : x ∈ K) : fderiv ℝ (q a₀) x ≠ 0 :=
    (hhom a₀).fderiv_ne_zero_of_regular_zero (hK0 x hx)
      (hd a₀ x (hK0 x hx)) (hregular x hx)
  obtain ⟨s, v, r, δ, c, hδ, hc, hcover, hpatch⟩ :=
    exists_finite_buffered_transverse_cover (fun a x ↦ fderiv ℝ (q a) x)
      a₀ K hK hcont hne (fun x ↦ O x ∩ {0}ᶜ)
      (fun x hx ↦ inter_mem (hO x hx) (compl_singleton_mem_nhds (hK0 x hx)))
  refine ⟨s, v, r, δ, c, hδ, hc, hcover, ?_⟩
  intro x hx
  obtain ⟨hv, hr, hchart, hgap⟩ := hpatch x hx
  refine ⟨hv, hr, hchart, ?_⟩
  intro a ha y hy t ht
  have hy0 : y ≠ 0 := (hchart hy).2
  rw [(hhom a).fderiv_smul hy0 (hd a y hy0) ht]
  exact hgap a ha y hy

end JanetCartan
