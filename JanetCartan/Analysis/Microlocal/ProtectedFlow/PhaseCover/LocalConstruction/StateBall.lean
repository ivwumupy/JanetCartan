module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.ChartData
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TransverseCompatibility

/-!
# The state ball for a local comparison family

The finite comparison-phase paragraph of `app:ch_regular:thm:no-return`
requires one state ball with a transverse gap and a uniform regular angular
buffer. These lemmas supply the state ball and identify the central momentum
of the actual family member used by `exists_localComparisonFamily`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- One state ball simultaneously supplies the frozen transverse gap, momentum
bounds and a positive angular buffer for `exists_localComparisonFamily`
(`app:ch_regular:thm:no-return`). -/
theorem exists_regular_transverse_stateBall
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) {ξ : E} (hξ : ξ ≠ 0) (hz : (0, ξ) ∈ D)
    (hν : H₀.hp (0, ξ) ≠ 0) {G M : Set E} (hG : IsOpen G) (hM : IsClosed M)
    (hreg : normalizedCovector ξ ∈ G \ M) :
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ closedBall ((0 : E), ξ) R ⊆ D ∧
      (∀ z ∈ closedBall ((0 : E), ξ) R, ⟪H₀.hp z, H₀.hp (0, ξ)⟫_ℝ ≠ 0) ∧
      ∀ z ∈ closedBall ((0 : E), ξ) R,
        ‖ξ‖ / 2 ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ ‖ξ‖ + R ∧
          closedBall (normalizedCovector z.2) b ⊆ G \ M := by
  obtain ⟨a, ha, haG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hG.inter hM.isOpen_compl).mem_nhds hreg)
  have hn : ContinuousAt (fun z : E × E ↦ normalizedCovector z.2) (0, ξ) :=
    (continuousAt_snd.norm.inv₀ (norm_ne_zero_iff.mpr hξ)).smul continuousAt_snd
  have ht : ContinuousAt (fun z ↦ ⟪H₀.hp z, H₀.hp (0, ξ)⟫_ℝ) (0, ξ) :=
    ((H₀.hasFDerivAt_hp _ (hDH₀ hz)).continuousAt).inner continuousAt_const
  have hgap : ∀ᶠ z in 𝓝 (0, ξ), ⟪H₀.hp z, H₀.hp (0, ξ)⟫_ℝ ≠ 0 :=
    ht.eventually_ne (inner_self_ne_zero.mpr hν)
  have hnorm : ∀ᶠ z : E × E in 𝓝 (0, ξ), ‖ξ‖ / 2 < ‖z.2‖ :=
    continuousAt_snd.norm.eventually (Ioi_mem_nhds (by
      change ‖ξ‖ / 2 < ‖ξ‖
      exact half_lt_self (norm_pos_iff.mpr hξ)))
  have hang : ∀ᶠ z : E × E in 𝓝 (0, ξ),
      normalizedCovector z.2 ∈ ball (normalizedCovector ξ) (a / 2) :=
    hn.preimage_mem_nhds (ball_mem_nhds _ (half_pos ha))
  have hall : {z : E × E | z ∈ D ∧ ⟪H₀.hp z, H₀.hp (0, ξ)⟫_ℝ ≠ 0 ∧
      ‖ξ‖ / 2 < ‖z.2‖ ∧ normalizedCovector z.2 ∈ ball (normalizedCovector ξ) (a / 2)}
      ∈ 𝓝 (0, ξ) := by
    filter_upwards [hD.mem_nhds hz, hgap, hnorm, hang] with z hz ht hn ha
    exact ⟨hz, ht, hn, ha⟩
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hall
  refine ⟨R, a / 2, hR, half_pos ha, fun z hz ↦ (hball hz).1,
    fun z hz ↦ (hball hz).2.1, fun z hz ↦ ⟨(hball hz).2.2.1.le, ?_, ?_⟩⟩
  · have hp : dist z.2 ξ ≤ R := (le_max_right _ _).trans (by simpa only [mem_closedBall, Prod.dist_eq] using hz)
    have hh := norm_add_le (z.2 - ξ) ξ
    rw [sub_add_cancel, ← dist_eq_norm] at hh
    linarith
  · intro p hp
    apply haG
    have hnear := (hball hz).2.2.2
    have hdist := dist_triangle p (normalizedCovector z.2) (normalizedCovector ξ)
    rw [mem_closedBall] at hp ⊢
    rw [mem_ball] at hnear
    linarith

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

omit [FiniteDimensional ℝ E] in
/-- Scalar-root uniqueness identifies the central flow momentum with its
prescribed tangent covector. This identifies the frozen member of the actual
common family in `exists_localComparisonFamily`, without identifying it with
the separate continuity-reference chart (`app:lem:common-hamilton-phase`). -/
theorem initial_momentum_eq_of_transverse_patch
    {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    {K : Set (E × E)} (hK : Convex ℝ K) (hKH : K ⊆ H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (hgap : ∀ z ∈ K, ⟪H.hp z, ν⟫_ℝ ≠ 0)
    {s : InitialData U} (hs : s ∈ Φ.parameters)
    (hrange : (Φ.position (0, s), Φ.momentum (0, s)) ∈ K)
    (hcenter : (j s.1, j s.2.2) ∈ K)
    (henergy : H.h (j s.1, j s.2.2) = s.2.1) :
    Φ.momentum (0, s) = j s.2.2 := by
  let p := Φ.momentum (0, s)
  let p' := j s.2.2
  let a := ⟪ν, p⟫_ℝ / ⟪ν, ν⟫_ℝ
  have hx : Φ.position (0, s) = j s.1 := by
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_position s hs
  have hp : p = a • ν + j s.2.2 :=
    sectionMomentum_eq_normal_add_tangent j ν p hν horth hspan s.2.2
      (by simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_momentum s hs)
  have hdiff : p' - p = (-a) • ν := by rw [hp]; dsimp [p']; module
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (j s.1, p + t • (p' - p)) ∈ K := by
    have hh := hK.add_smul_sub_mem hrange hcenter ht
    simpa [hx, p, p', Prod.mk_add_mk, Prod.mk_sub_mk] using hh
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
  have hf0 : f 0 = s.2.1 := by simpa [f, p, hx] using Φ.initial_energy s hs
  have hf1 : f 1 = s.2.1 := by simpa [f, p'] using henergy
  rw [hf1, hf0, sub_self, zero_div, hdiff, inner_smul_right] at he
  have hnonzero := hgap _ (hmem t (Ioo_subset_Icc_self ht))
  rw [hdiff] at hnonzero
  have ha : -a = 0 := (mul_eq_zero.mp he).resolve_right hnonzero
  simpa only [neg_eq_zero.mp ha, zero_smul, zero_add] using hp

end JanetCartan.ProtectedFlow.PhaseCover
