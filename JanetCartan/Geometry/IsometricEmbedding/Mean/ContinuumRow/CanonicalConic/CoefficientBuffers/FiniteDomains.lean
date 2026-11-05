module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Finite coefficient and segment domains inside the canonical cone

An arbitrary open coefficient region determines a positive cap. For every
smaller actual input ball, compactness enlarges it inside the outer cone.
Projection and convexity give one field ball containing the coefficient
arguments, all physical segments, and the smaller original mask supports.
All domains are chosen before the varying projected-stress field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol
variable {n : ℕ}

private theorem coefficient_lift_mem_closedBall (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {p : Euclidean n × CarrierParameter}
    (hp : p ∈ closedBall ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ρ) :
    (((p.1, p.1), p.2, ηb) : InputVariables n) ∈
      closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ := by
  simp only [← closedBall_prod_same, mem_prod] at hp ⊢
  exact ⟨⟨hp.1, hp.1⟩, hp.2, mem_closedBall_self hρ⟩

private theorem coefficient_segment_mem_closedBall (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) {d : ℝ} {p : InputVariables n}
    (hp : p ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) d)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    transportSegmentInput n t p ∈
      closedBall ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) d := by
  simp only [← closedBall_prod_same, mem_prod] at hp ⊢
  exact ⟨(convex_closedBall (0 : Euclidean n) d).add_smul_sub_mem hp.1.2 hp.1.1 ht,
    hp.2.1⟩

private theorem coefficient_segment_mem_ball (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) {d s : ℝ} (hd : 0 < d) (hds : d < s)
    {p : InputVariables n}
    (hp : p ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) d)
    {t : ℝ} (ht : t ∈ Ioo (-(s - d) / (4 * d)) (1 + (s - d) / (4 * d))) :
    transportSegmentInput n t p ∈
      ball ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) s := by
  simp only [← closedBall_prod_same, mem_prod] at hp
  have hx : ‖p.1.1‖ ≤ d := by simpa only [mem_closedBall, dist_zero_right] using hp.1.1
  have hy : ‖p.1.2‖ ≤ d := by simpa only [mem_closedBall, dist_zero_right] using hp.1.2
  let e := (s - d) / (4 * d)
  have he : 0 < e := div_pos (sub_pos.mpr hds) (by positivity)
  have het : -e < t ∧ t < 1 + e := by simpa only [e, neg_div, mem_Ioo] using ht
  have heq : e * (4 * d) = s - d := div_mul_cancel₀ _ (by positivity : 4 * d ≠ 0)
  have habs : |1 - t| + |t| ≤ 1 + 2 * e := by
    rcases le_total t 0 with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonpos h]
      linarith [het.1]
    · rcases le_total t 1 with h' | h'
      · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg h]
        linarith
      · rw [abs_of_nonpos (by linarith : 1 - t ≤ 0), abs_of_nonneg h]
        linarith [het.2]
  have hn : ‖p.1.2 + t • (p.1.1 - p.1.2)‖ < s := by
    calc
      _ = ‖(1 - t) • p.1.2 + t • p.1.1‖ := by congr 1; module
      _ ≤ ‖(1 - t) • p.1.2‖ + ‖t • p.1.1‖ := norm_add_le _ _
      _ = |1 - t| * ‖p.1.2‖ + |t| * ‖p.1.1‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ |1 - t| * d + |t| * d := add_le_add
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = (|1 - t| + |t|) * d := by ring
      _ ≤ (1 + 2 * e) * d := mul_le_mul_of_nonneg_right habs hd.le
      _ < s := by nlinarith
  change (p.1.2 + t • (p.1.1 - p.1.2), p.2.1) ∈ _
  rw [← ball_prod_same]
  exact ⟨by simpa only [mem_ball, dist_zero_right] using hn,
    closedBall_subset_ball hds (by simpa only [← closedBall_prod_same, mem_prod] using hp.2.1)⟩

/-- Fixed finite domains for the canonical coefficients and every physical segment.
The cap is chosen from the arbitrary open coefficient region before the input
radius; the input ball and smaller original masks are the outputs of
`exists_actual_refined_supported_geometry`. Consumer:
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`, through
`CanonicalCarrier.exists_canonical_primitive_controls`.
Sources: `app:ch_background:eq:bg-Psi`, `bg-mixed-input`, and
`bg-full-complex-amplitude`. -/
theorem exists_coefficient_buffers_cap (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) (hηb : ηb ≠ 0)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E) :
    ∃ cap > (0 : ℝ), ∀ {r a ρ : ℝ}, 0 < ρ → ρ < cap →
      let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
      closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) →
      ∃ (W K : Set (InputVariables n))
        (Vphase Lphase : Set (Euclidean n × CarrierParameter))
        (I : Set ℝ) (D : CoefficientNormCharts n) (ε : ℝ),
        IsOpen W ∧ IsCompact K ∧ closedBall p₀ ρ ⊆ W ∧ W ⊆ K ∧
        K ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
        IsOpen Vphase ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase ∧
        IsOpen I ∧ (∃ l u : ℝ, I = Ioo l u) ∧ Icc (0 : ℝ) 1 ⊆ I ∧
        (∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase) ∧
        D.field.carrier = Lphase ∧ D.field.region = Vphase ∧
        Vphase ⊆ E ∩ coefficientDomain z₀ r (6 * a) ∧
        (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
        (∀ {a' : ℝ} (ha' : 0 < a'), 4 * a' < ρ →
          tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
            carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
        0 < ε ∧ (∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖) := by
  let c₀ : Euclidean n × CarrierParameter := (0, (z₀ 0, spectatorCenter z₀))
  let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
  obtain ⟨e, he, heE⟩ := Metric.mem_nhds_iff.mp (hE.mem_nhds hcenter)
  let cap := min e (‖ηb‖ / 2)
  have hcap : 0 < cap := lt_min he (half_pos (norm_pos_iff.mpr hηb))
  have hcapE : ball c₀ cap ⊆ E := (ball_subset_ball (min_le_left _ _)).trans heE
  refine ⟨cap, hcap, ?_⟩
  intro r a ρ hρ hρcap
  dsimp only
  intro hinput
  change closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) at hinput
  have hsmall : closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) ∩ ball p₀ cap :=
    subset_inter hinput (closedBall_subset_ball hρcap)
  obtain ⟨q, hq, hlarge⟩ := (isCompact_closedBall p₀ ρ).exists_cthickening_subset_open
    ((symbolInputDomain_open z₀ ηb r (6 * a)).inter isOpen_ball) hsmall
  rw [cthickening_closedBall hq.le hρ.le] at hlarge
  let s := q + ρ
  let d := (ρ + s) / 2
  have hρd : ρ < d := by dsimp [d, s]; linarith
  have hds : d < s := by dsimp [d, s]; linarith
  have hd : 0 < d := hρ.trans hρd
  have hs : 0 < s := hd.trans hds
  have hfield : closedBall c₀ s ⊆ E ∩ coefficientDomain z₀ r (6 * a) := by
    intro p hp
    have hl := coefficient_lift_mem_closedBall z₀ ηb hs.le hp
    have hl' := hlarge hl
    have hv := (coefficient_evaluation_ranges z₀ ηb r (6 * a)).1 hl'.1
    refine ⟨hcapE ?_, hv⟩
    have hb := hl'.2
    simp only [p₀, ← ball_prod_same, mem_prod] at hb
    simpa only [c₀, ← ball_prod_same, mem_prod] using And.intro hb.1.1 hb.2.1
  let D : CoefficientNormCharts n := {
    measurement := ⟨0, ρ, hρ, univ, isOpen_univ, subset_univ _⟩
    angular := ⟨((z₀ 0, spectatorCenter z₀), 0), ρ + 1, by positivity,
      univ, isOpen_univ, subset_univ _⟩
    high := ⟨‖ηb‖, ρ, hρ, univ, isOpen_univ, subset_univ _⟩
    field := ⟨c₀, d, hd, ball c₀ s, isOpen_ball, closedBall_subset_ball hds⟩ }
  let I := Ioo (-(s - d) / (4 * d)) (1 + (s - d) / (4 * d))
  have hext : 0 < (s - d) / (4 * d) := div_pos (sub_pos.mpr hds) (by positivity)
  refine ⟨ball p₀ d, closedBall p₀ d, ball c₀ s, closedBall c₀ d, I, D,
    ‖ηb‖ / 2, isOpen_ball, isCompact_closedBall _ _, closedBall_subset_ball hρd,
    ball_subset_closedBall, ?_, isOpen_ball, isCompact_closedBall _ _,
    closedBall_subset_ball hds, isOpen_Ioo, ⟨_, _, rfl⟩, ?_, ?_, ?_,
    rfl, rfl, ball_subset_closedBall.trans hfield, ?_, ?_,
    half_pos (norm_pos_iff.mpr hηb), ?_⟩
  · exact (closedBall_subset_closedBall hds.le).trans (fun _ hp ↦ (hlarge hp).1)
  · intro t ht
    change -(s - d) / (4 * d) < t ∧ t < 1 + (s - d) / (4 * d)
    rw [neg_div]
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht p hp
    exact coefficient_segment_mem_ball z₀ ηb hd hds (ball_subset_closedBall hp) ht
  · intro t ht p hp
    exact coefficient_segment_mem_closedBall z₀ ηb (ball_subset_closedBall hp) ht
  · intro p hp
    have hp' := hp
    simp only [← closedBall_prod_same, mem_prod] at hp'
    have hn : ‖‖p.2.2‖⁻¹ • p.2.2‖ = 1 :=
      NormedSpace.norm_normalize (hinput hp).2.2.1
    change p.1.1 ∈ closedBall 0 ρ ∧ p.1.2 ∈ closedBall 0 ρ ∧
      (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ∈ closedBall ((z₀ 0, spectatorCenter z₀), 0) (ρ + 1) ∧
      ‖p.2.2‖ ∈ closedBall ‖ηb‖ ρ ∧
      (p.1.1, p.2.1) ∈ closedBall c₀ d ∧ (p.1.2, p.2.1) ∈ closedBall c₀ d
    refine ⟨hp'.1.1, hp'.1.2, ?_, ?_, ?_, ?_⟩
    · simp only [← closedBall_prod_same, mem_prod]
      refine ⟨⟨closedBall_subset_closedBall (by linarith) hp'.2.1.1,
        closedBall_subset_closedBall (by linarith) hp'.2.1.2⟩, ?_⟩
      simp only [mem_closedBall, dist_zero_right, hn]
      linarith
    · exact (dist_norm_norm_le _ _).trans (mem_closedBall_iff_norm.mp hp'.2.2)
    · apply closedBall_subset_closedBall hρd.le
      simpa only [c₀, ← closedBall_prod_same, mem_prod] using And.intro hp'.1.1 hp'.2.1
    · apply closedBall_subset_closedBall hρd.le
      simpa only [c₀, ← closedBall_prod_same, mem_prod] using And.intro hp'.1.2 hp'.2.1
  · intro a' ha' haρ p hp
    change p ∈ closedBall c₀ d
    have hx := FixedCutoffs.physical_tsupport_four ha' 1 hp.1
    have hz := hp.2
    change p.2.1 ∈ closedBall (z₀ 0) (a' / 2) ∧
      p.2.2 ∈ closedBall (spectatorCenter z₀) (a' / 2) at hz
    simp only [c₀, ← closedBall_prod_same, mem_prod]
    exact ⟨closedBall_subset_closedBall (by linarith) hx,
      closedBall_subset_closedBall (by linarith) hz.1,
      closedBall_subset_closedBall (by linarith) hz.2⟩
  · intro p hp
    have hp' := hp
    simp only [← closedBall_prod_same, mem_prod] at hp'
    have hn : ‖ηb‖ - ‖p.2.2‖ ≤ ρ := (norm_sub_norm_le _ _).trans
      (by simpa only [norm_sub_rev] using mem_closedBall_iff_norm.mp hp'.2.2)
    have hc : cap ≤ ‖ηb‖ / 2 := min_le_right _ _
    linarith

end JanetCartan.ContinuumRow.CanonicalConic
