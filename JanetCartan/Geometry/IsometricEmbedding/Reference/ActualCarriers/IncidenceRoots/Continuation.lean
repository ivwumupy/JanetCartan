module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Frozen

/-!
# Actual incidence roots on fixed cylinders

Step 3 of `app:ch_seed:prop:seed-actual-menu`. The analytic inputs are
joint smoothness and explicit value/first-scalar-derivative closeness of the
literal current incidence. No current root or implicit solution is assumed.
The Hamilton-phase and pencil-continuity producers must supply these inputs.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- On a frozen buffered cylinder, construct the actual root, its joint
smoothness, fixed-interval uniqueness, interior containment and exact low
bounds. The threshold is chosen before the physical domain, frame and phase
(`app:ch_seed:prop:seed-actual-menu`, Step 3).

Only scalar-parameter `C¹` closeness is required, uniformly in physical and
covector variables. The physical derivatives need not be small. -/
theorem exists_current_incidence_root_on_cylinder {n : ℕ} {P : Patch n}
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀) (z : Euclidean 3) (k : Euclidean n)
    {r a c e : ℝ} (_hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (he : 0 < e)
    (hinterior : ∀ t ∈ Icc (-a) a, incidenceParameter z t ∈ parameterInterior P.radius)
    (hgap₀ : ∀ q ∈ Metric.closedBall k (2 * r), ∀ t ∈ Icc (-a) a,
      2 * c ≤ |scalarDerivative (frozenDeterminantIncidence P z) (q, t)|)
    (hend₀ : ∀ q ∈ Metric.closedBall k (2 * r),
      (frozenDeterminantIncidence P z (q, -a) ≤ -e ∧
        e ≤ frozenDeterminantIncidence P z (q, a)) ∨
      (frozenDeterminantIncidence P z (q, a) ≤ -e ∧
        e ≤ frozenDeterminantIncidence P z (q, -a))) :
    ∃ (δ : ℝ) (g₀ : Euclidean n → ℝ), 0 < δ ∧
      ContDiffOn ℝ ∞ g₀ (Metric.ball k (2 * r)) ∧
      (∀ q ∈ Metric.ball k (2 * r), g₀ q ∈ Ioo (-a) a ∧
        frozenDeterminantIncidence P z (q, g₀ q) = 0) ∧
      ∀ (X : Set (Euclidean n)), IsOpen X →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n)
          (Θ : Euclidean n → Euclidean 3 → ℝ) (ε : ℝ), ε ≤ δ →
        (∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
          ContDiffAt ℝ ∞ (currentIncidence Q Θ z) (p, t)) →
        (∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
          |currentIncidence Q Θ z (p, t) - frozenDeterminantIncidence P z (p.2, t)| ≤ ε ∧
          |scalarDerivative (currentIncidence Q Θ z) (p, t) -
            scalarDerivative (frozenDeterminantIncidence P z) (p.2, t)| ≤ ε) →
        ∃ g : Euclidean n × Euclidean n → ℝ,
          ContDiffOn ℝ ∞ g (X ×ˢ Metric.ball k (2 * r)) ∧
          ContDiffOn ℝ ∞ (fun p ↦ incidenceParameter z (g p))
            (X ×ˢ Metric.ball k (2 * r)) ∧
          (∀ p ∈ X ×ˢ Metric.ball k (2 * r),
            g p ∈ Ioo (-a) a ∧ incidenceParameter z (g p) ∈ parameterInterior P.radius ∧
            currentIncidence Q Θ z (p, g p) = 0 ∧
            c ≤ |scalarDerivative (currentIncidence Q Θ z) (p, g p)| ∧
            |g p - g₀ p.2| ≤ ε / c ∧
            ‖fderiv ℝ g p‖ ≤ ‖fderiv ℝ (currentIncidence Q Θ z) (p, g p)‖ / c) ∧
          (∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
            currentIncidence Q Θ z (p, t) = 0 ↔ g p = t) := by
  have hf₀ (q : Euclidean n) (t : ℝ) (ht : t ∈ Icc (-a) a) :
      ContDiffAt ℝ ∞ (frozenDeterminantIncidence P z) (q, t) :=
    contDiffAt_frozenDeterminantIncidence hP z (q, t) (fun i ↦ (hinterior t ht i).le)
  obtain ⟨g₀, hg₀, hroot₀, _⟩ := exists_smooth_root_on_interval
    Metric.isOpen_ball (by linarith : -a < a) hc
    (fun q _ t ht ↦ hf₀ q t ht)
    (fun q hq t ht ↦ (by linarith [hgap₀ q (Metric.ball_subset_closedBall hq) t ht]))
    (fun q hq ↦ (hend₀ q (Metric.ball_subset_closedBall hq)).imp
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩)
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩))
  refine ⟨min c (e / 2), g₀, lt_min hc (half_pos he), hg₀,
    fun q hq ↦ ⟨(hroot₀ q hq).1, (hroot₀ q hq).2.1⟩, ?_⟩
  intro X hX Q Θ ε hε hf hclose
  have hεc := hε.trans (min_le_left _ _)
  have hεe := hε.trans (min_le_right _ _)
  have hgap : ∀ p ∈ X ×ˢ Metric.ball k (2 * r), ∀ t ∈ Icc (-a) a,
      c ≤ |scalarDerivative (currentIncidence Q Θ z) (p, t)| := by
    intro p hp t ht
    have hd := (hclose p hp t ht).2
    have htri := abs_sub_abs_le_abs_sub
      (scalarDerivative (frozenDeterminantIncidence P z) (p.2, t))
      (scalarDerivative (currentIncidence Q Θ z) (p, t))
    rw [abs_sub_comm] at htri
    have hg := hgap₀ p.2 (Metric.ball_subset_closedBall hp.2) t ht
    linarith
  have hend : ∀ p ∈ X ×ˢ Metric.ball k (2 * r),
      (currentIncidence Q Θ z (p, -a) < 0 ∧ 0 < currentIncidence Q Θ z (p, a)) ∨
      (currentIncidence Q Θ z (p, a) < 0 ∧ 0 < currentIncidence Q Θ z (p, -a)) := by
    intro p hp
    have hl := abs_le.mp (hclose p hp (-a) ⟨le_rfl, by linarith⟩).1
    have hu := abs_le.mp (hclose p hp a ⟨by linarith, le_rfl⟩).1
    exact (hend₀ p.2 (Metric.ball_subset_closedBall hp.2)).imp
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩)
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩)
  have hU : IsOpen (X ×ˢ Metric.ball k (2 * r)) := hX.prod Metric.isOpen_ball
  obtain ⟨g, hg, hroot, huniq⟩ := exists_smooth_root_on_interval
    hU (by linarith : -a < a) hc hf hgap hend
  refine ⟨g, hg, contDiffOn_const.add (hg.smul contDiffOn_const), ?_, huniq⟩
  intro p hp
  have ht := Ioo_subset_Icc_self (hroot p hp).1
  have ht₀ := Ioo_subset_Icc_self (hroot₀ p.2 hp.2).1
  refine ⟨(hroot p hp).1, hinterior _ ht, (hroot p hp).2.1, (hroot p hp).2.2, ?_, ?_⟩
  · have hdist := scalar_gap_mul_abs_sub_le
      (fun t ht ↦ (hf p hp t ht).differentiableAt (by simp)) (hgap p hp) ht₀ ht
    have hval := (hclose p hp (g₀ p.2) ht₀).1
    rw [(hroot₀ p.2 hp.2).2.1, sub_zero] at hval
    rw [(hroot p hp).2.1, zero_sub, abs_neg] at hdist
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  · apply norm_fderiv_root_le hc ((hf p hp _ ht).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      _ (hroot p hp).2.2 le_rfl
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hroot q hq).2.1

end JanetCartan.ActualCarriers
