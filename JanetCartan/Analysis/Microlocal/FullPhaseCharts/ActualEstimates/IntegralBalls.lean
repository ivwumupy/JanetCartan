module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.ChartCoordinates

/-!
# Positive balls for the two literal integrations

The full and transverse actual phases use the same elementary ball construction.
This closes the ball-containment inputs of `InverseEstimates.PhaseBounds` from
open primitive domains and continuity of the frozen carrier. No phase estimate
or inverse estimate is an input. The centers have zero physical coordinates and
zero epsilon, retaining a two-sided neighborhood as required by
`app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Topology

namespace JanetCartan.FullPhaseCharts.ActualEstimates
open InverseEstimates

variable {R D X E : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Construct all positive source and target balls for the literal covector
and physical integrations. This geometric lemma is instantiated for both
actual maps; the ball radius can subsequently cap the data and physical boxes
of `app:ch_seed:prop:seed-phase-charts`. -/
theorem exists_carrier_integration_balls
    (p₀ : R × D) (z v : R × D → E)
    {V : Set (R × D)} {I : Set ℝ} {U B : Set X} {Z : Set E}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hB : IsOpen B) (hZ : IsOpen Z)
    (hp₀ : p₀ ∈ V) (hI₀ : (0 : ℝ) ∈ I) (hU₀ : (0 : X) ∈ U)
    (hB₀ : (0 : X) ∈ B) (hZ₀ : z p₀ ∈ Z)
    (hz : ContinuousAt z p₀) (hv : ContinuousAt v p₀) :
    ∃ σ > (0 : ℝ), ∃ ρ > (0 : ℝ),
      closedBall ((p₀, (0 : X)), z p₀) σ ⊆ (V ×ˢ U) ×ˢ Z ∧
      closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ ⊆ (V ×ˢ I) ×ˢ U ∧
      closedBall p₀ ρ ⊆ V ∧
      closedBall ((p₀, (0 : ℝ)), ((0 : X), (0 : X))) ρ ⊆ (V ×ˢ I) ×ˢ B ×ˢ B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (carrierSubstitution z v t)
        (closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ)
        (closedBall ((p₀, (0 : X)), z p₀) σ)) ∧
      (∀ q ∈ closedBall ((p₀, (0 : ℝ)), ((0 : X), (0 : X))) ρ,
        ∀ t ∈ Icc (0 : ℝ) 1,
          jointPhysicalSegment t q ∈ closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ) ∧
      MapsTo quotientChartReindex
        (closedBall (((0 : ℝ), (p₀.1, (0 : X), (0 : X))), p₀.2) ρ)
        (closedBall ((p₀, (0 : ℝ)), ((0 : X), (0 : X))) ρ) := by
  obtain ⟨σ, hσ, htarget⟩ := nhds_basis_closedBall.mem_iff.mp
    (((hV.prod hU).prod hZ).mem_nhds (show ((p₀, (0 : X)), z p₀) ∈ (V ×ˢ U) ×ˢ Z from ⟨⟨hp₀, hU₀⟩, hZ₀⟩))
  obtain ⟨d, hd, hsource⟩ := nhds_basis_closedBall.mem_iff.mp
    (((hV.prod hI).prod (hU.inter hB)).mem_nhds (show ((p₀, (0 : ℝ)), (0 : X)) ∈ (V ×ˢ I) ×ˢ (U ∩ B) from ⟨⟨hp₀, hI₀⟩, hU₀, hB₀⟩))
  obtain ⟨dz, hdz, hzclose⟩ := Metric.continuousAt_iff.mp hz (σ / 4) (by positivity)
  obtain ⟨dv, hdv, hvclose⟩ := Metric.continuousAt_iff.mp hv 1 zero_lt_one
  let M := ‖v p₀‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let ρ := min d (min (dz / 2) (min (dv / 2) (min (σ / 2) (σ / (4 * M)))))
  have hρ : 0 < ρ := lt_min hd (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hρd : ρ ≤ d := min_le_left _ _
  have hρz : ρ < dz := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hρv : ρ < dv := lt_of_le_of_lt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) (by linarith)
  have hρσ : ρ ≤ σ / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρM : ρ * M ≤ σ / 4 := by
    have hh : ρ ≤ σ / (4 * M) := (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hh' := (le_div_iff₀ (by positivity : 0 < 4 * M)).mp hh
    nlinarith
  have hsrc : closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ ⊆ (V ×ˢ I) ×ˢ (U ∩ B) :=
    (closedBall_subset_closedBall hρd).trans hsource
  have hparts (q : ((R × D) × ℝ) × X)
      (hq : q ∈ closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ) :
      q.1.1 ∈ closedBall p₀ ρ ∧ q.1.2 ∈ closedBall (0 : ℝ) ρ ∧ q.2 ∈ closedBall (0 : X) ρ := by
    simpa only [← closedBall_prod_same, mem_prod, and_assoc] using hq
  have ha : closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ ⊆ (V ×ˢ I) ×ˢ U :=
    fun q hq ↦ ⟨(hsrc hq).1, (hsrc hq).2.1⟩
  have hp : closedBall p₀ ρ ⊆ V := by
    intro p hp
    have hm : ((p, (0 : ℝ)), (0 : X)) ∈ closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ := by
      simpa only [← closedBall_prod_same, mem_prod] using
        And.intro (And.intro hp (mem_closedBall_self (x := (0 : ℝ)) hρ.le)) (mem_closedBall_self (x := (0 : X)) hρ.le)
    exact (ha hm).1.1
  refine ⟨σ, hσ, ρ, hρ, htarget, ha, hp, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq' : (q.1.1 ∈ closedBall p₀ ρ ∧ q.1.2 ∈ closedBall (0 : ℝ) ρ) ∧
        q.2.1 ∈ closedBall (0 : X) ρ ∧ q.2.2 ∈ closedBall (0 : X) ρ := by
      simpa only [← closedBall_prod_same, mem_prod] using hq
    have hx : (q.1, q.2.1) ∈ closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ := by
      simpa only [← closedBall_prod_same, mem_prod] using And.intro hq'.1 hq'.2.1
    have hy : (q.1, q.2.2) ∈ closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ := by
      simpa only [← closedBall_prod_same, mem_prod] using And.intro hq'.1 hq'.2.2
    exact ⟨(hsrc hx).1, (hsrc hx).2.2, (hsrc hy).2.2⟩
  · intro t ht q hq
    obtain ⟨hp, he, hx⟩ := hparts q hq
    have hz' : dist (z q.1.1) (z p₀) < σ / 4 := hzclose (hp.trans_lt hρz)
    have hv' : ‖v q.1.1‖ ≤ M := by
      have hh := norm_le_insert' (v q.1.1) (v p₀)
      have hh' := hvclose (hp.trans_lt hρv)
      rw [dist_eq_norm] at hh'
      dsimp [M]
      linarith
    have he' : |q.1.2| ≤ ρ := by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using he
    have hs : ‖(t * q.1.2) • v q.1.1‖ ≤ ρ * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul ((mul_le_mul ht.2 he' (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
        hv' (norm_nonneg _) hρ.le
    have hzσ : z q.1.1 + (t * q.1.2) • v q.1.1 ∈ closedBall (z p₀) σ := by
      rw [mem_closedBall, dist_eq_norm]
      calc
        _ ≤ ‖z q.1.1 - z p₀‖ + ‖(t * q.1.2) • v q.1.1‖ := by
          simpa only [add_sub_right_comm] using norm_add_le
            (z q.1.1 - z p₀) ((t * q.1.2) • v q.1.1)
        _ ≤ σ / 4 + ρ * M := add_le_add (by simpa only [dist_eq_norm] using hz'.le) hs
        _ ≤ σ := by linarith
    have hpσ := closedBall_subset_closedBall (by linarith : ρ ≤ σ) hp
    have hxσ := closedBall_subset_closedBall (by linarith : ρ ≤ σ) hx
    simpa only [carrierSubstitution, ← closedBall_prod_same, mem_prod] using
      And.intro (And.intro hpσ hxσ) hzσ
  · intro q hq t ht
    have hq' : (q.1.1 ∈ closedBall p₀ ρ ∧ q.1.2 ∈ closedBall (0 : ℝ) ρ) ∧
        q.2.1 ∈ closedBall (0 : X) ρ ∧ q.2.2 ∈ closedBall (0 : X) ρ := by
      simpa only [← closedBall_prod_same, mem_prod] using hq
    have hx := (convex_closedBall (0 : X) ρ).add_smul_sub_mem hq'.2.2 hq'.2.1 ht
    simpa only [jointPhysicalSegment_apply, ← closedBall_prod_same, mem_prod] using
      And.intro hq'.1 hx
  · intro q hq
    simpa only [quotientChartReindex_apply, mem_closedBall, Prod.dist_eq,
      max_le_iff, Prod.eta, and_assoc, and_left_comm, and_comm] using hq

end JanetCartan.FullPhaseCharts.ActualEstimates
