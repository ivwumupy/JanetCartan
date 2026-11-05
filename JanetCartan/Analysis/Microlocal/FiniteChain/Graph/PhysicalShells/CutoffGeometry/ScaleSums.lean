module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.Volumes
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.Overlap

/-!
# Scale-relative counts and carrier volume sums

The physical pair estimates in `app:ch_regular:eq:chain-tail` sum graph
and output indices independently. Bounded overlap controls all carriers
inside a ball by its volume, without a logarithmic loss in the scale.
The comparable annular counts depend only on the ratio of its endpoints.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
variable {n : ℕ}

private theorem sum_carrier_volume_le (K : ℕ → Set (Euclidean n))
    (hK : ∀ j, IsCompact (K j)) (D : ℕ)
    (hcount : ∀ (s : Finset ℕ) ξ, (∀ j ∈ s, ξ ∈ K j) → s.card ≤ D)
    (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ j ∈ s, K j ⊆ closedBall 0 R) :
    ∑ j ∈ s, volume.real (K j) ≤ (D : ℝ) * R ^ n * frequencyBallVolume n := by
  classical
  have hint (j : ℕ) : Integrable ((K j).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff (hK j).measurableSet).mpr
      (integrableOn_const (hK j).measure_ne_top)
  have hball : Integrable ((closedBall (0 : Euclidean n) R).indicator (fun _ => (D : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (isCompact_closedBall _ _).measure_ne_top)
  have hpoint (ξ : Euclidean n) :
      (∑ j ∈ s, (K j).indicator (fun _ => (1 : ℝ)) ξ) ≤
        (closedBall (0 : Euclidean n) R).indicator (fun _ => (D : ℝ)) ξ := by
    by_cases hξ : ξ ∈ closedBall (0 : Euclidean n) R
    · rw [indicator_of_mem hξ]
      simp only [indicator_apply, Finset.sum_boole]
      exact_mod_cast hcount (s.filter (fun j => ξ ∈ K j)) ξ
        (fun j hj => (Finset.mem_filter.mp hj).2)
    · rw [indicator_of_notMem hξ]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro j hj
      exact indicator_of_notMem (fun h => hξ (hsub j hj h)) _
  calc
    _ = ∫ ξ, ∑ j ∈ s, (K j).indicator (fun _ => (1 : ℝ)) ξ := by
      rw [integral_finsetSum s (fun j _ => hint j)]
      simp only [integral_indicator_const _ (hK _).measurableSet, smul_eq_mul, mul_one]
    _ ≤ ∫ ξ, (closedBall (0 : Euclidean n) R).indicator (fun _ => (D : ℝ)) ξ :=
      integral_mono (integrable_finsetSum s (fun j _ => hint j)) hball hpoint
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_closedBall,
        smul_eq_mul, volume_real_frequency_closedBall hR]
      ring

/-- All high graph carriers inside radius `R` have total volume at most
three times that ball's volume. This prevents a scale-dependent counting
loss in `app:ch_regular:eq:chain-tail`. -/
theorem sum_volume_real_highGraphCutoff_le (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ j ∈ s, tsupport (highGraphCutoff (n := n) j) ⊆ closedBall 0 R) :
    ∑ j ∈ s, volume.real (tsupport (highGraphCutoff (n := n) j)) ≤
      3 * R ^ n * frequencyBallVolume n :=
  sum_carrier_volume_le _ hasCompactSupport_highGraphCutoff 3
    card_highGraphCutoff_overlap_le s hR hsub

/-- All low graph carriers inside radius `R` obey the same volume bound,
uniformly over arbitrarily deep contractions (`app:ch_regular:eq:chain-tail`). -/
theorem sum_volume_real_lowGraphCutoff_le (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ j ∈ s, tsupport (lowGraphCutoff (n := n) j) ⊆ closedBall 0 R) :
    ∑ j ∈ s, volume.real (tsupport (lowGraphCutoff (n := n) j)) ≤
      3 * R ^ n * frequencyBallVolume n :=
  sum_carrier_volume_le _ hasCompactSupport_lowGraphCutoff 3
    card_lowGraphCutoff_overlap_le s hR hsub

/-- The independent output carrier sum includes its low ball with a uniform
constant (`app:ch_regular:eq:chain-tail`). -/
theorem sum_volume_real_outputCutoff_le (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ k ∈ s, tsupport (outputCutoff (n := n) k) ⊆ closedBall 0 R) :
    ∑ k ∈ s, volume.real (tsupport (outputCutoff (n := n) k)) ≤
      4 * R ^ n * frequencyBallVolume n :=
  sum_carrier_volume_le _ hasCompactSupport_outputCutoff 4
    card_outputCutoff_overlap_le s hR hsub

/-- The independent high graph/output volume sum at radius `R`. This is
the rectangular sum used when grouping pairs by their largest frequency
in `app:ch_regular:eq:chain-tail`. -/
theorem sum_highGraphCutoff_outputCutoff_volume_le (s t : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, tsupport (highGraphCutoff (n := n) j) ⊆ closedBall 0 R)
    (ht : ∀ k ∈ t, tsupport (outputCutoff (n := n) k) ⊆ closedBall 0 R) :
    ∑ j ∈ s, ∑ k ∈ t,
      volume.real (tsupport (highGraphCutoff (n := n) j)) *
        volume.real (tsupport (outputCutoff (n := n) k)) ≤
      12 * R ^ (2 * n) * frequencyBallVolume n ^ 2 := by
  rw [← Finset.sum_mul_sum]
  have hV := frequencyBallVolume_nonneg n
  have h := mul_le_mul (sum_volume_real_highGraphCutoff_le s hR hs)
    (sum_volume_real_outputCutoff_le t hR ht)
    (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))
    (by positivity : 0 ≤ 3 * R ^ n * frequencyBallVolume n)
  convert h using 1
  rw [pow_mul]
  ring

/-- The low graph/output rectangular volume sum has the same bound; small
graph frequencies are retained in `app:ch_regular:eq:chain-tail`. -/
theorem sum_lowGraphCutoff_outputCutoff_volume_le (s t : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, tsupport (lowGraphCutoff (n := n) j) ⊆ closedBall 0 R)
    (ht : ∀ k ∈ t, tsupport (outputCutoff (n := n) k) ⊆ closedBall 0 R) :
    ∑ j ∈ s, ∑ k ∈ t,
      volume.real (tsupport (lowGraphCutoff (n := n) j)) *
        volume.real (tsupport (outputCutoff (n := n) k)) ≤
      12 * R ^ (2 * n) * frequencyBallVolume n ^ 2 := by
  rw [← Finset.sum_mul_sum]
  have hV := frequencyBallVolume_nonneg n
  have h := mul_le_mul (sum_volume_real_lowGraphCutoff_le s hR hs)
    (sum_volume_real_outputCutoff_le t hR ht)
    (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))
    (by positivity : 0 ≤ 3 * R ^ n * frequencyBallVolume n)
  convert h using 1
  rw [pow_mul]
  ring

end JanetCartan.FiniteChain.Graph.PhysicalShells
