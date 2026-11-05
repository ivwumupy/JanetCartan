module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.Support

/-!
# Uniform overlap of the physical cutoff carriers

All counts are for the closed supports of the actual cutoffs. They supply
the bounded-overlap input to the independent graph/output summation in
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
variable {n : ℕ}

private theorem card_le_of_index_width (s : Finset ℕ) (d : ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, j ≤ i + d) : s.card ≤ d + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hsub : s ⊆ Finset.Icc (s.min' hs) (s.min' hs + d) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨s.min'_le j hj, h _ (s.min'_mem hs) j hj⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega

/-- Overlapping high graph carriers have indices separated by at most two
(`app:ch_regular:eq:chain-tail`). -/
theorem highGraphCutoff_overlap_index_le {i j : ℕ} {ξ : Euclidean n}
    (hi : ξ ∈ tsupport (highGraphCutoff i)) (hj : ξ ∈ tsupport (highGraphCutoff j)) :
    j ≤ i + 2 := by
  apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
  exact (tsupport_highGraphCutoff_subset j hj).1.trans (tsupport_highGraphCutoff_subset i hi).2

/-- Overlapping low graph carriers also have uniformly close indices, even
at arbitrarily small frequencies (`app:ch_regular:eq:chain-tail`). -/
theorem lowGraphCutoff_overlap_index_le {i j : ℕ} {ξ : Euclidean n}
    (hi : ξ ∈ tsupport (lowGraphCutoff i)) (hj : ξ ∈ tsupport (lowGraphCutoff j)) :
    j ≤ i + 2 := by
  have h := (tsupport_lowGraphCutoff_subset i hi).1.trans (tsupport_lowGraphCutoff_subset j hj).2
  have hinv : ((2 : ℝ) ^ (i + 2))⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ := by
    calc
      _ = ((2 : ℝ) ^ (i + 1))⁻¹ / 2 := by
        rw [show i + 2 = (i + 1) + 1 by omega, pow_succ, mul_inv_rev]
        ring
      _ ≤ (2 * ((2 : ℝ) ^ j)⁻¹) / 2 := div_le_div_of_nonneg_right h (by norm_num)
      _ = _ := by ring
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    ((inv_le_inv₀ (by positivity) (by positivity)).mp hinv)

/-- At most three closed high graph carriers meet a fixed frequency
(`app:ch_regular:eq:chain-tail`). -/
theorem card_highGraphCutoff_overlap_le (s : Finset ℕ) (ξ : Euclidean n)
    (h : ∀ j ∈ s, ξ ∈ tsupport (highGraphCutoff j)) : s.card ≤ 3 :=
  card_le_of_index_width s 2 (fun i hi j hj => highGraphCutoff_overlap_index_le (h i hi) (h j hj))

/-- At most three closed low graph carriers meet a fixed frequency
(`app:ch_regular:eq:chain-tail`). -/
theorem card_lowGraphCutoff_overlap_le (s : Finset ℕ) (ξ : Euclidean n)
    (h : ∀ j ∈ s, ξ ∈ tsupport (lowGraphCutoff j)) : s.card ≤ 3 :=
  card_le_of_index_width s 2 (fun i hi j hj => lowGraphCutoff_overlap_index_le (h i hi) (h j hj))

/-- The independent output family has uniformly bounded overlap, including
its low ball (`app:ch_regular:eq:chain-tail`). -/
theorem card_outputCutoff_overlap_le (s : Finset ℕ) (ξ : Euclidean n)
    (h : ∀ k ∈ s, ξ ∈ tsupport (outputCutoff k)) : s.card ≤ 4 := by
  have he : (s.erase 0).card ≤ 3 := by
    apply card_le_of_index_width (s.erase 0) 2
    intro i hi j hj
    obtain ⟨hi0, his⟩ := Finset.mem_erase.mp hi
    obtain ⟨hj0, hjs⟩ := Finset.mem_erase.mp hj
    cases i with
    | zero => exact (hi0 rfl).elim
    | succ i =>
      cases j with
      | zero => exact (hj0 rfl).elim
      | succ j =>
        have hd := highGraphCutoff_overlap_index_le (h (i + 1) his) (h (j + 1) hjs)
        omega
  by_cases h0 : 0 ∈ s
  · have := Finset.card_erase_add_one h0
    omega
  · simpa only [Finset.erase_eq_of_notMem h0] using he.trans (by norm_num : 3 ≤ 4)

/-- The number of high graph carriers meeting an annulus depends only on
the endpoint ratio, not its physical radius. This is the comparable-pair
count in `app:ch_regular:eq:chain-tail`. -/
theorem card_highGraphCutoff_meeting_annulus_le (s : Finset ℕ) {a b : ℝ} (d : ℕ)
    (hab : b ≤ (2 : ℝ) ^ d * a)
    (h : ∀ j ∈ s, ∃ ξ : Euclidean n, ξ ∈ tsupport (highGraphCutoff j) ∧
      a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) : s.card ≤ d + 3 := by
  apply card_le_of_index_width s (d + 2)
  intro i hi j hj
  obtain ⟨ξ, hξ, ha, _⟩ := h i hi
  obtain ⟨η, hη, _, hb⟩ := h j hj
  have hp : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (i + (d + 2)) := by
    calc
      _ ≤ ‖η‖ := (tsupport_highGraphCutoff_subset j hη).1
      _ ≤ b := hb
      _ ≤ (2 : ℝ) ^ d * a := hab
      _ ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ (i + 2) :=
        mul_le_mul_of_nonneg_left (ha.trans (tsupport_highGraphCutoff_subset i hξ).2) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hp

/-- The same scale-relative count applies to the contracting graph annuli,
with no lower-frequency truncation (`app:ch_regular:eq:chain-tail`). -/
theorem card_lowGraphCutoff_meeting_annulus_le (s : Finset ℕ) {a b : ℝ} (d : ℕ)
    (hab : b ≤ (2 : ℝ) ^ d * a)
    (h : ∀ j ∈ s, ∃ ξ : Euclidean n, ξ ∈ tsupport (lowGraphCutoff j) ∧
      a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) : s.card ≤ d + 3 := by
  apply card_le_of_index_width s (d + 2)
  intro i hi j hj
  obtain ⟨ξ, hξ, _, hb⟩ := h i hi
  obtain ⟨η, hη, ha, _⟩ := h j hj
  have hp : ((2 : ℝ) ^ (i + 1))⁻¹ ≤ (2 : ℝ) ^ (d + 1) * ((2 : ℝ) ^ j)⁻¹ := by
    calc
      _ ≤ ‖ξ‖ := (tsupport_lowGraphCutoff_subset i hξ).1
      _ ≤ b := hb
      _ ≤ (2 : ℝ) ^ d * a := hab
      _ ≤ (2 : ℝ) ^ d * (2 * ((2 : ℝ) ^ j)⁻¹) :=
        mul_le_mul_of_nonneg_left (ha.trans (tsupport_lowGraphCutoff_subset j hη).2) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hp' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ (2 : ℝ) ^ (i + 1) * (2 : ℝ) ^ j)
  have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (i + (d + 2)) := by
    convert hp' using 1
    · field_simp
    · rw [show i + (d + 2) = (d + 1) + (i + 1) by omega, pow_add]
      field_simp
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow

/-- The independent output count costs at most one additional low ball
relative to the graph annulus count (`app:ch_regular:eq:chain-tail`). -/
theorem card_outputCutoff_meeting_annulus_le (s : Finset ℕ) {a b : ℝ} (d : ℕ)
    (hab : b ≤ (2 : ℝ) ^ d * a)
    (h : ∀ k ∈ s, ∃ ξ : Euclidean n, ξ ∈ tsupport (outputCutoff k) ∧
      a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) : s.card ≤ d + 4 := by
  have he : (s.erase 0).card ≤ d + 3 := by
    let t := (s.erase 0).image Nat.pred
    have ht := card_highGraphCutoff_meeting_annulus_le (n := n) t d hab (by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hk0, hks⟩ := Finset.mem_erase.mp hk
      cases k with
      | zero => exact (hk0 rfl).elim
      | succ k => exact h (k + 1) hks)
    have hc : t.card = (s.erase 0).card := Finset.card_image_of_injOn (show
        Set.InjOn Nat.pred (↑(s.erase 0) : Set ℕ) from by
      intro i hi j hj hij
      have hi0 := (Finset.mem_erase.mp hi).1
      have hj0 := (Finset.mem_erase.mp hj).1
      simp only [Nat.pred_eq_sub_one] at hij
      omega)
    rwa [hc] at ht
  by_cases h0 : 0 ∈ s
  · have := Finset.card_erase_add_one h0
    omega
  · simpa only [Finset.erase_eq_of_notMem h0] using he.trans (by omega : d + 3 ≤ d + 4)

end JanetCartan.FiniteChain.Graph.PhysicalShells
