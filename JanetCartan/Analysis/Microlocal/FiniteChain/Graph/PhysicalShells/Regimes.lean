module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers

/-!
# Exhaustive regimes for the actual cutoff pairs

The comparable remainder is finite, with cardinality bounded independently
of the input scale. Its complement satisfies the literal separated-range
predicate consumed by the physical noncomparable estimate. No frequencies
are discarded (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open Noncomparable KernelEstimates.NoncomparableGeometry

/-- The exact remainder after the four physical separated regimes, with
the input shoulder endpoints `a*ρ` and `b*ρ`
(`app:ch_regular:eq:chain-tail`). -/
def IsComparablePair (c C a b ρ : ℝ) (low : Bool) (j k : ℕ) : Prop :=
  ¬ SeparatedRanges c C (a * ρ) (b * ρ)
    (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k)

/-- Every actual pair belongs to the comparable remainder or to a separated
regime, including the output ball and all contracting graph annuli
(`app:ch_regular:eq:chain-tail`). -/
theorem comparable_or_separated (c C a b ρ : ℝ) (low : Bool) (j k : ℕ) :
    IsComparablePair c C a b ρ low j k ∨
      SeparatedRanges c C (a * ρ) (b * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) :=
  (Classical.em _).symm

/-- Both bookkeeping radii in a comparable pair lie in a fixed multiple of
the input annulus. The `max 1` upper bound accounts for output index zero;
no positive output lower endpoint is asserted there
(`app:ch_regular:eq:chain-tail`). -/
theorem comparablePair_radius_bounds {c C a b ρ : ℝ} (hρ : 1 ≤ ρ)
    {low : Bool} {j k : ℕ} (h : IsComparablePair c C a b ρ low j k) :
    (a / (8 * annulusFactor c C)) * ρ ≤ branchRadius low j ∧
      branchRadius low j ≤ max 1 (4 * annulusFactor c C * b) * ρ ∧
      (a / (8 * annulusFactor c C)) * ρ ≤ (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ k ≤ max 1 (4 * annulusFactor c C * b) * ρ := by
  let F := annulusFactor c C
  have hF : 0 < F := lt_of_lt_of_le (by norm_num) (two_le_annulusFactor c C)
  obtain ⟨hg₁, hg₂, ho₁, ho₂⟩ := (not_separatedRanges_iff ..).mp h
  have hg := graphLower_bounds low j
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hupper : (4 * F * b) * ρ ≤ max 1 (4 * F * b) * ρ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hρ0
  have hlow : a * ρ ≤ 8 * F * branchRadius low j := by
    dsimp [graphUpper] at hg₁
    have hh := mul_le_mul_of_nonneg_left hg.2 (show 0 ≤ 8 * F by positivity)
    nlinarith
  have hhigh : branchRadius low j ≤ (4 * F * b) * ρ := by
    nlinarith
  have hout : a * ρ ≤ 8 * F * (2 : ℝ) ^ k := by
    dsimp [outputUpper] at ho₁
    have hh : 0 ≤ F * (2 : ℝ) ^ k := by positivity
    nlinarith
  refine ⟨?_, hhigh.trans hupper, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (show 0 < 8 * F by positivity)).mpr (by nlinarith)
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (show 0 < 8 * F by positivity)).mpr (by nlinarith)
  · by_cases hk : k = 0
    · subst k
      simp only [pow_zero]
      have hh := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (4 * F * b)) hρ0
      exact hρ.trans (by simpa only [one_mul] using hh)
    · simp only [outputLower, hk, ↓reduceIte] at ho₂
      exact (show (2 : ℝ) ^ k ≤ (4 * F * b) * ρ by nlinarith).trans hupper

/-- On the comparable remainder the full graph carrier lies in one fixed
normalized annulus, bounded away from zero. The low branch is included when
it is comparable, and is handled by the separated estimate otherwise
(`app:ch_regular:eq:chain-tail`). -/
theorem comparableGraphCarrier_subset {n : ℕ} {c C a b ρ : ℝ}
    (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (h : IsComparablePair c C a b ρ low j k) :
    normalizedGraphCarrier (n := n) ρ low j ⊆
      frequencyAnnulus (a / (16 * annulusFactor c C))
        (4 * max 1 (4 * annulusFactor c C * b)) := by
  intro ξ hξ
  have hρ0 := zero_lt_one.trans_le hρ
  have hb := comparablePair_radius_bounds hρ h
  have hξ' := (mem_normalizedGraphCarrier_iff hρ0.ne' low j ξ).mp hξ
  rw [norm_smul, Real.norm_of_nonneg hρ0.le] at hξ'
  have hl := (graphLower_bounds low j).1
  have hu := (graphLower_bounds low j).2
  change _ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ _
  constructor
  · apply (mul_le_mul_iff_right₀ hρ0).mp
    have he : a / (16 * annulusFactor c C) = a / (8 * annulusFactor c C) / 2 := by ring
    rw [he]
    nlinarith [hb.1]
  · apply (mul_le_mul_iff_right₀ hρ0).mp
    dsimp [graphUpper] at hξ'
    nlinarith [hb.2.1]

/-- All comparable output carriers lie in a single normalized ball. This
also handles the independent output index zero
(`app:ch_regular:eq:chain-tail`). -/
theorem comparableOutputCarrier_subset {n : ℕ} {c C a b ρ : ℝ}
    (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (h : IsComparablePair c C a b ρ low j k) :
    normalizedOutputCarrier (n := n) ρ k ⊆
      Metric.closedBall 0 (2 * max 1 (4 * annulusFactor c C * b)) := by
  intro ζ hζ
  have hρ0 := zero_lt_one.trans_le hρ
  have hb := (comparablePair_radius_bounds hρ h).2.2.2
  have hζ' := ((mem_normalizedOutputCarrier_iff hρ0.ne' k ζ).mp hζ).2
  rw [norm_smul, Real.norm_of_nonneg hρ0.le] at hζ'
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (mul_le_mul_iff_right₀ hρ0).mp
  dsimp [outputUpper] at hζ'
  nlinarith

private theorem card_le_of_width (s : Finset ℕ) (d : ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, j ≤ i + d) : s.card ≤ d + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hsub : s ⊆ Finset.Icc (s.min' hs) (s.min' hs + d) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨s.min'_le j hj, h _ (s.min'_mem hs) j hj⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega

/-- The number of actual graph radii in any multiplicative window is
uniform in its location, for either branch (`app:ch_regular:eq:chain-tail`). -/
theorem card_branchRadius_interval_le (low : Bool) (s : Finset ℕ)
    {a b : ℝ} (d : ℕ) (hab : b ≤ (2 : ℝ) ^ d * a)
    (h : ∀ j ∈ s, a ≤ branchRadius low j ∧ branchRadius low j ≤ b) :
    s.card ≤ d + 1 := by
  apply card_le_of_width s d
  intro i hi j hj
  have h₁ := (h i hi).2.trans (hab.trans
    (mul_le_mul_of_nonneg_left (h j hj).1 (by positivity)))
  have h₂ := (h j hj).2.trans (hab.trans
    (mul_le_mul_of_nonneg_left (h i hi).1 (by positivity)))
  apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
  cases low
  · simpa only [branchRadius, Bool.false_eq_true, ↓reduceIte, pow_add, mul_comm] using h₂
  · simp only [branchRadius, ↓reduceIte] at h₁
    have hh := mul_le_mul_of_nonneg_right h₁
      (show 0 ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j by positivity)
    have hi0 : (2 : ℝ) ^ i ≠ 0 := by positivity
    have hj0 : (2 : ℝ) ^ j ≠ 0 := by positivity
    have he₁ : ((2 : ℝ) ^ i)⁻¹ * ((2 : ℝ) ^ i * (2 : ℝ) ^ j) = (2 : ℝ) ^ j := by
      field_simp
    have he₂ : (2 : ℝ) ^ d * ((2 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ i * (2 : ℝ) ^ j) =
        (2 : ℝ) ^ (i + d) := by
      rw [pow_add]
      field_simp
    rwa [he₁, he₂] at hh

/-- A finite collection of comparable pairs has a scale-independent bound
on its cardinality. Both shell indices remain independent
(`app:ch_regular:eq:chain-tail`). -/
theorem card_comparablePairs_le {c C a b ρ : ℝ} (hρ : 1 ≤ ρ)
    (low : Bool) (d : ℕ)
    (hd : max 1 (4 * annulusFactor c C * b) ≤
      (2 : ℝ) ^ d * (a / (8 * annulusFactor c C)))
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, IsComparablePair c C a b ρ low p.1 p.2) :
    s.card ≤ (d + 1) ^ 2 := by
  have hd' : max 1 (4 * annulusFactor c C * b) * ρ ≤
      (2 : ℝ) ^ d * ((a / (8 * annulusFactor c C)) * ρ) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (zero_le_one.trans hρ)
  have hg : (s.image Prod.fst).card ≤ d + 1 :=
    card_branchRadius_interval_le low _ d hd' (by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      have hb := comparablePair_radius_bounds hρ (hs p hp)
      exact ⟨hb.1, hb.2.1⟩)
  have ho : (s.image Prod.snd).card ≤ d + 1 :=
    card_branchRadius_interval_le false _ d hd' (by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      have hb := comparablePair_radius_bounds hρ (hs p hp)
      exact ⟨hb.2.2.1, hb.2.2.2⟩)
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  calc
    s.card ≤ ((s.image Prod.fst) ×ˢ (s.image Prod.snd)).card := Finset.card_le_card hsub
    _ = (s.image Prod.fst).card * (s.image Prod.snd).card := Finset.card_product ..
    _ ≤ (d + 1) * (d + 1) := Nat.mul_le_mul hg ho
    _ = _ := (sq _).symm

/-- The actual comparable remainder is finite and has uniformly bounded
cardinality before the scale is chosen. Its complement is precisely the
input to the noncomparable estimate (`app:ch_regular:eq:chain-tail`). -/
theorem exists_finite_comparablePairs (c C b : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ low : Bool,
      ∃ s : Finset (ℕ × ℕ), (s.card ≤ N) ∧
        ∀ j k, (j, k) ∈ s ↔ IsComparablePair c C a b ρ low j k := by
  classical
  have hF : 0 < annulusFactor c C := lt_of_lt_of_le (by norm_num) (two_le_annulusFactor c C)
  have hlow : 0 < a / (8 * annulusFactor c C) := by positivity
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt
    (max 1 (4 * annulusFactor c C * b) / (a / (8 * annulusFactor c C)))
    (by norm_num : (1 : ℝ) < 2)
  have hd' := ((div_lt_iff₀ hlow).mp hd).le
  refine ⟨(d + 1) ^ 2, ?_⟩
  intro ρ hρ low
  let E : Set (ℕ × ℕ) := {p | IsComparablePair c C a b ρ low p.1 p.2}
  have hfin : E.Finite := by
    by_contra hf
    obtain ⟨s, hs, hc⟩ := Set.Infinite.exists_subset_card_eq hf ((d + 1) ^ 2 + 1)
    have hb := card_comparablePairs_le hρ low d hd' s (fun p hp => hs hp)
    omega
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · exact card_comparablePairs_le hρ low d hd' _ (fun p hp => hfin.mem_toFinset.mp hp)
  · intro j k
    exact hfin.mem_toFinset

end JanetCartan.FiniteChain.Graph.PhysicalShells
