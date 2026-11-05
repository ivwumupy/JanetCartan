module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Geometry
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PairEstimate

/-!
# Concrete carriers for the independent physical pairs

These constructions discharge the frequency-carrier and radius hypotheses of
`Noncomparable.exists_physicalPair_summable_majorant`. The input carrier is the
whole primitive annulus, including its shoulders. The graph carrier keeps its
shrinking radius in the low branch (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped Pointwise
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open Noncomparable
variable {n r : ℕ}

/-- Physical lower endpoint of an actual graph branch
(`app:ch_regular:eq:joint-kernel-phase`). -/
def graphLower (low : Bool) (j : ℕ) : ℝ :=
  if low then branchRadius low j / 2 else branchRadius low j

/-- The graph carriers have endpoint ratio four in both branches
(`app:ch_regular:eq:chain-tail`). -/
def graphUpper (low : Bool) (j : ℕ) : ℝ := 4 * graphLower low j

/-- The output ball has lower endpoint zero; subsequent outputs are annuli
(`app:ch_regular:eq:joint-kernel-phase`). -/
def outputLower (k : ℕ) : ℝ := if k = 0 then 0 else (2 : ℝ) ^ k / 2

/-- One upper-endpoint formula includes the output ball and all annuli
(`app:ch_regular:eq:joint-kernel-phase`). -/
def outputUpper (k : ℕ) : ℝ := 2 * (2 : ℝ) ^ k

/-- Primitive normalized annulus, with both boundary shoulders retained
(`app:ch_regular:eq:chain-tail`). -/
def frequencyAnnulus (a b : ℝ) : Set (Euclidean n) := {ξ | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b}

/-- The normalized graph carrier is the full physical annulus divided by
the input scale (`app:ch_regular:eq:joint-kernel-phase`). -/
def normalizedGraphCarrier (ρ : ℝ) (low : Bool) (j : ℕ) : Set (Euclidean n) :=
  ρ⁻¹ • frequencyAnnulus (graphLower low j) (graphUpper low j)

/-- The normalized output carrier includes the full output ball at index
zero (`app:ch_regular:eq:joint-kernel-phase`). -/
def normalizedOutputCarrier (ρ : ℝ) (k : ℕ) : Set (Euclidean n) :=
  ρ⁻¹ • frequencyAnnulus (outputLower k) (outputUpper k)

/-- Compactness does not require a positive inner radius, so this also
applies to the bounded output ball (`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_frequencyAnnulus (a b : ℝ) :
    IsCompact (frequencyAnnulus (n := n) a b) := by
  apply (isCompact_closedBall (0 : Euclidean n) b).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
  intro ξ hξ
  change a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b at hξ
  rw [mem_closedBall, dist_zero_right]
  exact hξ.2

/-- Compact graph carriers exist at every strictly positive physical scale,
including all low graph indices (`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_normalizedGraphCarrier (ρ : ℝ) (low : Bool) (j : ℕ) :
    IsCompact (normalizedGraphCarrier (n := n) ρ low j) :=
  (isCompact_frequencyAnnulus _ _).smul _

/-- Compactness for every independent output carrier
(`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_normalizedOutputCarrier (ρ : ℝ) (k : ℕ) :
    IsCompact (normalizedOutputCarrier (n := n) ρ k) :=
  (isCompact_frequencyAnnulus _ _).smul _

private theorem mem_inverse_dilate_iff {ρ : ℝ} (hρ : ρ ≠ 0)
    (a b : ℝ) (ξ : Euclidean n) :
    ξ ∈ ρ⁻¹ • frequencyAnnulus a b ↔ a ≤ ‖ρ • ξ‖ ∧ ‖ρ • ξ‖ ≤ b := by
  constructor
  · rintro ⟨η, hη, rfl⟩
    change a ≤ ‖η‖ ∧ ‖η‖ ≤ b at hη
    simpa only [smul_smul, mul_inv_cancel₀ hρ, one_smul] using hη
  · intro hξ
    exact ⟨ρ • ξ, hξ, by simp [smul_smul, hρ]⟩

/-- Membership exposes exactly the physical endpoints required by the gap
estimate (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem mem_normalizedGraphCarrier_iff {ρ : ℝ} (hρ : ρ ≠ 0)
    (low : Bool) (j : ℕ) (ξ : Euclidean n) :
    ξ ∈ normalizedGraphCarrier ρ low j ↔
      graphLower low j ≤ ‖ρ • ξ‖ ∧ ‖ρ • ξ‖ ≤ graphUpper low j :=
  mem_inverse_dilate_iff hρ _ _ _

/-- Membership in the output carrier keeps the zero lower endpoint at
index zero (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem mem_normalizedOutputCarrier_iff {ρ : ℝ} (hρ : ρ ≠ 0)
    (k : ℕ) (ζ : Euclidean n) :
    ζ ∈ normalizedOutputCarrier ρ k ↔
      outputLower k ≤ ‖ρ • ζ‖ ∧ ‖ρ • ζ‖ ≤ outputUpper k :=
  mem_inverse_dilate_iff hρ _ _ _

/-- The primitive branch cutoff is supported in its exact physical annulus
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tsupport_graphBranchCutoff_subset (low : Bool) (j : ℕ) :
    tsupport (graphBranchCutoff (n := n) low j) ⊆
      frequencyAnnulus (graphLower low j) (graphUpper low j) := by
  cases low
  · simpa [graphBranchCutoff, frequencyAnnulus, graphLower, graphUpper,
      branchRadius, pow_add, mul_comm, show (2 : ℝ) ^ 2 = 4 by norm_num]
      using tsupport_highGraphCutoff_subset (n := n) j
  · intro ξ hξ
    have h := tsupport_lowGraphCutoff_subset j hξ
    change _ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ _
    norm_num [graphLower, graphUpper, branchRadius, pow_succ, mul_inv_rev] at h ⊢
    constructor <;> nlinarith [h.1, h.2]

/-- The output support statement holds uniformly through index zero
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tsupport_outputCutoff_subset_annulus (k : ℕ) :
    tsupport (outputCutoff (n := n) k) ⊆
      frequencyAnnulus (outputLower k) (outputUpper k) := by
  cases k with
  | zero =>
    intro ξ hξ
    have h := tsupport_outputCutoff_zero_subset hξ
    exact ⟨by simp [outputLower],
      by simpa [outputUpper, mem_closedBall, dist_zero_right] using h⟩
  | succ k =>
    simpa [frequencyAnnulus, outputLower, outputUpper, pow_succ, mul_assoc,
      mul_comm, mul_left_comm] using tsupport_outputCutoff_succ_subset (n := n) k

private theorem tsupport_rescale_subset {χ : Euclidean n → ℝ} {a b ρ : ℝ}
    (hρ : ρ ≠ 0) (hχ : tsupport χ ⊆ frequencyAnnulus a b) :
    tsupport (fun ξ => χ (ρ • ξ)) ⊆ ρ⁻¹ • frequencyAnnulus a b := by
  apply closure_minimal _ ((isCompact_frequencyAnnulus a b).smul ρ⁻¹).isClosed
  intro ξ hξ
  exact (mem_inverse_dilate_iff hρ a b ξ).mpr (hχ (subset_tsupport χ hξ))

/-- The actual rescaled graph cutoff satisfies the support premise of the
noncomparable physical estimate (`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_rescaled_graphBranchCutoff_subset {ρ : ℝ} (hρ : ρ ≠ 0)
    (low : Bool) (j : ℕ) :
    tsupport (fun ξ : Euclidean n => graphBranchCutoff low j (ρ • ξ)) ⊆
      normalizedGraphCarrier ρ low j :=
  tsupport_rescale_subset hρ (tsupport_graphBranchCutoff_subset low j)

/-- The actual independently rescaled output satisfies its support premise
(`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_rescaled_outputCutoff_subset {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) :
    tsupport (fun ζ : Euclidean n => outputCutoff k (ρ • ζ)) ⊆
      normalizedOutputCarrier ρ k :=
  tsupport_rescale_subset hρ (tsupport_outputCutoff_subset_annulus k)

/-- Endpoint comparison with the true graph radius; the low radius is not
clipped to one (`app:ch_regular:eq:chain-tail`). -/
theorem graphLower_bounds (low : Bool) (j : ℕ) :
    branchRadius low j / 2 ≤ graphLower low j ∧
      graphLower low j ≤ branchRadius low j := by
  have h := (branchRadius_pos low j).le
  cases low <;> simp only [graphLower, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith

private theorem inverse_dilate_subset_ball {ρ s b a : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hb : b ≤ s * a) (l : ℝ) :
    ρ⁻¹ • frequencyAnnulus (n := n) l b ⊆ (s / ρ) • closedBall 0 a := by
  intro ξ hξ
  have hn := ((mem_inverse_dilate_iff hρ.ne' l b ξ).mp hξ).2
  refine ⟨(ρ / s) • ξ, ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [norm_smul, Real.norm_of_nonneg hρ.le] at hn
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hs).mpr
    nlinarith [hn.trans hb]
  · dsimp
    rw [smul_smul, div_mul_div_cancel₀ hρ.ne', div_self hs.ne', one_smul]

/-- The normalized graph carrier lies in the true-radius dilation of one
fixed ball. This discharges the shrinking-volume premise of
`exists_physicalPair_summable_majorant` (`app:ch_regular:eq:chain-tail`). -/
theorem normalizedGraphCarrier_subset_dilate {ρ : ℝ} (hρ : 0 < ρ)
    (low : Bool) (j : ℕ) :
    normalizedGraphCarrier (n := n) ρ low j ⊆
      (branchRadius low j / ρ) • closedBall 0 4 := by
  apply inverse_dilate_subset_ball hρ (branchRadius_pos low j)
  dsimp [graphUpper]
  nlinarith [(graphLower_bounds low j).2]

/-- The output ball and annuli fit the same fixed profile ball after
division by their individual radii (`app:ch_regular:eq:chain-tail`). -/
theorem normalizedOutputCarrier_subset_dilate {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    normalizedOutputCarrier (n := n) ρ k ⊆
      ((2 : ℝ) ^ k / ρ) • closedBall 0 2 := by
  apply inverse_dilate_subset_ball hρ (by positivity)
  simp only [outputUpper, mul_comm, le_refl]

/-- The output plane wave has a fixed carrier at the largest pair radius.
This supplies `Bwave` in the noncomparable estimate, including index zero
(`app:ch_regular:eq:chain-tail`). -/
theorem normalizedOutputCarrier_wave_mem {ρ : ℝ} (hρ : 1 ≤ ρ)
    (low : Bool) (j k : ℕ) {ζ : Euclidean n}
    (hζ : ζ ∈ normalizedOutputCarrier ρ k) :
    (ρ / pairRadius ρ low j k) • ζ ∈ closedBall 0 2 := by
  have hρ0 := zero_lt_one.trans_le hρ
  have hR := pairRadius_bounds hρ low j k
  have hR0 := zero_lt_one.trans_le hR.1
  have hζ' := ((mem_normalizedOutputCarrier_iff hρ0.ne' k ζ).mp hζ).2
  rw [norm_smul, Real.norm_of_nonneg hρ0.le] at hζ'
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hR0).mpr
  dsimp [outputUpper] at hζ'
  nlinarith [hR.2.2.2]

/-- A fixed positive fraction of the concrete pair radius is controlled by
the actual lower endpoints. Only the primitive input inner radius enters;
there is no positive lower bound imposed on the output ball or low graph
tail (`app:ch_regular:eq:chain-tail`). -/
theorem pairRadius_fraction_le_endpoints {ρ a : ℝ} (hρ : 1 ≤ ρ)
    (ha : 0 < a) (low : Bool) (j k : ℕ) :
    min a (1 / 2) * pairRadius ρ low j k ≤
      max (graphLower low j) (max (a * ρ) (outputLower k)) := by
  apply fractional_pairRadius_le_lowerEndpoints hρ
    (le_of_lt (lt_min ha (by norm_num))) (min_le_left _ _) (min_le_right _ _)
    low j k (graphLower_bounds low j).1
  by_cases hk : k = 0
  · exact Or.inl hk
  · exact Or.inr (by simp [outputLower, hk])

end JanetCartan.FiniteChain.Graph.PhysicalShells
