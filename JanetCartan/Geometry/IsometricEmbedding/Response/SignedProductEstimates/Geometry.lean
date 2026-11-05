module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Sampling

/-!
# True beats of the sampled signed products

The geometric inputs for Step 1 of `app:ch_pairs:prop:pairs-lag-sum` are
provided for every `SignedPairs.Pair` by
`ActualCarriers.ConstructedSignedGeometry.exists_constructed_signed_geometry`.
Here the sampled products are identified with precisely those pairs, retaining
their true beats. In particular separation is needed only within one full
group; doubled plus carriers are represented with beat one.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedProductEstimates

open SignedPairs

variable {G J Z E : Type*} [NormedAddCommGroup Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {S : G → Set Z}

/-- The protected pair representing a sampled plus source has EXACT beat one,
also for equal indices (`app:rem:exhaustive-signed-pairs`). This supplements
`SignedPairs.sample_plus_represented` for the true-frequency substitution in
`cutoff_plusSource_eq_real_modulatedSource`. -/
theorem sample_plus_represented_with_beat
    (group : J → G) (z : J → Z) (hz : ∀ j, z j ∈ S (group j)) (i j : J) :
    ∃ q : Pair G Z S, q.beat = 1 ∧ ∀ f : G → Z → E,
      q.vector f = f (group i) (z i) + f (group j) (z j) := by
  by_cases h : group i = group j
  · have hzj : z j ∈ S (group i) := by simpa only [h] using hz j
    refine ⟨.sum (group i) ⟨z i, hz i⟩ ⟨z j, hzj⟩, rfl, ?_⟩
    intro f
    simp only [Pair.vector, h]
  · refine ⟨.cross (group i) (group j) h ⟨z i, hz i⟩ ⟨z j, hz j⟩
      1 1 (by norm_num) (by norm_num), rfl, ?_⟩
    intro f
    simp only [Pair.vector, one_smul]

/-- Within-group separation proves nonvanishing of every distinct minus
beat. Its exact value is the parameter distance in one group and one across
groups (`app:ch_seed:eq:seed-actual-chord`; `app:rem:exhaustive-signed-pairs`).
No injectivity of unrelated existential choices is assumed. -/
theorem sample_minus_represented_with_beat
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (group : J → G) (z : J → Z) (hz : ∀ j, z j ∈ S (group j))
    (hsep : ∀ i j, i ≠ j → group i = group j → h ≤ ‖z i - z j‖)
    {i j : J} (hij : i ≠ j) :
    ∃ q : Pair G Z S, h ≤ q.beat ∧
      (group i = group j → q.beat = ‖z i - z j‖) ∧
      (group i ≠ group j → q.beat = 1) ∧
      ∀ f : G → Z → E, q.vector f = f (group i) (z i) - f (group j) (z j) := by
  by_cases hg : group i = group j
  · have hzj : z j ∈ S (group i) := by simpa only [hg] using hz j
    have hnz : z i ≠ z j := by
      intro he
      have := hsep i j hij hg
      rw [he, sub_self, norm_zero] at this
      exact (not_le_of_gt hh) this
    have hsub : (⟨z i, hz i⟩ : S (group i)) ≠ ⟨z j, hzj⟩ :=
      fun he ↦ hnz (congrArg Subtype.val he)
    refine ⟨.difference (group i) ⟨z i, hz i⟩ ⟨z j, hzj⟩ hsub,
      hsep i j hij hg, fun _ ↦ rfl, fun hn ↦ (hn hg).elim, ?_⟩
    intro f
    simp only [Pair.vector, hg]
  · refine ⟨.cross (group i) (group j) hg ⟨z i, hz i⟩ ⟨z j, hz j⟩
      1 (-1) (by norm_num) (by norm_num), hhone,
      fun he ↦ (hg he).elim, fun _ ↦ rfl, ?_⟩
    intro f
    simp only [Pair.vector, one_smul, neg_smul, sub_eq_add_neg]

/-- Apply the published whole-family geometric bounds to the actual sampled
plus covectors. The original constants precede the samples and the frequency;
the plus diagonal retains its lower bound (`app:ch_pairs:setup:pairs-lag`). -/
theorem sampled_plus_frequency_bounds
    {a A : ℝ} (f : G → Z → E)
    (hfamily : ∀ q : Pair G Z S,
      a * q.beat ≤ ‖q.vector f‖ ∧ ‖q.vector f‖ ≤ A * q.beat)
    (group : J → G) (z : J → Z) (hz : ∀ j, z j ∈ S (group j))
    {lam : ℝ} (hlam : 0 ≤ lam) (i j : J) :
    a * lam ≤ ‖lam • (f (group i) (z i) + f (group j) (z j))‖ ∧
      ‖lam • (f (group i) (z i) + f (group j) (z j))‖ ≤ A * lam := by
  obtain ⟨q, hbeat, hq⟩ := sample_plus_represented_with_beat (E := E) group z hz i j
  have hb := frequency_bounds hlam (hfamily q).1 (hfamily q).2
  simpa only [hbeat, mul_one, hq f] using hb

/-- The original `lam h` lower frequency for every distinct sampled minus
covector follows from the whole signed geometry and within-group separation
(`app:ch_pairs:eq:pairs-lag-one-error`). The upper frequency uses the fixed
parameter diameter, hence stays at the carrier scale `lam`, not `lam / h`. -/
theorem sampled_minus_frequency_bounds
    {a A d : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hd : 1 ≤ d)
    (f : G → Z → E)
    (hfamily : ∀ q : Pair G Z S,
      a * q.beat ≤ ‖q.vector f‖ ∧ ‖q.vector f‖ ≤ A * q.beat)
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (group : J → G) (z : J → Z) (hz : ∀ j, z j ∈ S (group j))
    (hsep : ∀ i j, i ≠ j → group i = group j → h ≤ ‖z i - z j‖)
    (hdiam : ∀ i j, group i = group j → ‖z i - z j‖ ≤ d)
    {lam : ℝ} (hlam : 0 ≤ lam) {i j : J} (hij : i ≠ j) :
    a * (lam * h) ≤ ‖lam • (f (group i) (z i) - f (group j) (z j))‖ ∧
      ‖lam • (f (group i) (z i) - f (group j) (z j))‖ ≤ (A * d) * lam := by
  obtain ⟨q, hbeat, heq, hne, hq⟩ :=
    sample_minus_represented_with_beat (E := E) hh hhone group z hz hsep hij
  have hupper : q.beat ≤ d := by
    by_cases hg : group i = group j
    · rw [heq hg]
      exact hdiam i j hg
    · rw [hne hg]
      exact hd
  have hb := frequency_bounds hlam (hfamily q).1 (hfamily q).2
  rw [hq f] at hb
  constructor
  · exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbeat hlam) ha).trans hb.1
  · calc
      _ ≤ A * (lam * q.beat) := hb.2
      _ ≤ A * (lam * d) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hupper hlam) hA
      _ = (A * d) * lam := by ring

/-- The original closed angular buffer protects the actual sampled plus
covectors, including doubled carriers, uniformly over the whole current
family (`app:ch_pairs:setup:pairs-lag`). The input is the closure inclusion
published by `exists_constructed_signed_geometry`, for the SAME `g` and `S`. -/
theorem sampled_plus_mem_angularSet {n : ℕ} {X : Type*} {γ : ℝ}
    (g : X → G → Z → Euclidean n)
    (hclosed : closure (directionSet g S) ⊆ angularSet n γ)
    (group : J → G) (z : J → Z) (hz : ∀ j, z j ∈ S (group j))
    (x : X) (i j : J) :
    NormedSpace.normalize (g x (group i) (z i) + g x (group j) (z j)) ∈
      angularSet n γ := by
  obtain ⟨q, _, hq⟩ := sample_plus_represented_with_beat
    (E := Euclidean n) group z hz i j
  apply hclosed
  apply subset_closure
  exact ⟨x, q, congrArg NormedSpace.normalize (hq (g x)).symm⟩

/-- Distinct sampled minus covectors belong to the SAME original angular
buffer. Separation proves admissibility of the short chord, and no stronger
gap is assumed for the sampled family (`app:ch_seed:eq:seed-actual-chord`). -/
theorem sampled_minus_mem_angularSet {n : ℕ} {X : Type*} {γ : ℝ}
    (g : X → G → Z → Euclidean n)
    (hclosed : closure (directionSet g S) ⊆ angularSet n γ)
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (group : J → G) (z : J → Z) (hz : ∀ j, z j ∈ S (group j))
    (hsep : ∀ i j, i ≠ j → group i = group j → h ≤ ‖z i - z j‖)
    (x : X) {i j : J} (hij : i ≠ j) :
    NormedSpace.normalize (g x (group i) (z i) - g x (group j) (z j)) ∈
      angularSet n γ := by
  obtain ⟨q, _, _, _, hq⟩ := sample_minus_represented_with_beat
    (E := Euclidean n) hh hhone group z hz hsep hij
  apply hclosed
  apply subset_closure
  exact ⟨x, q, congrArg NormedSpace.normalize (hq (g x)).symm⟩

end JanetCartan.SignedProductEstimates
