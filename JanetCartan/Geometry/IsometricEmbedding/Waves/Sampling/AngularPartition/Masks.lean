module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportBuffers

/-!
# Square masks for a finite canonical cone cover

The direction bumps already used by the canonical charts have a plateau at
one quarter of `angularWidth` and support at one half of that width. Normalize
their squares with an additional complementary product. The denominator is
positive everywhere; the complementary product vanishes on the supplied cover.

Consumer: the angular inputs of
`Sampling.MeasuredAmplitude.exists_finite_retained_sampling_realization` and
the partition premise of `Sampling.sum_angularLocalizedKernel_prefix_normal`
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:sampling-prefix-normal`).
-/

@[expose] public noncomputable section
open Set Metric NormedSpace
open scoped ContDiff

namespace JanetCartan.Sampling
open ContinuumRow.CanonicalConic

variable {n : ℕ} {I : Type*} [Fintype I]
local notation "E" => Euclidean (n - 1)

private theorem sum_sq_add_prod_sq_pos (b : I → ℝ) :
    0 < (∑ i, b i ^ 2) + (∏ i, (1 - b i)) ^ 2 := by
  classical
  by_cases hb : ∃ i, b i ≠ 0
  · obtain ⟨i, hi⟩ := hb
    have hs : b i ^ 2 ≤ ∑ j, b j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (b j)) (Finset.mem_univ i)
    have hp := sq_pos_of_ne_zero hi
    linarith [sq_nonneg (∏ j, (1 - b j))]
  · have hz : ∀ i, b i = 0 := by simpa using hb
    simp [hz]

variable (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i)

/-- The positive denominator of the canonical angular square masks, evaluated
before radial normalization (`app:ch_waves:thm:sampling`). -/
def canonicalAngularSquareDenominator (θ : E) : ℝ :=
  Real.sqrt ((∑ i, directionMask (normalize (ηb i))
    (angularWidth_spec (hηb i) (hr i)).1 θ ^ 2) +
    (∏ i, (1 - directionMask (normalize (ηb i))
      (angularWidth_spec (hηb i) (hr i)).1 θ)) ^ 2)

/-- The complementary product prevents a zero denominator even outside the
selected support (`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareDenominator_pos (θ : E) :
    0 < canonicalAngularSquareDenominator ηb r hηb hr θ :=
  Real.sqrt_pos.mpr (sum_sq_add_prod_sq_pos _)

/-- The denominator is globally smooth in the ambient direction variable
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareDenominator_contDiff :
    ContDiff ℝ ∞ (canonicalAngularSquareDenominator ηb r hηb hr) := by
  apply ContDiff.sqrt
  · exact (ContDiff.sum (fun i _ ↦ (directionMask (normalize (ηb i))
      (angularWidth_spec (hηb i) (hr i)).1).contDiff.pow 2)).add
      ((contDiff_prod (fun i _ ↦ contDiff_const.sub
        (directionMask (normalize (ηb i))
          (angularWidth_spec (hηb i) (hr i)).1).contDiff)).pow 2)
  · intro θ
    exact (sum_sq_add_prod_sq_pos _).ne'

/-- The actual homogeneous real mask subordinate to the `i`th canonical
cone. No part of the supplied angular cover is discarded
(`app:ch_waves:thm:sampling`). -/
def canonicalAngularSquareMask (i : I) (η : E) : ℝ :=
  directionMask (normalize (ηb i)) (angularWidth_spec (hηb i) (hr i)).1
    (normalize η) / canonicalAngularSquareDenominator ηb r hηb hr (normalize η)

/-- Every constructed mask vanishes at the origin
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareMask_zero (i : I) :
    canonicalAngularSquareMask ηb r hηb hr i 0 = 0 := by
  have hz : directionMask (normalize (ηb i))
      (angularWidth_spec (hηb i) (hr i)).1 (0 : E) = 0 := by
    apply ContDiffBump.zero_of_le_dist
    change angularWidth (ηb i) (r i) / 2 ≤ dist 0 (normalize (ηb i))
    rw [dist_zero_left, norm_normalize (hηb i)]
    linarith [(angularWidth_spec (hηb i) (hr i)).2.1]
  simp [canonicalAngularSquareMask, hz]

/-- Positive dilation leaves every constructed angular mask unchanged
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareMask_homogeneous (i : I) (t : ℝ) (ht : 0 < t) (η : E) :
    canonicalAngularSquareMask ηb r hηb hr i (t • η) =
      canonicalAngularSquareMask ηb r hηb hr i η := by
  simp only [canonicalAngularSquareMask, normalize_smul_of_pos ht]

/-- Smoothness away from zero of the constructed square masks
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareMask_contDiffAt (i : I) {η : E} (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (canonicalAngularSquareMask ηb r hηb hr i) η := by
  have hn : ContDiffAt ℝ ∞ (normalize : E → E) η :=
    ((contDiffAt_id.norm ℝ hη).inv (norm_ne_zero_iff.mpr hη)).smul contDiffAt_id
  exact (((directionMask (normalize (ηb i))
    (angularWidth_spec (hηb i) (hr i)).1).contDiff.div
    (canonicalAngularSquareDenominator_contDiff ηb r hηb hr)
    (fun θ ↦ (canonicalAngularSquareDenominator_pos ηb r hηb hr θ).ne')).contDiffAt.comp η hn)

/-- The continuity input of `angularLocalizedKernel` follows from the
constructed smooth masks (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem canonicalAngularSquareMask_continuousOn (i : I) :
    ContinuousOn (canonicalAngularSquareMask ηb r hηb hr i) ({0}ᶜ : Set E) :=
  fun _ hη ↦ (canonicalAngularSquareMask_contDiffAt ηb r hηb hr i hη).continuousAt.continuousWithinAt

/-- The constructed square masks are nonnegative contractions
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareMask_mem_Icc (i : I) (η : E) :
    canonicalAngularSquareMask ηb r hηb hr i η ∈ Icc (0 : ℝ) 1 := by
  classical
  let b : I → ℝ := fun j ↦ directionMask (normalize (ηb j))
    (angularWidth_spec (hηb j) (hr j)).1 (normalize η)
  have hb : 0 ≤ b i := ContDiffBump.nonneg _
  have hd := canonicalAngularSquareDenominator_pos ηb r hηb hr (normalize η)
  have hs : b i ^ 2 ≤ ∑ j, b j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (b j)) (Finset.mem_univ i)
  have he : canonicalAngularSquareDenominator ηb r hηb hr (normalize η) ^ 2 =
      (∑ j, b j ^ 2) + (∏ j, (1 - b j)) ^ 2 :=
    Real.sq_sqrt (sum_sq_add_prod_sq_pos b).le
  change b i / canonicalAngularSquareDenominator ηb r hηb hr (normalize η) ∈ Icc _ _
  refine ⟨div_nonneg hb hd.le, (div_le_one hd).mpr ?_⟩
  nlinarith [sq_nonneg (∏ j, (1 - b j))]

/-- The literal absolute-value bound required by `angularLocalizedKernel`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem canonicalAngularSquareMask_abs_le (i : I) (η : E) :
    |canonicalAngularSquareMask ηb r hηb hr i η| ≤ 1 := by
  rw [abs_of_nonneg (canonicalAngularSquareMask_mem_Icc ηb r hηb hr i η).1]
  exact (canonicalAngularSquareMask_mem_Icc ηb r hηb hr i η).2

/-- Nonzero masks belong to the actual closed canonical direction sets,
with no symmetry assumption (`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareMask_support (i : I) {η : E}
    (h : canonicalAngularSquareMask ηb r hηb hr i η ≠ 0) :
    η ≠ 0 ∧ normalize η ∈ closedDirections (ηb i) (r i) := by
  have hη : η ≠ 0 := by
    rintro rfl
    exact h (canonicalAngularSquareMask_zero ηb r hηb hr i)
  have hb : directionMask (normalize (ηb i))
      (angularWidth_spec (hηb i) (hr i)).1 (normalize η) ≠ 0 :=
    (div_ne_zero_iff.mp h).1
  exact ⟨hη, mem_sphere_zero_iff_norm.mpr (norm_normalize hη),
    ball_subset_closedBall ((directionMask (normalize (ηb i))
      (angularWidth_spec (hηb i) (hr i)).1).support_eq ▸ hb)⟩

/-- A bump is one at every direction in its quarter-width covering ball
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquare_complement_eq_zero {θ : E}
    (hcover : ∃ i, θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4)) :
    (∏ i, (1 - directionMask (normalize (ηb i))
      (angularWidth_spec (hηb i) (hr i)).1 θ)) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hcover
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [(directionMask (normalize (ηb i))
    (angularWidth_spec (hηb i) (hr i)).1).one_of_mem_closedBall
      (ball_subset_closedBall hi), sub_self]

/-- The sum of the mask squares is exactly one on the supplied angular
cover (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem canonicalAngularSquareMask_sum_sq {S : Set E}
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    {η : E} (hη : normalize η ∈ S) :
    ∑ i, canonicalAngularSquareMask ηb r hηb hr i η ^ 2 = 1 := by
  have hc := canonicalAngularSquare_complement_eq_zero ηb r hηb hr (hcover _ hη)
  have hd := canonicalAngularSquareDenominator_pos ηb r hηb hr (normalize η)
  have he : canonicalAngularSquareDenominator ηb r hηb hr (normalize η) ^ 2 =
      ∑ i, directionMask (normalize (ηb i))
        (angularWidth_spec (hηb i) (hr i)).1 (normalize η) ^ 2 := by
    rw [canonicalAngularSquareDenominator, hc, zero_pow (by decide : 2 ≠ 0), add_zero]
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))
  simp only [canonicalAngularSquareMask, div_pow, ← Finset.sum_div]
  rw [← he, div_self (pow_ne_zero 2 hd.ne')]

include hηb hr in
/-- A supplied finite cover of the compact selected sphere support produces
all square-mask properties required by the retained sampling construction.
The hypotheses are geometric cover data, not a partition assumption
(`app:ch_waves:thm:sampling`). -/
theorem exists_canonical_angular_square_partition (_hn : 2 ≤ n) (S : Set E)
    (_hS : IsCompact S) (_hSphere : S ⊆ sphere 0 1)
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4)) :
    ∃ χ : I → E → ℝ,
      (∀ i, χ i 0 = 0) ∧
      (∀ i η, η ≠ 0 → ContDiffAt ℝ ∞ (χ i) η) ∧
      (∀ i (t : ℝ), 0 < t → ∀ η, χ i (t • η) = χ i η) ∧
      (∀ i η, χ i η ∈ Icc (0 : ℝ) 1) ∧
      (∀ i η, χ i η ≠ 0 → η ≠ 0 ∧ normalize η ∈ closedDirections (ηb i) (r i)) ∧
      (∀ η : E, normalize η ∈ S → ∑ i, χ i η ^ 2 = 1) :=
  ⟨canonicalAngularSquareMask ηb r hηb hr,
    canonicalAngularSquareMask_zero ηb r hηb hr,
    fun i _ hη ↦ canonicalAngularSquareMask_contDiffAt ηb r hηb hr i hη,
    canonicalAngularSquareMask_homogeneous ηb r hηb hr,
    canonicalAngularSquareMask_mem_Icc ηb r hηb hr,
    fun i _ h ↦ canonicalAngularSquareMask_support ηb r hηb hr i h,
    fun _ hη ↦ canonicalAngularSquareMask_sum_sq ηb r hηb hr hcover hη⟩

end JanetCartan.Sampling
