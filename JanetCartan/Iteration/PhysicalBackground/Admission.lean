module

public import JanetCartan.Iteration.PhysicalBackground.Density
public import JanetCartan.Analysis.ContDiff.DerivativeBounds.Composition

/-!
# Finite-low admission of the actual current uncut density

A single small RAW norm admits the same factor-two representative to the
original positive-density class. It is not a positive-density premise.
The raw norm has the precise task22 producer; task24 still owes its smallness
from the original source baseline and a fixed physical-history neighborhood.
The all-order estimates retain the derivative reserve, rather than asserting
uniform high-order smallness on every admissible physical history.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev UncutDensity PositiveBackground

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Choose one raw threshold BEFORE the current geometry and raw input.
The density is constructed, is globally positive after adding one, and enters
the exact finite-low label class consumed by task22's universal positive branch.
Higher orders retain the same uncut representative and quantitative estimates
(`app:ch_background:prop:bg-current`). -/
theorem exists_uncut_density_admission
    (d₀ : ι → CarrierData n N)
    (hρsmooth : ∀ i, ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d₀ i).angularCutoff p.1 p.2 : ℂ)))
    (hcρ : ∀ i, HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d₀ i).angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ∀ i, ContDiff ℝ ∞ (d₀ i).highCutoff)
    (hlow : ∀ i t, t ≤ 1 → (d₀ i).highCutoff t = 0)
    (hhi : ∀ i t, |(d₀ i).highCutoff t| ≤ 1)
    (hρ : ∀ i z η, |(d₀ i).angularCutoff z η| ≤ 1)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (hKin : ∀ i, IsCompact (Kin i)) (k : ℕ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧ ∃ δ > (0 : ℝ),
      ∀ d : ι → CarrierData n N,
      (∀ i, (d i).angularCutoff = (d₀ i).angularCutoff) →
      (∀ i, (d i).highCutoff = (d₀ i).highCutoff) →
      ∀ u : AugmentedInput n ι, (∀ s, u ∈ augmentedInputLevel n ι s) →
      (augmentedInputSobolevScale n ι).gradeNorm (k + (3 + (n - 1)) + 2) u ≤ δ →
      ∃ v : ι → CarrierVariable n → ℝ,
        (∀ i, ContDiff ℝ ∞ (v i)) ∧
        (∀ i, v i =ᵐ[carrierMeasure n] initialDensity (d i) 2 (u.fst.snd i)) ∧
        (∀ i p, 1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) ∧
        (∀ i, ContDiff ℝ ∞ (densityOnInitialLabels (v i))) ∧
        (∀ i, cNorm (Kin i) k (densityOnInitialLabels (v i)) ≤ 1) ∧
        (∀ i s, cNorm univ s (v i) ≤ C s *
          (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u) ∧
        (∀ i s, cNorm (Kin i) s (densityOnInitialLabels (v i)) ≤ C s *
          (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u) ∧
        ∀ σ : ℝ, 0 < σ →
          (∀ i, ContDiff ℝ ∞ (fun p ↦ positiveDensityAmplitude σ (v i p))) ∧
          (∀ i p, 0 < positiveDensityAmplitude σ (v i p)) ∧
          ∀ i p, positiveDensityAmplitude σ (v i p) ^ 2 = σ ^ 2 * (1 + v i p) := by
  obtain ⟨C, hC, hconstruct⟩ := exists_uncut_density_estimates d₀ hρsmooth hcρ
    hχsmooth hlow hhi hρ Kin hKin
  refine ⟨C, hC, (1 / 2) / C k, div_pos (by norm_num) (hC k), ?_⟩
  intro d hangular hhigh u hu hsmall
  obtain ⟨v, hv, he, _hpositions, hnorm, hjet, hlabel⟩ := hconstruct d hangular hhigh u hu
  have hb : C k * (augmentedInputSobolevScale n ι).gradeNorm
      (k + (3 + (n - 1)) + 2) u ≤ 1 / 2 := by
    rw [mul_comm]
    exact (le_div_iff₀ (hC k)).mp hsmall
  have hi (i : ι) (p : CarrierVariable n) :
      1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
    have ht := (hjet i k 0 (Nat.zero_le k) p).trans hb
    have hn : |v i p| ≤ (1 / 2 : ℝ) := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using ht
    obtain ⟨hl, hr⟩ := abs_le.mp hn
    constructor <;> linarith
  refine ⟨v, hv, he, hi, fun i ↦ contDiff_densityOnInitialLabels (hv i),
    (fun i ↦ (hlabel i k).trans (hb.trans (by norm_num))), hnorm, hlabel, ?_⟩
  intro σ hσ
  exact ⟨fun i ↦ (positiveDensityAmplitude_properties hσ (hv i) (hi i)).1,
    fun i ↦ (positiveDensityAmplitude_properties hσ (hv i) (hi i)).2.1,
    fun i ↦ (positiveDensityAmplitude_properties hσ (hv i) (hi i)).2.2⟩

/-- The fixed synthesis reserve is paid ONCE. This is the exact high-order
passage from task22's raw estimate at reserve `r₀+q` to the current initial
label profile at reserve `r₀`, with `q=3+(n-1)+2`.
It is applied to the representative constructed above, not a new density. -/
theorem label_profile_of_raw_profile
    (Kin : Set (Euclidean (n - 1) × Euclidean 3))
    (u : AugmentedInput n ι) (v : CarrierVariable n → ℝ)
    (C D : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s)
    (hv : ∀ s, cNorm Kin s (densityOnInitialLabels v) ≤ C s *
      (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u)
    {T : ℝ} (r₀ : ℕ)
    (hraw : ∀ s, (augmentedInputSobolevScale n ι).gradeNorm s u ≤
      D s * T ^ (s - (r₀ + (3 + (n - 1)) + 2))) :
    HasDerivativeProfile Kin (densityOnInitialLabels v) r₀ T
      (fun s ↦ C s * D (s + (3 + (n - 1)) + 2)) := by
  intro s
  have h := (hv s).trans (mul_le_mul_of_nonneg_left (hraw _) (hC s))
  have he : s + (3 + (n - 1)) + 2 - (r₀ + (3 + (n - 1)) + 2) = s - r₀ := by omega
  simpa only [he, mul_assoc] using h

/-- Positive square root preserves the full derivative reserve on the original
label domain. Constants are fixed before the scale and the current density;
there is no false uniform high-order `O(σ)` assertion for current histories
(`app:ch_background:eq:bg-current-profile`). -/
theorem exists_positive_initial_profile
    (Kin : Set (Euclidean (n - 1) × Euclidean 3)) (hKin : IsCompact Kin)
    (σ : ℝ) (B : ℕ → ℝ) (hB : ∀ s, 0 ≤ B s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ), ContDiff ℝ ∞ v →
      (∀ p ∈ Kin, 1 + v p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      ∀ (T : ℝ), 1 ≤ T → ∀ r₀ : ℕ, HasDerivativeProfile Kin v r₀ T B →
        HasDerivativeProfile Kin (fun p ↦ positiveDensityAmplitude σ (v p)) r₀ T C := by
  let I : Set ℝ := Icc (-1 / 2) (1 / 2)
  let g : ℝ → ℝ := positiveDensityAmplitude σ
  have hg (t : ℝ) (ht : t ∈ I) : ContDiffAt ℝ ∞ g t :=
    contDiffAt_positiveDensityAmplitude σ contDiffAt_id (by
      dsimp [I] at ht
      linarith [ht.1])
  let A := fun s ↦ cNorm I s g
  let C := fun r ↦ ∑ j ∈ Finset.range (r + 1), ResponseTransfer.GradedPrimitives.compositionConstant A B j
  have hA (s) : 0 ≤ A s := cNorm_nonneg ..
  refine ⟨C, fun r ↦ Finset.sum_nonneg (fun j _ ↦
    ResponseTransfer.GradedPrimitives.compositionConstant_nonneg hA hB j), ?_⟩
  intro v hv hi T hT r₀ hprofile
  have hmap : MapsTo v Kin I := by
    intro p hp
    have hh := hi p hp
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  exact DerivativeBounds.hasDerivativeProfile_fixed_smooth_comp hKin
    (fun p _ ↦ hv.contDiffAt) (fun p hp ↦ hg (v p) (hmap hp)) A B hA hB hT r₀ hprofile
    (fun s p hp ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt isCompact_Icc
      (fun t ht ↦ (hg t ht).of_le (by simp)) (hmap hp) le_rfl)

end JanetCartan.PhysicalBackground
