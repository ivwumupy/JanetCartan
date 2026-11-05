module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.SectionDetectorSupport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AngularPartition

/-!
# Compatible carrier weights on the selected joint detector cover

Construct the carrier weights inside the actual returned plateau radii and
use the existing angular square masks on the SAME selected labels. Every
original detector direction retains a nonzero local mask at its original
incidence root. The angular square sum is unchanged, and the carrier weights
meet the support and common `PatchBounds` inputs of `FiniteRealization`.
-/

@[expose] public noncomputable section
open Set Metric NormedSpace
open scoped ContDiff

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic SeparatedSampling

/-- Construct fixed smooth carrier weights on the actual plateau balls,
with one common sampling cube and unit upper bound. The half-radius balls
used in the joint cover remain plateaus of the new weights
(`app:ch_waves:thm:sampling`). -/
theorem exists_joint_cover_carrier_weights {I : Type*} [Fintype I]
    (z₀ : I → Euclidean 3) (d : I → ℝ) (hd : ∀ i, 0 < d i)
    (ψ : I → Point → ℝ)
    (hψ : ∀ i z, WithLp.toLp 2 z ∈ closedBall (z₀ i) (d i) → ψ i z = 1) :
    ∃ B > (0 : ℝ), ∃ φ : I → Point → ℝ,
      (∀ i, ContDiff ℝ ∞ (φ i)) ∧ (∀ i, HasCompactSupport (φ i)) ∧
      (∀ i, PatchBounds (φ i) B 1) ∧
      (∀ i z, WithLp.toLp 2 z ∈ closedBall (z₀ i) (d i / 2) → φ i z = 1) ∧
      (∀ i z, φ i z ≠ 0 → WithLp.toLp 2 z ∈ ball (z₀ i) (d i)) ∧
      (∀ i z, φ i z ≠ 0 → ψ i z = 1) := by
  classical
  let f (i : I) : ContDiffBump (z₀ i) :=
    ⟨d i / 2, d i, div_pos (hd i) (by norm_num), by linarith [hd i]⟩
  let φ (i : I) (z : Point) : ℝ := f i (WithLp.toLp 2 z)
  have hc (i : I) : HasCompactSupport (φ i) :=
    (f i).hasCompactSupport.comp_homeomorph
      (PiLp.homeomorph (p := 2) (fun _ : Fin 3 ↦ ℝ)).symm
  choose B hB hbound using fun i ↦ (hc i).isCompact.isBounded.exists_pos_norm_le
  let Bmax := 1 + ∑ i, B i
  have hsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ ↦ (hB i).le)
  have hBmax : 0 < Bmax := by dsimp [Bmax]; linarith
  have hle (i : I) : B i ≤ Bmax := by
    have := Finset.single_le_sum (fun j _ ↦ (hB j).le) (Finset.mem_univ i)
    dsimp [Bmax]
    linarith
  have hsupp (i : I) (z : Point) (hz : φ i z ≠ 0) :
      WithLp.toLp 2 z ∈ ball (z₀ i) (d i) := by
    change WithLp.toLp 2 z ∈ Function.support (f i) at hz
    simpa only [(f i).support_eq] using hz
  refine ⟨Bmax, hBmax, φ, fun i ↦ (f i).contDiff.comp (by fun_prop), hc, ?_,
    fun i z hz ↦ (f i).one_of_mem_closedBall hz, hsupp, ?_⟩
  · intro i
    exact {
      radius_nonneg := hBmax.le
      nonneg := fun _ ↦ (f i).nonneg
      le_bound := fun _ ↦ (f i).le_one
      support := fun z hz j ↦
        (show |z j| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j).trans
          ((hbound i z (subset_tsupport (φ i) hz)).trans (hle i)) }
  · exact fun i z hz ↦ hψ i z (ball_subset_closedBall (hsupp i z hz))

/-- The constructed angular square mask is strictly positive on its own
quarter-width covering ball. This keeps the same label as the carrier
plateau, rather than using unrelated finite subcovers
(`app:ch_waves:thm:sampling`). -/
theorem canonicalAngularSquareMask_pos_of_mem_ball {n : ℕ} {I : Type*} [Fintype I]
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i)
    (i : I) {η : Euclidean (n - 1)}
    (hη : normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4)) :
    0 < canonicalAngularSquareMask ηb r hηb hr i η := by
  have hone := (directionMask (normalize (ηb i))
    (angularWidth_spec (hηb i) (hr i)).1).one_of_mem_closedBall (ball_subset_closedBall hη)
  unfold canonicalAngularSquareMask
  rw [hone]
  exact div_pos zero_lt_one (canonicalAngularSquareDenominator_pos ηb r hηb hr _)

/-- Construct compatible carrier weights and angular square masks from the
original detector and the original section, using both returned local radii.
The entire closed detector support is covered, with a positive product on
the SAME selected label at each original root. The final weighted normal
reassembly still has to use these weights; the assertion here does not
identify an arbitrary previously chosen carrier weight with their sum
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem exists_sectionDetector_sampling_masks {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (hsupport : detectorDirectionSupport a ⊆ O)
    (r d : sectionDetectorSupport root a → ℝ)
    (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (ψ : sectionDetectorSupport root a → Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → ψ w z = 1) :
    ∃ labels : Finset (sectionDetectorSupport root a),
    ∃ B > (0 : ℝ), ∃ φ : labels → Point → ℝ,
    ∃ χ : labels → Euclidean (n - 1) → ℝ,
      (∀ i, ContDiff ℝ ∞ (φ i)) ∧ (∀ i, HasCompactSupport (φ i)) ∧
      (∀ i, PatchBounds (φ i) B 1) ∧
      (∀ i z, φ i z ≠ 0 → ψ i.1 z = 1) ∧
      (∀ i, χ i 0 = 0) ∧
      (∀ i η, η ≠ 0 → ContDiffAt ℝ ∞ (χ i) η) ∧
      (∀ i (t : ℝ), 0 < t → ∀ η, χ i (t • η) = χ i η) ∧
      (∀ i η, χ i η ∈ Icc (0 : ℝ) 1) ∧
      (∀ i η, χ i η ≠ 0 → normalize η ∈ closedDirections
        (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1)) ∧
      (∀ η : Euclidean (n - 1), normalize η ∈ incidentDetectorDirections T (detectorDirectionSupport a) →
        ∑ i, χ i η ^ 2 = 1) ∧
      (∀ k ∈ detectorDirectionSupport a, ∃ i : labels,
        φ i (root k).ofLp = 1 ∧
        0 < χ i (T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) := by
  classical
  obtain ⟨labels, hη, hcover⟩ :=
    exists_sectionDetector_joint_cover T hP hroot a hsupport r d hr hd ψ hplateau
  obtain ⟨B, hB, φ, hφsmooth, hφcompact, hφbound, hφone, _hφsupport, hφplateau⟩ :=
    exists_joint_cover_carrier_weights (fun i : labels ↦ i.1.1.1)
      (fun i ↦ d i.1) (fun i ↦ hd i.1) (fun i ↦ ψ i.1)
      (fun i ↦ hplateau i.1)
  let ηb := fun i : labels ↦ T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2
  let r' := fun i : labels ↦ r i.1
  let hr' := fun i : labels ↦ hr i.1
  let χ := canonicalAngularSquareMask ηb r' hη hr'
  refine ⟨labels, B, hB, φ, χ, hφsmooth, hφcompact, hφbound, hφplateau,
    canonicalAngularSquareMask_zero ηb r' hη hr',
    fun i η hn ↦ canonicalAngularSquareMask_contDiffAt ηb r' hη hr' i hn,
    canonicalAngularSquareMask_homogeneous ηb r' hη hr',
    canonicalAngularSquareMask_mem_Icc ηb r' hη hr',
    fun i η hn ↦ (canonicalAngularSquareMask_support ηb r' hη hr' i hn).2, ?_, ?_⟩
  · apply canonicalAngularSquareMask_sum_sq ηb r' hη hr'
    rintro θ ⟨k, hk, rfl⟩
    obtain ⟨i, _hz, hdir, _hp⟩ := hcover k hk
    exact ⟨i, hdir⟩
  · intro k hk
    obtain ⟨i, hz, hdir, _hp⟩ := hcover k hk
    refine ⟨i, hφone i (root k).ofLp (ball_subset_closedBall hz), ?_⟩
    exact canonicalAngularSquareMask_pos_of_mem_ball ηb r' hη hr' i hdir

end JanetCartan.Sampling
