module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.DensityFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.InputScale
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.Extension

/-!
# Concrete initial-scale inputs for the common inverse

The density sizes are the actual sums in
`app:ch_background:eq:bg-density-adjoint`, on the original augmented input.
Their one-derivative bounds follow from the constructed fixed multipliers.
Outside the raw order-one domain the sizes are set to zero; every use in the
inverse theorem proves domain membership first.

The final lemma only converts the constructed Sobolev lifts to the existing
`GradedScale` interface. It does not supply a geometric adjoint estimate.
Its producer is `exists_finite_projected_augmented_densityAdjoints`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped Classical

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev DensityMultiplier PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Sum of the actual uncut density norms, retaining every carrier/initial
coordinate and both quadratures (`app:ch_background:eq:bg-density-adjoint`). -/
def densityUncutFamilySize (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n-1))
    {r a : ι → ℝ} (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (s : ℕ) (u : AugmentedInput n ι) : ℝ :=
  if h : ∀ i, MemRawSobolev 1 (u.fst.snd i) then
    ∑ i, physicalSobolevNorm s (physicalComplexifyL2
      (densityUncut (z₀ i) (θ₀ i) (hr i) (ha i) (u.fst.snd i) (h i)))
  else 0

/-- Sum of the actual cutoff density norms. The multiplier is the fixed
half-order Fourier symbol and original physical bump
(`app:ch_background:eq:bg-density-adjoint`). -/
def densityFamilySize (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n-1))
    {r a : ι → ℝ} (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (b : ι → ContDiffBump (0 : CarrierVariable n))
    (s : ℕ) (u : AugmentedInput n ι) : ℝ :=
  if h : ∀ i, MemRawSobolev 1 (u.fst.snd i) then
    ∑ i, physicalSobolevNorm s (physicalComplexifyL2
      (density (z₀ i) (θ₀ i) (hr i) (ha i) (b i) (u.fst.snd i) (h i)))
  else 0

/-- On the actual order-one domain the uncut size is exactly the original
sum, not its totalized value (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityUncutFamilySize_eq (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n-1))
    {r a : ι → ℝ} (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (s : ℕ) (u : AugmentedInput n ι) (hu : ∀ i, MemRawSobolev 1 (u.fst.snd i)) :
    densityUncutFamilySize z₀ θ₀ hr ha s u =
      ∑ i, physicalSobolevNorm s (physicalComplexifyL2
        (densityUncut (z₀ i) (θ₀ i) (hr i) (ha i) (u.fst.snd i) (hu i))) := by
  simp only [densityUncutFamilySize, dite_eq_left hu]

/-- On its domain the cutoff size is exactly the sum of the literal density
norms (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityFamilySize_eq (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n-1))
    {r a : ι → ℝ} (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (b : ι → ContDiffBump (0 : CarrierVariable n))
    (s : ℕ) (u : AugmentedInput n ι) (hu : ∀ i, MemRawSobolev 1 (u.fst.snd i)) :
    densityFamilySize z₀ θ₀ hr ha b s u =
      ∑ i, physicalSobolevNorm s (physicalComplexifyL2
        (density (z₀ i) (θ₀ i) (hr i) (ha i) (b i) (u.fst.snd i) (hu i))) := by
  simp only [densityFamilySize, dite_eq_left hu]

/-- The actual fixed multiplier input to
`ContinuumInverse.density_rightInverse_le`, on the same augmented scale.
Membership and both estimates are derived from the full mixed raw norm.
No inverse, adjoint or multiplier bound is assumed
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densityFamily_gradeNorm_bounds
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n-1))
    {r a : ι → ℝ} (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (b : ι → ContDiffBump (0 : CarrierVariable n)) :
    ∃ L : ℕ → ℝ, (∀ s, 0 ≤ L s) ∧
      ∀ (s : ℕ) (u : AugmentedInput n ι),
        u ∈ (augmentedInputSobolevScale n ι).level (s+1) →
        ∃ hu : ∀ i, MemRawSobolev 1 (u.fst.snd i),
          (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut (z₀ i) (θ₀ i) (hr i) (ha i) (u.fst.snd i) (hu i))) ∧
            MemPhysicalSobolev s (physicalComplexifyL2
            (density (z₀ i) (θ₀ i) (hr i) (ha i) (b i) (u.fst.snd i) (hu i)))) ∧
          densityUncutFamilySize z₀ θ₀ hr ha s u ≤
            L s * (augmentedInputSobolevScale n ι).gradeNorm (s+1) u ∧
          densityFamilySize z₀ θ₀ hr ha b s u ≤
            L s * (augmentedInputSobolevScale n ι).gradeNorm (s+1) u := by
  classical
  choose L hL hbound using fun s ↦ exists_densityFamily_bounds z₀ θ₀ r a hr ha b s
  refine ⟨L, hL, ?_⟩
  intro s u hu
  obtain ⟨v, rfl⟩ := hu
  let hv := fun i ↦ (RawSobolevSpace.toRawL2_mem (s+1) (v.fst.snd i)).mono
    (by omega : 1 ≤ s+1)
  have h := hbound s v
  refine ⟨hv, h.1, ?_, ?_⟩
  · change _ ≤ L s * (augmentedInputSobolevScale n ι).gradeNorm (s+1)
      (augmentedInputToL2 (s+1) v)
    rw [augmentedInputSobolevScale_gradeNorm (s+1) v]
    unfold densityUncutFamilySize
    split_ifs with hm
    · exact h.2.1
    · exact False.elim (hm hv)
  · change _ ≤ L s * (augmentedInputSobolevScale n ι).gradeNorm (s+1)
      (augmentedInputToL2 (s+1) v)
    rw [augmentedInputSobolevScale_gradeNorm (s+1) v]
    unfold densityFamilySize
    split_ifs with hm
    · exact h.2.2
    · exact False.elim (hm hv)

/-- Translate actual Sobolev lifts into the regularity and raw norm inputs
of `ContinuumInverse.rightInverse_mem` and `rightInverse_gradeNorm_le`.
The construction must supply `hlift`; the uniform augmented canonical
constructor proves it from primitive data
(`app:ch_background:prop:bg-adjoint`). -/
theorem augmentedAdjoint_gradeNorm_of_lifts (A : AugmentedInput n ι →L[ℝ] OutputL2 n)
    (s : ℕ) (C H : ℝ)
    (hlift : ∀ v : PeriodicSobolevSpace n (Euclidean n) s,
      ∃ u : AugmentedInputSobolevSpace n ι s,
        augmentedInputToL2 s u = A.adjoint (toL2 s v) ∧
        ‖u‖ ≤ C * (‖v‖ + H * ‖toL2 s v‖)) :
    ∀ v : OutputL2 n, v ∈ (periodicSobolevScale n (Euclidean n)).level s →
      A.adjoint v ∈ (augmentedInputSobolevScale n ι).level s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint v) ≤
        C * ((periodicSobolevScale n (Euclidean n)).gradeNorm s v + H * ‖v‖) := by
  intro v hv
  let w := ofL2 s v hv
  have hw : toL2 s w = v := toL2_ofL2 ..
  obtain ⟨u, hu, hb⟩ := hlift w
  rw [hw] at hu hb
  refine ⟨⟨u, hu⟩, ?_⟩
  rw [← hu, augmentedInputSobolevScale_gradeNorm]
  have hwNorm : ‖w‖ = (periodicSobolevScale n (Euclidean n)).gradeNorm s v := by
    have he : inclusion (Nat.le_refl s) w = w := by
      apply toL2_injective s
      exact multiplier_toL2_inclusion _ _
    simpa only [he, hw] using multiplier_norm_inclusion_eq_gradeNorm (Nat.le_refl s) w
  simpa only [hwNorm] using hb

end JanetCartan.ContinuumAdjoint.Canonical
