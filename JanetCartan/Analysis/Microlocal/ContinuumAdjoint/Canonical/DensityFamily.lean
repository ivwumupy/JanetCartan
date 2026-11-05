module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Density
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.DirectSum

/-!
# Finite canonical density family on the full input space

The sum in `app:ch_background:eq:bg-density-adjoint` is bounded by the norm of
the SAME augmented initial space, including every carrier and both auxiliary
summands. This instantiates each multiplier bound with the actual fixed masks.
No adjoint estimate is assumed. The final adjoint construction must put its
output in this input space before composing with this result.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev DensityMultiplier

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Every carrier component is controlled by the full augmented Hilbert norm
before physical cutoffs (`app:ch_background:prop:bg-adjoint`). -/
theorem carrier_norm_le_augmentedInput (s : ℕ)
    (u : AugmentedInputSobolevSpace n ι s) (i : ι) :
    rawSobolevNorm s (RawSobolevSpace.toRawL2 s (u.fst.snd i)) ≤ ‖u‖ := by
  rw [← RawSobolevSpace.norm_eq]
  exact (PiLp.norm_apply_le u.fst.snd i).trans
    ((WithLp.norm_snd_le _ u.fst).trans (WithLp.norm_fst_le _ u))

/-- The actual finite density family has one uniform constant at each order,
both before and after all physical initial cutoffs. Constants depend only on
the fixed masks and the order. This supplies the multiplier input of
`ContinuumInverse.density_rightInverse_le`, without any estimate for that
inverse (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densityFamily_bounds
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    (r a : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (b : ι → ContDiffBump (0 : CarrierVariable n)) (s : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : AugmentedInputSobolevSpace n ι (s + 1),
      let f := fun i ↦ RawSobolevSpace.toRawL2 (s + 1) (u.fst.snd i)
      let hf := fun i ↦ (RawSobolevSpace.toRawL2_mem (s + 1) (u.fst.snd i)).mono
        (by omega : 1 ≤ s + 1)
      (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
        (densityUncut (z₀ i) (θ₀ i) (hr i) (ha i) (f i) (hf i))) ∧
        MemPhysicalSobolev s (physicalComplexifyL2
        (density (z₀ i) (θ₀ i) (hr i) (ha i) (b i) (f i) (hf i)))) ∧
      (∑ i, physicalSobolevNorm s (physicalComplexifyL2
        (densityUncut (z₀ i) (θ₀ i) (hr i) (ha i) (f i) (hf i)))) ≤ L * ‖u‖ ∧
      (∑ i, physicalSobolevNorm s (physicalComplexifyL2
        (density (z₀ i) (θ₀ i) (hr i) (ha i) (b i) (f i) (hf i)))) ≤ L * ‖u‖ := by
  classical
  choose L hL hb using fun i ↦ exists_density_bounds (z₀ i) (θ₀ i) (hr i) (ha i) (b i) s
  refine ⟨∑ i, L i, Finset.sum_nonneg (fun i _ ↦ hL i), fun u ↦ ?_⟩
  have h i := hb i (RawSobolevSpace.toRawL2 (s + 1) (u.fst.snd i))
    (RawSobolevSpace.toRawL2_mem (s + 1) (u.fst.snd i))
  refine ⟨fun i ↦ ⟨(h i).2.1.1, (h i).2.2.1⟩, ?_, ?_⟩
  · calc
      _ ≤ ∑ i, L i * rawSobolevNorm (s + 1)
          (RawSobolevSpace.toRawL2 (s + 1) (u.fst.snd i)) :=
        Finset.sum_le_sum (fun i _ ↦ (h i).2.1.2)
      _ ≤ ∑ i, L i * ‖u‖ := Finset.sum_le_sum (fun i _ ↦
        mul_le_mul_of_nonneg_left (carrier_norm_le_augmentedInput (s + 1) u i) (hL i))
      _ = _ := (Finset.sum_mul _ _ _).symm
  · calc
      _ ≤ ∑ i, L i * rawSobolevNorm (s + 1)
          (RawSobolevSpace.toRawL2 (s + 1) (u.fst.snd i)) :=
        Finset.sum_le_sum (fun i _ ↦ (h i).2.2.2)
      _ ≤ ∑ i, L i * ‖u‖ := Finset.sum_le_sum (fun i _ ↦
        mul_le_mul_of_nonneg_left (carrier_norm_le_augmentedInput (s + 1) u i) (hL i))
      _ = _ := (Finset.sum_mul _ _ _).symm

end JanetCartan.ContinuumAdjoint.Canonical
