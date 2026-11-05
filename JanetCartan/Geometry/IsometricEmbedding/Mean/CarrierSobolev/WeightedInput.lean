module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.InputScale
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.TransverseWeight

/-!
# Weighted carrier bounds from the full initial scale

The concrete augmented scale of `app:ch_background:prop:bg-adjoint` controls
all carrier transverse Bessel energies used in the raw cutoff estimate
following `app:ch_background:defn:bg-mixed`. Weighted membership and the norm
bound follow from full mixed physical Sobolev membership; no geometric
adjoint or inverse estimate is assumed.
-/

@[expose] public noncomputable section

namespace JanetCartan.CarrierSobolev
open ContinuumRow RawCutoffBounds

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Membership in the full `X^s` domain supplies each raw carrier's transverse
weighted membership required by the cutoff estimate following
`app:ch_background:defn:bg-mixed`. -/
theorem augmentedInput_carrierWeightedMem {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) (i : ι) :
    CarrierWeightedMem (transverseBesselWeight s) (u.fst.snd i) :=
  ((mem_augmentedInputLevel_iff s u).mp hu).2.1 i |>.carrierWeightedMem_transverseBesselWeight

/-- Every carrier's transverse weighted norm is bounded by the full initial
`X^s` norm with constant one. This connects `app:ch_background:eq:bg-r-inverse`
to `RawCutoffBounds.carrierSquaredCutoff_tail` without a new analytic premise. -/
theorem carrierWeightedNorm_le_augmentedInput_gradeNorm {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) (i : ι) :
    carrierWeightedNorm (transverseBesselWeight s) (u.fst.snd i)
      (augmentedInput_carrierWeightedMem hu i) ≤
        (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  exact (carrierWeightedNorm_transverseBesselWeight_le
    (RawSobolevSpace.toRawL2_mem s (v.fst.snd i))).trans
      ((RawSobolevSpace.norm_eq s (v.fst.snd i)).symm.le.trans
        ((PiLp.norm_apply_le v.fst.snd i).trans
          ((WithLp.norm_snd_le _ v.fst).trans (WithLp.norm_fst_le _ v))))

end JanetCartan.CarrierSobolev
