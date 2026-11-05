module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.ProductBounds.Coefficient
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Smooth
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Postcomposition
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.ReducedOperator

/-!
# Smooth bounds for the actual image coefficient multipliers

The product estimate for `app:ch_background:eq:bg-commutator` retains the
coefficient order and complementary datum order. Its consumer is the extension
of the existing cutoff multiplier to every Sobolev level.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace ContinuumRow

variable {n : ℕ}

/-- The norm of the smooth realization is the manuscript's Fourier Sobolev norm
(`app:ch_background:prop:bg-inverse`). -/
theorem multiplier_norm_ofSmooth (s : ℕ) (f : Torus n → Euclidean n)
    (hf : IsSmoothPeriodic f) : ‖ofSmooth s f hf‖ = periodicSobolevNorm s f := by
  rw [norm_eq]
  simp only [periodicSobolevNorm, periodicFourierCoeff_congr_ae (toL2_ofSmooth_ae s f hf)]

/-- Changing the realization order preserves the same smooth field
(`app:ch_background:eq:bg-commutator`). -/
theorem multiplier_inclusion_ofSmooth {s t : ℕ} (h : s ≤ t)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    inclusion h (ofSmooth t f hf) = ofSmooth s f hf := by
  apply toL2_injective s
  rfl

private theorem multiplier_inclusion_apply {s t : ℕ} (h : s ≤ t)
    (u : PeriodicSobolevSpace n (Euclidean n) t) :
    inclusion h u = (toLevel s).symm
      ⟨(toLevel t u).val, antitone_periodicSobolevLevel h (toLevel t u).property⟩ := rfl

/-- A change of Sobolev level keeps the underlying L² datum unchanged
(`app:ch_background:eq:bg-commutator`). -/
theorem multiplier_toL2_inclusion {s t : ℕ} (h : s ≤ t)
    (u : PeriodicSobolevSpace n (Euclidean n) t) :
    toL2 s (inclusion h u) = toL2 t u := by
  rw [toL2_apply, multiplier_inclusion_apply, LinearEquiv.apply_symm_apply, toL2_apply]

/-- Literal multiplication agrees with the smooth product at any realization
orders (`app:ch_background:eq:bg-commutator`). -/
theorem cutoffMultiplier_ofSmooth (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s t : ℕ) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    cutoffMultiplier q (toL2 s (ofSmooth s f hf)) =
      toL2 t (ofSmooth t (fun x ↦ q x • f x) (Exterior.smooth_smul hq hf)) := by
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn q (toL2 s (ofSmooth s f hf)),
    toL2_ofSmooth_ae s f hf, toL2_ofSmooth_ae t _ (Exterior.smooth_smul hq hf)]
      with x hx hy hz
  rw [hx, hy, hz]

/-- Finite jet/lower-Sobolev product estimate on smooth fields, with constant
only depending on dimension and order (`app:ch_background:eq:bg-commutator`). -/
theorem norm_ofSmooth_cutoff_le (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    ‖ofSmooth s (fun x ↦ q x • f x) (Exterior.smooth_smul hq hf)‖ ≤
      AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ j ∈ Finset.range (s + 1), cNorm (fundamentalCell n) j (periodicLift q) *
          ‖ofSmooth (s - j) f hf‖ := by
  simp only [multiplier_norm_ofSmooth]
  exact AuxiliaryRawBand.periodicSobolevNorm_smul_le q f hq hf s

/-- The coarser bound is used only for completion, not for the single-high
estimate (`app:ch_background:eq:bg-commutator`). -/
theorem norm_ofSmooth_cutoff_le_top (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    ‖ofSmooth s (fun x ↦ q x • f x) (Exterior.smooth_smul hq hf)‖ ≤
      (AuxiliaryRawBand.coefficientProductConstant n s * (s + 1) *
        cNorm (fundamentalCell n) s (periodicLift q)) * ‖ofSmooth s f hf‖ := by
  apply (norm_ofSmooth_cutoff_le q hq s f hf).trans
  calc
    _ ≤ AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ _j ∈ Finset.range (s + 1),
          cNorm (fundamentalCell n) s (periodicLift q) * ‖ofSmooth s f hf‖ := by
      apply mul_le_mul_of_nonneg_left _ (AuxiliaryRawBand.coefficientProductConstant_nonneg n s)
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul
        (cNorm_mono_order (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        _ (norm_nonneg _) (cNorm_nonneg _ _ _)
      exact periodicSobolevSeminorm_mono (Nat.sub_le s j) (toLevel s (ofSmooth s f hf))
    _ = _ := by simp; ring

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
