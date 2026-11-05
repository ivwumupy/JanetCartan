module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement.Geometry

/-! # Restriction and reassembly of a single band

The genuine complex Hilbert identification for `app:ch_waves:thm:individual`.
Both quadratures are retained; no smoothness is asserted for the sharp pieces.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

/-- Restrict a wide datum to each literal sharp annulus
(`app:ch_waves:thm:individual`). -/
def bandRestriction (n j : ℕ) : WideBandL2 n j →L[ℂ] BandPair n j :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun b : Fin 2 ↦
      (annularRestriction (R := (2 : ℝ) ^ (j + b.val))).comp
        (zeroExtension (measurableSet_wideBand n j)).toContinuousLinearMap)

/-- Reassemble the sharp data by zero extension and addition on the wide band
(`app:ch_waves:thm:individual`). -/
def bandAssembly (n j : ℕ) : BandPair n j →L[ℂ] WideBandL2 n j :=
  (restriction (wideBand n j)).comp
    (∑ b : Fin 2, annularExtension.toContinuousLinearMap.comp (PiLp.proj 2 _ b))

/-- Coordinate action of the actual restriction
(`app:ch_waves:thm:individual`). -/
theorem bandRestriction_apply (n j : ℕ) (f : WideBandL2 n j) (b : Fin 2) :
    bandRestriction n j f b = annularRestriction
      (zeroExtension (measurableSet_wideBand n j) f) := rfl

/-- Literal representative of the restriction, on its annular measure
(`app:ch_waves:thm:individual`). -/
theorem bandRestriction_coeFn (n j : ℕ) (f : WideBandL2 n j) (b : Fin 2) :
    bandRestriction n j f b =ᵐ[annularMeasure n ((2 : ℝ) ^ (j + b.val))] f := by
  rw [bandRestriction_apply]
  filter_upwards [restriction_coeFn (annulus n ((2 : ℝ) ^ (j + b.val)))
      (zeroExtension (measurableSet_wideBand n j) f),
    ae_restrict_of_ae (zeroExtension_coeFn (measurableSet_wideBand n j) f),
    ae_restrict_mem (measurableSet_annulus n ((2 : ℝ) ^ (j + b.val)))] with η h₁ h₂ hη
  exact h₁.trans (h₂.trans (Set.indicator_of_mem (annulus_subset_wideBand n j b hη) _))

/-- Pointwise formula for the reassembly operator
(`app:ch_waves:thm:individual`). -/
theorem bandAssembly_apply (n j : ℕ) (v : BandPair n j) :
    bandAssembly n j v = restriction (wideBand n j)
      (annularExtension (v 0) + annularExtension (v 1)) := by
  simp [bandAssembly, Fin.sum_univ_two, PiLp.proj_apply]

/-- The actual reassembly is the sum of the zero-extended representatives
(`app:ch_waves:thm:individual`). -/
theorem bandAssembly_coeFn (n j : ℕ) (v : BandPair n j) :
    bandAssembly n j v =ᵐ[volume.restrict (wideBand n j)] fun η ↦
      (annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val))).indicator (v 0) η +
      (annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val))).indicator (v 1) η := by
  rw [bandAssembly_apply]
  filter_upwards [restriction_coeFn (wideBand n j)
      (annularExtension (v 0) + annularExtension (v 1)),
    ae_restrict_of_ae (Lp.coeFn_add (annularExtension (v 0)) (annularExtension (v 1))),
    ae_restrict_of_ae (zeroExtension_coeFn
      (measurableSet_annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val))) (v 0)),
    ae_restrict_of_ae (zeroExtension_coeFn
      (measurableSet_annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val))) (v 1))]
    with η h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (congrArg₂ (· + ·) h₃ h₄))

/-- Reassembly after restriction is the original wide datum
(`app:ch_waves:thm:individual`). -/
theorem bandAssembly_bandRestriction (n j : ℕ) (f : WideBandL2 n j) :
    bandAssembly n j (bandRestriction n j f) = f := by
  apply Lp.ext
  have h₀ := (ae_eq_restrict_iff_indicator_ae_eq
    (measurableSet_annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val)))).mp
      (bandRestriction_coeFn n j f 0)
  have h₁ := (ae_eq_restrict_iff_indicator_ae_eq
    (measurableSet_annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val)))).mp
      (bandRestriction_coeFn n j f 1)
  filter_upwards [bandAssembly_coeFn n j (bandRestriction n j f),
    ae_restrict_of_ae h₀, ae_restrict_of_ae h₁,
    ae_restrict_of_ae (ae_not_mem_both_annuli n j),
    ae_restrict_mem (measurableSet_wideBand n j)] with η ha h₀ h₁ hd hw
  rw [ha, h₀, h₁]
  rw [wideBand_eq_union] at hw
  rcases hw with h | h
  · have hh := fun h' ↦ hd ⟨h, h'⟩
    simp only [Set.indicator_of_mem h, Set.indicator_of_notMem hh, add_zero]
  · have hh := fun h' ↦ hd ⟨h', h⟩
    simp only [Set.indicator_of_mem h, Set.indicator_of_notMem hh, zero_add]

/-- Restriction after reassembly returns both original complex components
(`app:ch_waves:thm:individual`). -/
theorem bandRestriction_bandAssembly (n j : ℕ) (v : BandPair n j) :
    bandRestriction n j (bandAssembly n j v) = v := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  have ha := ae_mono (Measure.restrict_mono (annulus_subset_wideBand n j b) le_rfl)
    (bandAssembly_coeFn n j v)
  filter_upwards [bandRestriction_coeFn n j (bandAssembly n j v) b, ha,
    ae_restrict_of_ae (ae_not_mem_both_annuli n j),
    ae_restrict_mem (measurableSet_annulus n ((2 : ℝ) ^ (j + b.val)))]
    with η hr ha hd hb
  change (bandRestriction n j (bandAssembly n j v) b) η = (v b) η
  rw [hr, ha]
  fin_cases b
  · change η ∈ annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val)) at hb
    have hh := fun h' ↦ hd ⟨hb, h'⟩
    rw [Set.indicator_of_mem hb, Set.indicator_of_notMem hh, add_zero]
    rfl
  · change η ∈ annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val)) at hb
    have hh := fun h' ↦ hd ⟨h', hb⟩
    rw [Set.indicator_of_mem hb, Set.indicator_of_notMem hh, zero_add]
    rfl

/-- The complex pairing of reassembly and restriction, including the imaginary
quadrature (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem inner_bandAssembly (n j : ℕ) (v : BandPair n j) (f : WideBandL2 n j) :
    inner ℂ (bandAssembly n j v) f = inner ℂ v (bandRestriction n j f) := by
  rw [bandAssembly_apply, ← inner_conj_symm]
  rw [← inner_zeroExtension (measurableSet_wideBand n j), inner_add_right,
    map_add, inner_conj_symm, inner_conj_symm]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, bandRestriction_apply]
  exact congrArg₂ (· + ·) (inner_zeroExtension _ _ _) (inner_zeroExtension _ _ _)

/-- Restriction preserves the literal Hilbert norm
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_bandRestriction (n j : ℕ) (f : WideBandL2 n j) :
    ‖bandRestriction n j f‖ = ‖f‖ := by
  have h := inner_bandAssembly n j (bandRestriction n j f) f
  rw [bandAssembly_bandRestriction] at h
  have hr := congrArg (RCLike.re (K := ℂ)) h
  simp only [inner_self_eq_norm_sq] at hr
  nlinarith [norm_nonneg f, norm_nonneg (bandRestriction n j f)]

/-- Actual complex linear isometric equivalence from one wide band to its two
sharp components (`app:ch_waves:thm:individual`). -/
def bandRefinement (n j : ℕ) : WideBandL2 n j ≃ₗᵢ[ℂ] BandPair n j where
  toFun := bandRestriction n j
  invFun := bandAssembly n j
  left_inv := bandAssembly_bandRestriction n j
  right_inv := bandRestriction_bandAssembly n j
  map_add' := map_add (bandRestriction n j)
  map_smul' := map_smul (bandRestriction n j)
  norm_map' := norm_bandRestriction n j

end JanetCartan.RawInputPartition
