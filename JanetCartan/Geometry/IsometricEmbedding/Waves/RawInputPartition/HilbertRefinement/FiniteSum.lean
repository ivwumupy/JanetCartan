module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement.Band

/-! # The full finite Hilbert identification

All prefixes retain both sharp components of each wide band on the same full
input, as required by `app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

/-- Refinement of the full finite sum, with the literal shared refined radii
(`app:ch_waves:thm:individual`). -/
def wideRefinement (n J : ℕ) : WideInput n J ≃ₗᵢ[ℂ] RefinedInput n J where
  toFun v := WithLp.toLp 2 (fun i ↦ bandRefinement n i.1.val (v i.1) i.2)
  invFun w := WithLp.toLp 2 (fun j ↦ (bandRefinement n j.val).symm
    (WithLp.toLp 2 (fun b ↦ w (j, b))))
  left_inv v := by
    apply PiLp.ext
    intro j
    exact (bandRefinement n j.val).symm_apply_apply (v j)
  right_inv w := by
    apply PiLp.ext
    intro i
    exact congrArg (fun v : BandPair n i.1.val ↦ v i.2)
      ((bandRefinement n i.1.val).apply_symm_apply
        (WithLp.toLp 2 (fun b ↦ w (i.1, b))))
  map_add' v w := by
    apply PiLp.ext
    intro i
    exact congrArg (fun v : BandPair n i.1.val ↦ v i.2)
      (map_add (bandRefinement n i.1.val) (v i.1) (w i.1))
  map_smul' c v := by
    apply PiLp.ext
    intro i
    exact congrArg (fun v : BandPair n i.1.val ↦ v i.2)
      (map_smul (bandRefinement n i.1.val) c (v i.1))
  norm_map' v := by
    change ‖WithLp.toLp 2 (fun i : RefinedIndex J ↦
      bandRefinement n i.1.val (v i.1) i.2)‖ = ‖v‖
    have h : ‖WithLp.toLp 2 (fun i : RefinedIndex J ↦
        bandRefinement n i.1.val (v i.1) i.2)‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      exact (PiLp.norm_sq_eq_of_L2 _ (bandRefinement n j.val (v j))).symm.trans
        (congrArg (fun r : ℝ ↦ r ^ 2) ((bandRefinement n j.val).norm_map (v j)))
    nlinarith [norm_nonneg v, norm_nonneg (WithLp.toLp 2
      (fun i : RefinedIndex J ↦ bandRefinement n i.1.val (v i.1) i.2))]

/-- Literal coordinate formula for full refinement
(`app:ch_waves:thm:individual`). -/
theorem wideRefinement_apply (n J : ℕ) (v : WideInput n J) (i : RefinedIndex J) :
    wideRefinement n J v i = bandRestriction n i.1.val (v i.1) i.2 := rfl

/-- The inverse reassembles the two sharp pieces of each original band
(`app:ch_waves:thm:individual`). -/
theorem wideRefinement_symm_apply (n J : ℕ) (w : RefinedInput n J) (j : Fin J) :
    (wideRefinement n J).symm w j =
      bandAssembly n j.val (WithLp.toLp 2 (fun b ↦ w (j, b))) := rfl

/-- Reassembly after full refinement returns the original full datum
(`app:ch_waves:thm:individual`). -/
theorem wideRefinement_left_inverse (n J : ℕ) (v : WideInput n J) :
    (wideRefinement n J).symm (wideRefinement n J v) = v :=
  (wideRefinement n J).symm_apply_apply v

/-- Full refinement after reassembly returns all sharp components
(`app:ch_waves:thm:individual`). -/
theorem wideRefinement_right_inverse (n J : ℕ) (w : RefinedInput n J) :
    wideRefinement n J ((wideRefinement n J).symm w) = w :=
  (wideRefinement n J).apply_symm_apply w

/-- Refinement preserves the literal finite-sum norm (`app:ch_waves:eq:B-bounds`). -/
theorem norm_wideRefinement (n J : ℕ) (v : WideInput n J) :
    ‖wideRefinement n J v‖ = ‖v‖ := (wideRefinement n J).norm_map v

/-- Both complex quadratures, including their cross pairing, are preserved
(`app:ch_waves:thm:individual`). -/
theorem inner_wideRefinement (n J : ℕ) (v w : WideInput n J) :
    inner ℂ (wideRefinement n J v) (wideRefinement n J w) = inner ℂ v w :=
  (wideRefinement n J).inner_map_map v w

/-- The identical isometry on the underlying real Hilbert input
(`app:ch_waves:thm:individual`). -/
def realWideRefinement (n J : ℕ) : WideInput n J ≃ₗᵢ[ℝ] RefinedInput n J :=
  { toLinearEquiv := (wideRefinement n J).toLinearEquiv.restrictScalars ℝ
    norm_map' := (wideRefinement n J).norm_map }

/-- The real Hilbert pairing is preserved without discarding either quadrature
(`app:ch_waves:thm:individual`). -/
theorem inner_realWideRefinement (n J : ℕ) (v w : WideInput n J) :
    inner ℝ (realWideRefinement n J v) (realWideRefinement n J w) = inner ℝ v w :=
  (realWideRefinement n J).inner_map_map v w

/-- Original wide-band prefix acting on the same full input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def widePrefix (n J L : ℕ) : WideInput n J →L[ℂ] WideInput n J :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin J ↦
      if j.val < L then PiLp.proj 2 _ j else 0)

/-- Coordinate formula for the original prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem widePrefix_apply (n J L : ℕ) (v : WideInput n J) (j : Fin J) :
    widePrefix n J L v j = if j.val < L then v j else 0 := by
  by_cases h : j.val < L <;> simp [widePrefix, h, PiLp.proj_apply]

/-- Refinement intertwines the unchanged grouped prefixes
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideRefinement_prefix (n J L : ℕ) (v : WideInput n J) :
    wideRefinement n J (widePrefix n J L v) = refinedPrefix n J L (wideRefinement n J v) := by
  apply PiLp.ext
  intro i
  change wideRefinement n J (widePrefix n J L v) i =
    refinedPrefix n J L (wideRefinement n J v) i
  have hf := widePrefix_apply n J L v i.1
  have hg := refinedPrefix_apply n J L (wideRefinement n J v) i
  by_cases h : i.1.val < L
  · rw [ite_eq_left h] at hf hg
    rw [hg, wideRefinement_apply, hf, wideRefinement_apply]
  · rw [ite_eq_right h] at hf hg
    rw [hg, wideRefinement_apply, hf, map_zero]
    rfl

end JanetCartan.RawInputPartition
