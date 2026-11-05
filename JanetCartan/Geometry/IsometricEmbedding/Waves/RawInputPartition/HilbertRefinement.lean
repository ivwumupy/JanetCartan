module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement.FiniteSum
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement.Channel

/-!
# Wide-band Hilbert refinement and unchanged synthesis normals

For `app:ch_waves:thm:individual`, the original smooth wide-band data are
identified isometrically with the shared literal sharp annular data. Restriction
and zero-extension are actual inverse maps, retaining both complex quadratures.
The finite synthesis uses the original mask times `sqrt ‖η‖`; reassembly proves
its equality with `RawInputHilbert.synthesis`. Consequently output normals and
the unchanged grouped-prefix normals of `app:ch_waves:eq:sampling-prefix-normal`
agree. Sharp indicators serve only the measurable Hilbert decomposition.

The mask hypotheses are only measurability and bounds on the wide bands. The
constructed `radialBand` is supported there by `radialBand_eq_zero_off_wideBand`.
-/

@[expose] public noncomputable section
open MeasureTheory
set_option maxHeartbeats 800000
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

variable {n J : ℕ} {M : Fin J → ℝ} {β : Fin J → Euclidean (n - 1) → ℂ}

/-- Actual wide-band synthesis on the original full finite input
(`app:ch_waves:thm:individual`). -/
def wideSynthesis
    (hβ : ∀ j, AEStronglyMeasurable (β j) (volume.restrict (wideBand n j.val)))
    (hb : ∀ j, ∀ᵐ η ∂volume.restrict (wideBand n j.val), ‖β j η‖ ≤ M j) :
    WideInput n J →L[ℂ] Output n :=
  ∑ j, (wideChannel (hβ j) (hb j)).comp (PiLp.proj 2 _ j)

/-- Literal sum of the original half-derivative channels
(`app:ch_waves:thm:individual`). -/
theorem wideSynthesis_apply
    (hβ : ∀ j, AEStronglyMeasurable (β j) (volume.restrict (wideBand n j.val)))
    (hb : ∀ j, ∀ᵐ η ∂volume.restrict (wideBand n j.val), ‖β j η‖ ≤ M j)
    (v : WideInput n J) :
    wideSynthesis hβ hb v = ∑ j, wideChannel (hβ j) (hb j) (v j) := by
  simp [wideSynthesis, PiLp.proj_apply]

/-- Refinement preserves the actual synthesis operator, not just a norm bound
(`app:ch_waves:thm:individual`). -/
theorem wideSynthesis_eq_refined
    (hβ : ∀ j, AEStronglyMeasurable (β j) (volume.restrict (wideBand n j.val)))
    (hM : ∀ j, 0 ≤ M j)
    (hb : ∀ j, ∀ᵐ η ∂volume.restrict (wideBand n j.val), ‖β j η‖ ≤ M j) :
    wideSynthesis hβ hb =
      (synthesis (radius := refinedRadius (J := J))
        (fun i ↦ refinedMask_measurable (hβ i.1) i.2) (fun i ↦ hM i.1)
        (fun i ↦ refinedMask_bound (hb i.1) i.2)).comp
          (wideRefinement n J).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, wideSynthesis_apply]
  erw [synthesis_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  exact wideChannel_eq_refined (hβ j) (hM j) (hb j) (v j)

/-- The adjoint changes coordinates by the same genuine Hilbert equivalence
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideRefinement_adjoint_wideSynthesis
    (hβ : ∀ j, AEStronglyMeasurable (β j) (volume.restrict (wideBand n j.val)))
    (hM : ∀ j, 0 ≤ M j)
    (hb : ∀ j, ∀ᵐ η ∂volume.restrict (wideBand n j.val), ‖β j η‖ ≤ M j)
    (f : Output n) :
    wideRefinement n J ((wideSynthesis hβ hb).adjoint f) =
      (synthesis (radius := refinedRadius (J := J))
        (fun i ↦ refinedMask_measurable (hβ i.1) i.2) (fun i ↦ hM i.1)
        (fun i ↦ refinedMask_bound (hb i.1) i.2)).adjoint f := by
  rw [wideSynthesis_eq_refined hβ hM hb, ContinuousLinearMap.adjoint_comp]
  change wideRefinement n J
    (((wideRefinement n J : WideInput n J →L[ℂ] RefinedInput n J).adjoint)
      (_ : RefinedInput n J)) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact (wideRefinement n J).apply_symm_apply _

/-- Equality of the actual full output normals
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideSynthesis_normal_eq_refined
    (hβ : ∀ j, AEStronglyMeasurable (β j) (volume.restrict (wideBand n j.val)))
    (hM : ∀ j, 0 ≤ M j)
    (hb : ∀ j, ∀ᵐ η ∂volume.restrict (wideBand n j.val), ‖β j η‖ ≤ M j) :
    let S := synthesis (radius := refinedRadius (J := J))
      (fun i ↦ refinedMask_measurable (hβ i.1) i.2) (fun i ↦ hM i.1)
      (fun i ↦ refinedMask_bound (hb i.1) i.2)
    (wideSynthesis hβ hb).comp (wideSynthesis hβ hb).adjoint = S.comp S.adjoint := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro f
  change wideSynthesis hβ hb ((wideSynthesis hβ hb).adjoint f) = _
  have hs := congrArg (fun T : WideInput n J →L[ℂ] Output n ↦
    T ((wideSynthesis hβ hb).adjoint f)) (wideSynthesis_eq_refined hβ hM hb)
  rw [hs]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [wideRefinement_adjoint_wideSynthesis hβ hM hb]

/-- Equality of the grouped-prefix normals on the same full input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideSynthesis_prefix_normal_eq_refined
    (hβ : ∀ j, AEStronglyMeasurable (β j) (volume.restrict (wideBand n j.val)))
    (hM : ∀ j, 0 ≤ M j)
    (hb : ∀ j, ∀ᵐ η ∂volume.restrict (wideBand n j.val), ‖β j η‖ ≤ M j)
    (L : ℕ) :
    let S := synthesis (radius := refinedRadius (J := J))
      (fun i ↦ refinedMask_measurable (hβ i.1) i.2) (fun i ↦ hM i.1)
      (fun i ↦ refinedMask_bound (hb i.1) i.2)
    (wideSynthesis hβ hb).comp ((widePrefix n J L).comp (wideSynthesis hβ hb).adjoint) =
      S.comp ((refinedPrefix n J L).comp S.adjoint) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro f
  change wideSynthesis hβ hb (widePrefix n J L ((wideSynthesis hβ hb).adjoint f)) = _
  have hs := congrArg (fun T : WideInput n J →L[ℂ] Output n ↦
    T (widePrefix n J L ((wideSynthesis hβ hb).adjoint f))) (wideSynthesis_eq_refined hβ hM hb)
  rw [hs]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [wideRefinement_prefix, wideRefinement_adjoint_wideSynthesis hβ hM hb]

/-- Synthesis for the actually constructed smooth radial partition, with all
measurability and boundedness inputs discharged (`app:ch_waves:thm:individual`). -/
def radialWideSynthesis (n J : ℕ) : WideInput n J →L[ℂ] Output n :=
  wideSynthesis (fun j ↦ radialBand_complex_measurable n j.val)
    (fun j ↦ radialBand_complex_bound n j.val)

/-- Actual application to the constructed radial masks: refinement does not
change their synthesis (`app:ch_waves:thm:individual`). -/
theorem radialWideSynthesis_eq_refined (n J : ℕ) :
    radialWideSynthesis n J =
      (synthesis (radius := refinedRadius (J := J))
        (fun i ↦ refinedMask_measurable (radialBand_complex_measurable n i.1.val) i.2)
        (fun _ ↦ zero_le_one)
        (fun i ↦ refinedMask_bound (radialBand_complex_bound n i.1.val) i.2)).comp
          (wideRefinement n J).toContinuousLinearEquiv.toContinuousLinearMap :=
  wideSynthesis_eq_refined _ (fun _ ↦ zero_le_one) _

/-- The actual radial synthesis reassembles to the original smooth masks,
without any sharp indicator in its coefficient (`app:ch_waves:thm:individual`). -/
theorem radialWideSynthesis_coeFn (n J : ℕ) (v : WideInput n J) :
    radialWideSynthesis n J v =ᵐ[volume] fun η ↦
      ∑ j : Fin J, (Real.sqrt ‖η‖ : ℂ) * (radialBand n j.val η : ℂ) * v j η := by
  change wideSynthesis _ _ v =ᵐ[volume] _
  rw [wideSynthesis_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h : ∀ᵐ η ∂(volume : Measure (Euclidean (n - 1))), ∀ j : Fin J,
      (wideChannel (radialBand_complex_measurable n j.val)
        (radialBand_complex_bound n j.val) (v j)) η =
        (Real.sqrt ‖η‖ : ℂ) * (radialBand n j.val η : ℂ) * v j η :=
    Filter.eventually_all.mpr (fun j : Fin J ↦ radialWideChannel_coeFn n j.val (v j))
  filter_upwards [h] with η hη
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ ↦ hη j)

end JanetCartan.RawInputPartition
