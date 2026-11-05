module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Channel

/-!
# Finite annular Hilbert synthesis

The actual complex operator behind `app:ch_waves:thm:individual`, on the shared
Lebesgue annular sum. The only analytic inputs are measurability and bounds of
the masks, to be supplied by the raw-input producer. The current-canonical,
raw-primary and simultaneous-sampling consumers must instantiate these inputs.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
namespace JanetCartan.RawInputHilbert
open RawInputRealization


variable {n : ℕ} {ι : Type*} [Fintype ι] {radius M : ι → ℝ}
  {β : ι → Euclidean (n - 1) → ℂ}

/-- Complex density synthesis on the same finite annular sum as the paper's
`X_K` (`app:ch_waves:thm:individual`). -/
def synthesis (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i) :
    Input n radius →L[ℂ] Output n :=
  ∑ i, (channel (hβ i) (hM i) (hb i)).comp (PiLp.proj 2 _ i)

/-- Coordinate formula for the constructed synthesis
(`app:ch_waves:thm:individual`). -/
theorem synthesis_apply
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (v : Input n radius) :
    synthesis hβ hM hb v = ∑ i, channel (hβ i) (hM i) (hb i) (v i) := by
  simp [synthesis, PiLp.proj_apply]

/-- AE identification with the literal density already used in the Fourier
and smooth-field constructions (`app:ch_waves:eq:B-bounds`). -/
theorem synthesis_coeFn
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (v : Input n radius) : synthesis hβ hM hb v =ᵐ[volume] density β v := by
  rw [synthesis_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  filter_upwards [eventuallyEq_sum (s := Finset.univ)
    (fun i _ ↦ channel_coeFn (hβ i) (hM i) (hb i) (v i))] with η hη
  simpa only [RawInputRealization.density, Finset.sum_apply] using hη

/-- The Hilbert norm estimate has no factor depending on the number of annuli
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_synthesis_le
    (hR : ∀ i, 0 ≤ radius i)
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i) :
    ‖synthesis hβ hM hb‖ ≤ Real.sqrt (∑ i, radius i * M i ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hcs : (∑ i, (Real.sqrt (radius i) * M i) * ‖v i‖) ≤
      Real.sqrt (∑ i, (Real.sqrt (radius i) * M i) ^ 2) * ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
    apply (Real.le_sqrt (Finset.sum_nonneg (fun i _ ↦
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i)) (norm_nonneg _))) (by positivity)).mpr
    rw [norm_input_sq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [mul_pow, Real.sq_sqrt (hR _)] at hcs
  rw [synthesis_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ ?_).trans hcs)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_channel_le (hβ i) (hM i) (hb i)) (norm_nonneg _))

/-- The genuine adjoint is the vector of the channel adjoints
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_synthesis
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i) :
    (synthesis hβ hM hb).adjoint =
      (PiLp.continuousLinearEquiv 2 ℂ (fun i ↦ AnnularL2 n (radius i))).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun i ↦ (channel (hβ i) (hM i) (hb i)).adjoint)) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.inner_apply, synthesis_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Adjoint coordinate, before taking a representative
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_synthesis_apply
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (f : Output n) (i : ι) :
    (synthesis hβ hM hb).adjoint f i = (channel (hβ i) (hM i) (hb i)).adjoint f := by
  rw [adjoint_synthesis]
  rfl

/-- Literal formula for each coordinate of the genuine Hilbert adjoint
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_synthesis_coeFn
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (f : Output n) (i : ι) :
    (synthesis hβ hM hb).adjoint f i =ᵐ[annularMeasure n (radius i)]
      fun η ↦ (Real.sqrt ‖η‖ : ℂ) * starRingEnd ℂ (β i η) * f η := by
  rw [adjoint_synthesis_apply]
  exact adjoint_channel_coeFn (hβ i) (hM i) (hb i) f

end JanetCartan.RawInputHilbert
