module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Restriction
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# Bounded measurable complex multiplication

The local factor in the annular synthesis of `app:ch_waves:thm:individual`.
The conjugate multiplier is proved to be the Hilbert adjoint, for the normal
identity `app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.RawInputHilbert

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {a : α → ℂ} {C : ℝ}

/-- Actual multiplication on complex L² from an almost-everywhere bound;
used for `app:ch_waves:eq:B-bounds`. -/
def boundedMultiplier (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  AmplitudeBound.multiplicationOperator ((memLp_top_of_bound ha C hb).toLp a)

/-- Literal representative of the bounded multiplier in
`app:ch_waves:eq:B-bounds`. -/
theorem boundedMultiplier_coeFn (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : Lp ℂ 2 μ) :
    boundedMultiplier ha hb f =ᵐ[μ] fun x ↦ a x * f x := by
  filter_upwards [AmplitudeBound.multiplicationOperator_coeFn
    ((memLp_top_of_bound ha C hb).toLp a) f,
    MemLp.coeFn_toLp (memLp_top_of_bound ha C hb)] with x h₁ h₂
  exact h₁.trans (congrArg (fun z ↦ z * f x) h₂)

/-- Operator bound for the actual multiplier (`app:ch_waves:eq:B-bounds`). -/
theorem norm_boundedMultiplier_le (ha : AEStronglyMeasurable a μ)
    (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖boundedMultiplier ha hb‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMultiplier_coeFn ha hb f, hb] with x hx hxC
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hxC (norm_nonneg _)

/-- Conjugating a bounded coefficient preserves its bound
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem conj_bound (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖starRingEnd ℂ (a x)‖ ≤ C := by
  simpa using hb

/-- Complex adjoint equals multiplication by the conjugate coefficient
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_boundedMultiplier (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    (boundedMultiplier ha hb).adjoint =
      boundedMultiplier ha.star (conj_bound hb) := by
  rw [← ContinuousLinearMap.adjoint_adjoint
    (boundedMultiplier ha.star (conj_bound hb))]
  congr 1
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_coeFn ha hb f,
    boundedMultiplier_coeFn ha.star (conj_bound hb) g] with x hf hg
  simp only [hf, hg, RCLike.inner_apply, map_mul, Pi.star_apply, starRingEnd_apply]
  ring

end JanetCartan.RawInputHilbert
