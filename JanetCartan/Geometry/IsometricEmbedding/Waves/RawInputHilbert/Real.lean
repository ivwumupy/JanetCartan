module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Normal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Dyadic

/-!
# Both real quadratures of annular synthesis

The real operator in `app:ch_waves:thm:individual` is obtained only by restricting
scalars of the constructed complex operator. Its real adjoint is the same map
as the complex adjoint. No real-part projection discards the second quadrature.
-/

@[expose] public noncomputable section

open MeasureTheory
namespace JanetCartan.RawInputHilbert
open RawInputRealization

private theorem l2_real_inner_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : Lp ℂ 2 μ) : inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

private theorem input_real_inner_eq {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}
    (v w : Input n radius) : inner ℝ v w = (inner ℂ v w).re := by
  simp only [PiLp.inner_apply, l2_real_inner_eq, Complex.re_sum]

variable {n : ℕ} {ι : Type*} [Fintype ι] {radius M : ι → ℝ}
  {β : ι → Euclidean (n - 1) → ℂ}

/-- The actual real raw-input synthesis, retaining both quadratures
(`app:ch_waves:thm:individual`). -/
def realSynthesis
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i) :
    Input n radius →L[ℝ] Output n := (synthesis hβ hM hb).restrictScalars ℝ

/-- Scalar restriction preserves the actual synthesis bound
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_realSynthesis_le
    (hR : ∀ i, 0 ≤ radius i)
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i) :
    ‖realSynthesis hβ hM hb‖ ≤ Real.sqrt (∑ i, radius i * M i ^ 2) := by
  rw [realSynthesis, ContinuousLinearMap.norm_restrictScalars]
  exact norm_synthesis_le hR hβ hM hb

/-- The real adjoint is precisely the restriction of the complex adjoint
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_realSynthesis
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i) :
    (realSynthesis hβ hM hb).adjoint = (synthesis hβ hM hb).adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f v
  change inner ℝ ((synthesis hβ hM hb).adjoint f) v = inner ℝ f (synthesis hβ hM hb v)
  rw [input_real_inner_eq, l2_real_inner_eq, ContinuousLinearMap.adjoint_inner_left]

/-- Real coordinate projections retain the complex channels as complete pairs
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_realCoordinateProjection (s : Finset ι) :
    ((coordinateProjection (n := n) (radius := radius) s).restrictScalars ℝ).adjoint =
      (coordinateProjection s).restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  change inner ℝ (coordinateProjection s v) w = inner ℝ v (coordinateProjection s w)
  rw [input_real_inner_eq, input_real_inner_eq]
  congr 1
  conv_lhs => rw [← adjoint_coordinateProjection s]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Scalar restriction preserves the prefix contraction bound
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_realCoordinateProjection_le (s : Finset ι) :
    ‖(coordinateProjection (n := n) (radius := radius) s).restrictScalars ℝ‖ ≤ 1 := by
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact norm_coordinateProjection_le s

/-- The real prefix normal is exactly the sum of the same channel normals
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem realSynthesis_coordinateProjection_adjoint
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (s : Finset ι) :
    (realSynthesis hβ hM hb).comp (((coordinateProjection s).restrictScalars ℝ).comp
      (realSynthesis hβ hM hb).adjoint) =
      (∑ i ∈ s, (channel (hβ i) (hM i) (hb i)).comp
        (channel (hβ i) (hM i) (hb i)).adjoint).restrictScalars ℝ := by
  rw [adjoint_realSynthesis]
  exact congrArg (fun T : Output n →L[ℂ] Output n ↦ T.restrictScalars ℝ)
    (synthesis_coordinateProjection_adjoint hβ hM hb s)

/-- The real prefix normal has the same explicit annular multiplier
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem realSynthesis_prefix_normal_coeFn
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (s : Finset ι) (f : Output n) :
    realSynthesis hβ hM hb ((coordinateProjection s).restrictScalars ℝ
      ((realSynthesis hβ hM hb).adjoint f)) =ᵐ[volume]
      fun η ↦ (normalWeight (radius := radius) β s η : ℂ) * f η := by
  rw [adjoint_realSynthesis]
  exact synthesis_prefix_normal_coeFn hβ hM hb s f

/-- The same literal multiplier describes the real normal, with both
quadratures present (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem realSynthesis_normal_coeFn
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (f : Output n) :
    realSynthesis hβ hM hb ((realSynthesis hβ hM hb).adjoint f) =ᵐ[volume]
      fun η ↦ (normalWeight (radius := radius) β Finset.univ η : ℂ) * f η := by
  rw [adjoint_realSynthesis]
  exact synthesis_normal_coeFn hβ hM hb f

end JanetCartan.RawInputHilbert
