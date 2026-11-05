module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Projections

/-!
# Literal output normal of the annular synthesis

The normal is a nonnegative multiplication operator on full Lebesgue L², with
annular indicators present. This supplies the raw-input part of
`app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
namespace JanetCartan.RawInputHilbert
open RawInputRealization

variable {n : ℕ} {R M : ℝ} {β : Euclidean (n - 1) → ℂ}

/-- A single channel normal is multiplication by the actual annular weight
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem channel_normal_coeFn
    (hβ : AEStronglyMeasurable β (annularMeasure n R))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M) (f : Output n) :
    channel hβ hM hb ((channel hβ hM hb).adjoint f) =ᵐ[volume]
      fun η ↦ (annulus n R).indicator (fun η ↦ (‖η‖ * ‖β η‖ ^ 2 : ℝ)) η * f η := by
  have ha := (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_annulus n R)).mp
    (adjoint_channel_coeFn hβ hM hb f)
  filter_upwards [channel_coeFn hβ hM hb ((channel hβ hM hb).adjoint f), ha] with η he ha
  rw [he]
  by_cases hη : η ∈ annulus n R
  · simp only [channelDensity, Set.indicator_of_mem hη] at *
    rw [ha]
    calc
      _ = ((Real.sqrt ‖η‖ : ℂ) ^ 2) * (β η * starRingEnd ℂ (β η)) * f η := by ring
      _ = _ := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _), Complex.mul_conj']
        push_cast
        rfl
  · simp [channelDensity, hη]

variable {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- The literal multiplier of a selected output normal
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def normalWeight (β : ι → Euclidean (n - 1) → ℂ) (s : Finset ι)
    (η : Euclidean (n - 1)) : ℝ :=
  ‖η‖ * ∑ i ∈ s, (annulus n (radius i)).indicator (fun η ↦ ‖β i η‖ ^ 2) η

omit [Fintype ι] in
/-- Nonnegativity of the literal output multiplier
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normalWeight_nonneg (β : ι → Euclidean (n - 1) → ℂ) (s : Finset ι)
    (η : Euclidean (n - 1)) : 0 ≤ normalWeight (radius := radius) β s η := by
  classical
  unfold normalWeight
  apply mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦ ?_)
  exact Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _

/-- Exact multiplier for every prefix normal on the fixed output space
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem synthesis_prefix_normal_coeFn
    {M : ι → ℝ} {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (s : Finset ι) (f : Output n) :
    synthesis hβ hM hb (coordinateProjection s ((synthesis hβ hM hb).adjoint f)) =ᵐ[volume]
      fun η ↦ (normalWeight (radius := radius) β s η : ℂ) * f η := by
  classical
  have he := congrArg (fun T : Output n →L[ℂ] Output n ↦ T f)
    (synthesis_coordinateProjection_adjoint hβ hM hb s)
  simp only [ContinuousLinearMap.comp_apply, sum_apply] at he
  rw [he]
  refine (Lp.coeFn_finsetSum s _).trans ?_
  have ha := eventuallyEq_sum (s := s) (fun i _ ↦ channel_normal_coeFn (hβ i) (hM i) (hb i) f)
  refine ha.trans (Filter.Eventually.of_forall fun η ↦ ?_)
  simp only [Finset.sum_apply, normalWeight, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hη : η ∈ annulus n (radius i) <;> simp [hη]

/-- The full output normal has multiplier `|η| ∑ᵢ 1_annulusᵢ |βᵢ|²`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem synthesis_normal_coeFn
    {M : ι → ℝ} {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (f : Output n) :
    synthesis hβ hM hb ((synthesis hβ hM hb).adjoint f) =ᵐ[volume]
      fun η ↦ (normalWeight (radius := radius) β Finset.univ η : ℂ) * f η := by
  have hp : ∀ v : Input n radius, coordinateProjection Finset.univ v = v := by
    classical
    intro v
    apply PiLp.ext
    intro i
    simp [coordinateProjection_apply]
  simpa only [hp] using synthesis_prefix_normal_coeFn hβ hM hb Finset.univ f

end JanetCartan.RawInputHilbert
