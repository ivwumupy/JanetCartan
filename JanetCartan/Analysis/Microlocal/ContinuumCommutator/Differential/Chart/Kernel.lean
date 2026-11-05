module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.ChartMeasure

/-!
# Literal kernels in the unit-torus chart

The measure step for `app:ch_background:eq:bg-commutator`. Source integration
uses normalized Haar measure on the unit torus and is proved equal to the
original Lebesgue integral. Frequency integration and its `2π` phase are unchanged.
The consumer is the compact-test transfer in `Differential.Chart`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The closed physical box used for both positions in
`app:ch_background:eq:bg-commutator`. -/
def chartBox (r : ℝ) : Set E := {x | ∀ i, |x i| ≤ r}

/-- The physical box lies in the normalized representative cell
(`app:ch_background:eq:bg-commutator`). -/
theorem chartBox_subset_cell {r : ℝ} (hr : r < 1 / 2) :
    chartBox (d := d) r ⊆ halfOpenCell d := by
  intro x hx i
  have hi := abs_le.mp (hx i)
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- Both positions of a nonzero full amplitude lie in the physical box
(`app:ch_background:eq:bg-commutator`). -/
theorem positions_mem_chartBox {r : ℝ} {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) {x y ξ : E}
    (h : b ξ (pairedPosition x y) ≠ 0) : x ∈ chartBox r ∧ y ∈ chartBox r := by
  have hp := hs ξ _ h
  constructor
  · intro i
    simpa [pairedPosition, i.isLt] using hp ⟨i.val, by omega⟩
  · intro i
    simpa [pairedPosition, show ¬i.val + d < d by omega] using hp ⟨i.val + d, by omega⟩

/-- Source-first Fourier integration on normalized unit-torus measure, with
literal Euclidean positions and frequency (`app:ch_background:eq:bg-commutator`). -/
def torusSourceTransform
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ) (u : Torus d → ℂ) (x ξ : E) : ℂ :=
  ∫ z : Torus d, Real.fourierChar (-⟪centeredTorusRepresentative z, ξ⟫) •
    (u z * b ξ (pairedPosition x (centeredTorusRepresentative z)))

/-- The literal chart operator. Frequency remains continuous Lebesgue frequency;
only the physical source and target use unit-torus charts
(`app:ch_background:eq:bg-commutator`). -/
def torusKernelOperator
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ) (u : Torus d → ℂ) : Torus d → ℂ :=
  fun z ↦ 𝓕⁻ (torusSourceTransform b u (centeredTorusRepresentative z))
    (centeredTorusRepresentative z)

/-- Exact source measure comparison, with no normalization factor
(`app:ch_background:eq:bg-commutator`). -/
theorem torusSourceTransform_eq {r : ℝ} (hr : r < 1 / 2)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : Torus d → ℂ) (x ξ : E) :
    torusSourceTransform b u x ξ =
      sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) (periodicLift u) x ξ := by
  unfold sourceAmplitudeTransform
  rw [Real.fourier_eq]
  have h := integral_representative_of_supported (chartBox_subset_cell hr)
    (fun y : E ↦ Real.fourierChar (-⟪y, ξ⟫) •
      (periodicLift u y * b ξ (pairedPosition x y))) (by
        intro y hy
        have hz : b ξ (pairedPosition x y) = 0 := by
          by_contra h
          exact hy (positions_mem_chartBox hs h).2
        simp [hz])
  simpa only [torusSourceTransform, periodicLift, Function.comp_apply,
    torusQuotient_centeredTorusRepresentative, smul_eq_mul] using h

/-- The chart operator is precisely periodization of the literal full-amplitude
Lebesgue operator (`app:ch_background:eq:bg-commutator`). -/
theorem torusKernelOperator_eq {r : ℝ} (hr : r < 1 / 2)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : Torus d → ℂ) :
    torusKernelOperator b u = amplitudePeriodization
      (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (periodicLift u)) := by
  funext z
  unfold torusKernelOperator amplitudePeriodization fullAmplitudeOperator
  rw [show torusSourceTransform b u (centeredTorusRepresentative z) =
    sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y))
      (periodicLift u) (centeredTorusRepresentative z) from
        funext (torusSourceTransform_eq hr b hs u _)]
  rfl

/-- Source agreement is required only where the amplitude is nonzero
(`app:ch_background:eq:bg-commutator`). -/
theorem fullAmplitudeOperator_congr_on_source {r : ℝ}
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) {u v : E → ℂ}
    (huv : EqOn u v (chartBox r)) :
    fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u =
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) v := by
  have he (x ξ : E) : (fun y ↦ u y • b ξ (pairedPosition x y)) =
      (fun y ↦ v y • b ξ (pairedPosition x y)) := by
    funext y
    by_cases h : b ξ (pairedPosition x y) = 0
    · simp [h]
    · rw [huv (positions_mem_chartBox hs h).2]
  funext x
  unfold fullAmplitudeOperator sourceAmplitudeTransform
  simp only [he]

/-- Output localization is a consequence of the actual amplitude support
(`app:ch_background:eq:bg-commutator`). -/
theorem fullAmplitudeOperator_supported {r : ℝ}
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : E → ℂ) :
    SupportedInCenteredBox r
      (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u) := by
  intro x hx
  by_contra h
  have hz (y ξ : E) : b ξ (pairedPosition x y) = 0 := by
    by_contra hb
    exact h (positions_mem_chartBox hs hb).1
  apply hx
  simp [fullAmplitudeOperator, sourceAmplitudeTransform, hz, Real.fourier_eq,
    Real.fourierInv_eq]

/-- The actual chart output vanishes off the quotient of the physical box
(`app:ch_background:eq:bg-commutator`). -/
theorem torusKernelOperator_supported {r : ℝ} (hr : r < 1 / 2)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : Torus d → ℂ)
    (z : Torus d) (hz : z ∉ torusChart (chartBox r)) : torusKernelOperator b u z = 0 := by
  rw [torusKernelOperator_eq hr b hs u]
  by_contra h
  exact hz (fullAmplitudeOperator_supported b hs (periodicLift u) _ h)

end JanetCartan.Pseudodifferential.DifferentialChart
