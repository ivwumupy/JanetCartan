module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoundedSymbols
public import JanetCartan.Analysis.Fourier.Periodic

/-!
# Physical cutoff modulations

The actual multiplication operators `M_p`, `M_q` of
`app:ch_osc:lem:osc-amplitude`. A measurable map to the auxiliary torus allows
arbitrary fixed physical box scales. The Euclidean chart below uses unit-period
characters, hence the shared `2π` convention.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}

/-- The pointwise modulus bound for a physical Fourier character
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_mFourier_apply_le_one (k : Fin n → ℤ) (x : Torus n) :
    ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
  simpa only [UnitAddTorus.mFourier_norm] using (UnitAddTorus.mFourier k).norm_coe_le_norm x

/-- The bounded cutoff character used in `app:ch_osc:lem:osc-amplitude`. -/
def cutoffModulationSymbol (q : X → Torus n) (hq : Measurable q)
    (χ : X → ℂ) (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ x ∂μ, ‖χ x‖ ≤ 1)
    (k : Fin n → ℤ) : Lp ℂ ∞ μ :=
  boundedSymbol (fun x ↦ χ x * UnitAddTorus.mFourier k (q x))
    (hχ.mul ((UnitAddTorus.mFourier k).continuous.stronglyMeasurable.comp_measurable
      hq).aestronglyMeasurable) 1
    (hbound.mono fun x hx ↦ by
      rw [norm_mul]
      exact (mul_le_mul hx (norm_mFourier_apply_le_one k (q x))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-- The actual cutoff modulation in `app:ch_osc:lem:osc-amplitude`. -/
def cutoffModulation (q : X → Torus n) (hq : Measurable q)
    (χ : X → ℂ) (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ x ∂μ, ‖χ x‖ ≤ 1)
    (k : Fin n → ℤ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  multiplicationOperator (cutoffModulationSymbol q hq χ hχ hbound k)

/-- Physical cutoff modulations are contractions, uniformly in the mode and
box scale (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_cutoffModulation_le (q : X → Torus n) (hq : Measurable q)
    (χ : X → ℂ) (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ x ∂μ, ‖χ x‖ ≤ 1)
    (k : Fin n → ℤ) : ‖cutoffModulation q hq χ hχ hbound k‖ ≤ 1 :=
  (norm_multiplicationOperator_le _).trans (norm_boundedSymbol_le _ _ _ _ zero_le_one)

/-- Pointwise realization of the physical modulations in
`app:ch_osc:lem:osc-amplitude`. -/
theorem cutoffModulation_coeFn (q : X → Torus n) (hq : Measurable q)
    (χ : X → ℂ) (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ x ∂μ, ‖χ x‖ ≤ 1)
    (k : Fin n → ℤ) (f : Lp ℂ 2 μ) :
    cutoffModulation q hq χ hχ hbound k f =ᵐ[μ]
      fun x ↦ χ x * UnitAddTorus.mFourier k (q x) * f x := by
  filter_upwards [multiplicationOperator_coeFn (cutoffModulationSymbol q hq χ hχ hbound k) f,
    boundedSymbol_coeFn (fun x ↦ χ x * UnitAddTorus.mFourier k (q x)) _ 1 _] with x hx hs
  exact hx.trans (congrArg (fun z ↦ z * f x) hs)

/-- The quotient chart for a physical box with scale `ℓ`, used in
`app:ch_osc:lem:osc-amplitude`. Positive nonzero scales are chosen in applications. -/
def scaledTorusChart (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Torus n :=
  torusQuotient (ℓ⁻¹ • x)

/-- The physical box chart is measurable (`app:ch_osc:lem:osc-amplitude`). -/
theorem measurable_scaledTorusChart (ℓ : ℝ) : Measurable (scaledTorusChart (n := n) ℓ) := by
  apply Continuous.measurable
  unfold scaledTorusChart torusQuotient
  fun_prop

end JanetCartan.AmplitudeBound
