module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullScalarKernel
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel

/-!
# Two-position amplitude estimates from the manuscript hypotheses

The scalar and normal conclusions of `app:ch_osc:lem:osc-amplitude` in
`paper.tex`, including literal kernels and the unbounded-frequency limit.
Ordered coordinate derivatives express the total multi-index budget. All
coefficient, periodization, integrability and adjoint premises are discharged.
The Fourier convention is the unit-period `2π` convention of the project.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace JanetCartan.AmplitudeBound

/-- The physical derivative hypothesis through total order `N` in
`app:ch_osc:lem:osc-amplitude`. The empty list includes order zero. -/
def HasAmplitudeDerivativeBound {X : Type*} {n : ℕ}
    (b : X → EuclideanSpace ℝ (Fin n) → ℂ) (N : ℕ) (A : ℝ) : Prop :=
  ∀ ξ is, is.length ≤ N → ∀ z, ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A

/-- Extract order zero from the manuscript's derivative budget
(`app:ch_osc:lem:osc-amplitude`). -/
theorem HasAmplitudeDerivativeBound.norm_le {X : Type*} {n N : ℕ}
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ} {A : ℝ}
    (h : HasAmplitudeDerivativeBound b N A) (ξ : X) (z : EuclideanSpace ℝ (Fin n)) :
    ‖b ξ z‖ ≤ A := h ξ [] (Nat.zero_le N) z

/-- The pure top derivatives needed for Fourier summability follow from the
full manuscript budget (`app:ch_osc:lem:osc-amplitude`). -/
theorem HasAmplitudeDerivativeBound.pure_le {X : Type*} {n N : ℕ}
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ} {A : ℝ}
    (h : HasAmplitudeDerivativeBound b N A) (ξ : X) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖euclideanCoordinateDerivList (List.replicate N i) (b ξ) z‖ ≤ A :=
  h ξ _ (by simp) z

/-- A larger torus chosen solely from the fixed physical box, for
`app:ch_osc:lem:osc-amplitude`. -/
def amplitudeBoxScale (R : ℝ) : ℝ := 4 * (|R| + 1)

/-- The chosen torus has positive scale (`app:ch_osc:lem:osc-amplitude`). -/
theorem amplitudeBoxScale_pos (R : ℝ) : 0 < amplitudeBoxScale R := by
  unfold amplitudeBoxScale
  positivity

/-- The physical box lies strictly inside the larger torus cell
(`app:ch_osc:lem:osc-amplitude`). -/
theorem div_amplitudeBoxScale_lt (R : ℝ) : R / amplitudeBoxScale R < 1 / 2 := by
  rw [div_lt_iff₀ (amplitudeBoxScale_pos R)]
  unfold amplitudeBoxScale
  have := le_abs_self R
  have := abs_nonneg R
  linarith

/-- The constant in `app:ch_osc:lem:osc-amplitude`, depending only on the
physical box and dimension, independently of frequency support. -/
def fixedBoxAmplitudeConstant (d : ℕ) (R : ℝ) : ℝ :=
  boxAmplitudeConstant d (amplitudeBoxScale R)

/-- Nonnegativity of the fixed-box estimate constant
(`app:ch_osc:lem:osc-amplitude`). -/
theorem fixedBoxAmplitudeConstant_nonneg (d : ℕ) (R : ℝ) :
    0 ≤ fixedBoxAmplitudeConstant d R :=
  mul_nonneg (mul_nonneg (coefficientSumConstant_nonneg d)
    (smoothCoefficientConstant_pos d).le)
    (zero_le_one.trans (one_le_boxDerivativeFactor d _))

/-- Scalar assertion of `app:ch_osc:lem:osc-amplitude`. The bounded operator
is the strong and tempered-distribution limit of the original compact-frequency
integrals, whose bounds are uniform in the cutoff radius. No frequency support
or kernel reconstruction premise is assumed. -/
theorem exists_twoPositionAmplitudeOperator {d : ℕ} (hd : 0 < d) (R : ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hbound : HasAmplitudeDerivativeBound b (2 * (d + 1)) A) :
    ∃ (B : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ]
          Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
      (Bρ : ℝ → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ]
          Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2),
      ‖B‖ ≤ fixedBoxAmplitudeConstant d R * A ∧
      (∀ ρ, ‖Bρ ρ‖ ≤ fixedBoxAmplitudeConstant d R * A) ∧
      (∀ ρ f, Bρ ρ f =ᵐ[volume] boxScalarAmplitudeKernel b ρ f) ∧
      (∀ f, Tendsto (fun ρ ↦ Bρ ρ f) atTop (𝓝 (B f))) ∧
      (∀ f, Tendsto (fun ρ ↦ Lp.toTemperedDistribution (Bρ ρ f)) atTop
        (𝓝 (Lp.toTemperedDistribution (B f)))) := by
  have hm := hb.continuous.stronglyMeasurable
  have hf (ξ) : ContDiff ℝ ∞ (b ξ) := hb.comp (contDiff_const.prodMk contDiff_id)
  let B := boxScalarAmplitudeOperator b hm hd (amplitudeBoxScale_pos R)
    (div_amplitudeBoxScale_lt R) hs hf A hbound.norm_le hbound.pure_le
  let Bρ := boxCompactFrequencyAmplitudeOperator b hm hd (amplitudeBoxScale_pos R)
    (div_amplitudeBoxScale_lt R) hs hf A hbound.norm_le hbound.pure_le
  have hlim (f) : Tendsto (fun ρ ↦ Bρ ρ f) atTop (𝓝 (B f)) :=
    tendsto_boxCompactFrequencyAmplitudeOperator b hm hd (amplitudeBoxScale_pos R)
      (div_amplitudeBoxScale_lt R) hs hf A hbound.norm_le hbound.pure_le f
  refine ⟨B, Bρ, ?_, ?_, ?_, hlim, ?_⟩
  · exact norm_boxScalarAmplitudeOperator_le b hm hd (amplitudeBoxScale_pos R)
      (div_amplitudeBoxScale_lt R) hs hf A hbound.norm_le hbound.pure_le
  · exact fun ρ ↦ norm_boxCompactFrequencyAmplitudeOperator_le b hm hd
      (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs hf A
      hbound.norm_le hbound.pure_le ρ
  · exact fun ρ f ↦ boxCompactFrequencyAmplitudeOperator_ae_kernel b hm hd
      (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs hf A
      hbound.norm_le hbound.pure_le ρ f
  · intro f
    exact (Lp.toTemperedDistributionCLM ℂ
      (volume : Measure (EuclideanSpace ℝ (Fin d))) 2).continuous.continuousAt.tendsto.comp
        (hlim f)

/-- Normal assertion of `app:ch_osc:lem:osc-amplitude`, with the literal
kernel of `app:ch_osc:eq:two-position-normal-bound`. Only the given input-kernel
identity is assumed; the actual adjoint and Fourier/integral interchanges have
been proved. Only measurability in the parameter and smoothness in the physical
variables are required for `c`. The constant depends solely on dimension and
physical box. -/
theorem exists_twoPositionNormalOperator {d m : ℕ} (hd : 0 < d) (R : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin m))} (hD : MeasurableSet D)
    (t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hts : HasCompactSupport (Function.uncurry t))
    (T : Lp ℂ 2 (volume.restrict D) →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hT : ∀ h, T h =ᵐ[volume] fun x ↦ ∫ u, t x u * h u ∂volume.restrict D)
    (c : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hc : StronglyMeasurable (Function.uncurry c))
    (hf : ∀ u, ContDiff ℝ ∞ (c u))
    (hs : ∀ u, SupportedInCenteredBox R (c u)) (A : ℝ)
    (hbound : HasAmplitudeDerivativeBound c (2 * (d + 1)) A)
    (g : Lp ℂ ∞ (volume.restrict D)) :
    ∃ N : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ]
        Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2,
      ‖N‖ ≤ fixedBoxAmplitudeConstant d R * A * ‖T‖ ^ 2 * ‖g‖ ∧
      ∀ f, N f =ᵐ[volume] fullNormalAmplitudeKernel (μ := volume.restrict D) t c g f := by
  have hA : 0 ≤ A := (norm_nonneg (c 0 0)).trans (hbound.norm_le 0 0)
  refine ⟨boxNormalAmplitudeOperator c hc hd (amplitudeBoxScale_pos R)
    (div_amplitudeBoxScale_lt R) hs hf A hA hbound.norm_le hbound.pure_le T g, ?_, ?_⟩
  · exact norm_boxNormalAmplitudeOperator_le c hc hd (amplitudeBoxScale_pos R)
      (div_amplitudeBoxScale_lt R) hs hf A hA hbound.norm_le hbound.pure_le T g
  · exact fun f ↦ boxNormalAmplitudeOperator_ae_kernel hD t ht hts T hT c hc hd
      (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs hf A hA
      hbound.norm_le hbound.pure_le g f

end JanetCartan.AmplitudeBound
