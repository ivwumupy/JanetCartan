module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint.Amplitude
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullScalarKernel.Integrability
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Adjoint

/-!
# The literal compact-frequency adjoint

For `app:ch_regular_base:thm:actual-calculus` (2)–(3), the adjoint of the
compact-frequency realization is obtained by conjugating and exchanging the
physical positions of the full amplitude. The kernel below retains all masks
and the `2π` phase convention. Fubini derives its integral realization.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology RealInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The literal frequency-integrated kernel for
`app:ch_regular_base:thm:actual-calculus` (2)–(3). -/
def compactFrequencyAmplitudeKernel (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ρ : ℝ) (x y : E) : ℂ :=
  ∫ ξ in Metric.closedBall 0 ρ,
    Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
      b ξ (pairedPosition x y)

/-- Joint continuity of the literal compact-frequency kernel
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem continuous_compactFrequencyAmplitudeKernel
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : Continuous (Function.uncurry b)) (ρ : ℝ) :
    Continuous (Function.uncurry (compactFrequencyAmplitudeKernel b ρ)) := by
  apply continuous_parametric_integral_of_continuous (s := Metric.closedBall 0 ρ)
    (hs := isCompact_closedBall 0 ρ)
  have ha : Continuous (fun p : (E × E) × E ↦ b p.2 (pairedPosition p.1.1 p.1.2)) :=
    hb.comp (continuous_snd.prodMk (continuous_pairedPosition.comp continuous_fst))
  exact (by fun_prop : Continuous (fun p : (E × E) × E ↦
    Complex.exp (↑(2 * Real.pi * ⟪p.1.1 - p.1.2, p.2⟫) * Complex.I))).mul ha

/-- The full compact-frequency kernel has compact support in both physical
positions (`app:ch_regular_base:thm:actual-calculus`). -/
theorem hasCompactSupport_compactFrequencyAmplitudeKernel
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {R : ℝ}
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (ρ : ℝ) :
    HasCompactSupport (Function.uncurry (compactFrequencyAmplitudeKernel b ρ)) := by
  let ℓ := amplitudeBoxScale R
  have hc := hasCompactSupport_boxCellCutoff (d := d) (amplitudeBoxScale_pos R).ne'
  apply HasCompactSupport.intro (hc.prod hc)
  rintro ⟨x, y⟩ hxy
  have hz : ∀ ξ, b ξ (pairedPosition x y) = 0 := by
    intro ξ
    rw [← boxCellCutoff_boxAmplitudePeriodization_eq (amplitudeBoxScale_pos R)
      (div_amplitudeBoxScale_lt R) (hs ξ) x y]
    by_cases hx : x ∈ tsupport (boxCellCutoff (d := d) ℓ)
    · have hy : y ∉ tsupport (boxCellCutoff (d := d) ℓ) := fun hy ↦ hxy ⟨hx, hy⟩
      simp [image_eq_zero_of_notMem_tsupport hy, ℓ]
    · simp [image_eq_zero_of_notMem_tsupport hx, ℓ]
  simp [Function.uncurry, compactFrequencyAmplitudeKernel, hz]

/-- Reversing the full amplitude reverses and conjugates the literal kernel,
with the same frequency ball (`app:ch_regular_base:thm:actual-calculus`). -/
theorem compactFrequencyAmplitudeKernel_adjointAmplitude
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ) (ρ : ℝ) (x y : E) :
    compactFrequencyAmplitudeKernel (adjointAmplitude b) ρ x y =
      star (compactFrequencyAmplitudeKernel b ρ y x) := by
  unfold compactFrequencyAmplitudeKernel
  simp only [Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [adjointAmplitude_pairedPosition, map_mul, starRingEnd_apply]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [inner_sub_left, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- Fubini identifies the frequency-first construction with integration
against the literal physical kernel (`app:ch_regular_base:thm:actual-calculus`). -/
theorem boxScalarAmplitudeKernel_eq_compactFrequencyAmplitudeKernel
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) {R : ℝ}
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A) (ρ : ℝ) (f : Lp (α := E) ℂ 2) (x : E) :
    boxScalarAmplitudeKernel b ρ f x =
      ∫ y, compactFrequencyAmplitudeKernel b ρ x y * f y := by
  unfold boxScalarAmplitudeKernel
  rw [integral_integral_swap (integrable_boxScalarAmplitudeKernel_prod b hb
    (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs A hzero ρ f x)]
  simp only [compactFrequencyAmplitudeKernel, integral_mul_const]

section Realization

variable (hd : 0 < d) (R : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hbound : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)

/-- The existing compact-frequency operator at the canonical auxiliary scale
(`app:ch_regular_base:thm:actual-calculus`). -/
def twoPositionCompactFrequencyL2Operator (ρ : ℝ) :
    Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  boxCompactFrequencyAmplitudeOperator b hb.continuous.stronglyMeasurable hd
    (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) A hbound.norm_le hbound.pure_le ρ

/-- The bounded compact-frequency realization acts by its literal physical
kernel on every L² input (`app:ch_regular_base:thm:actual-calculus`). -/
theorem twoPositionCompactFrequencyL2Operator_ae_kernel
    (ρ : ℝ) (f : Lp (α := E) ℂ 2) :
    twoPositionCompactFrequencyL2Operator hd R b hb hs A hbound ρ f =ᵐ[volume]
      fun x ↦ ∫ y, compactFrequencyAmplitudeKernel b ρ x y * f y := by
  have h := boxCompactFrequencyAmplitudeOperator_ae_kernel b
    hb.continuous.stronglyMeasurable hd (amplitudeBoxScale_pos R)
    (div_amplitudeBoxScale_lt R) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) A
    hbound.norm_le hbound.pure_le ρ f
  filter_upwards [h] with x hx
  exact hx.trans (boxScalarAmplitudeKernel_eq_compactFrequencyAmplitudeKernel b
    hb.continuous.stronglyMeasurable hs A hbound.norm_le ρ f x)

/-- The actual Hilbert adjoint is the compact-frequency realization of the
reversed conjugate full amplitude, at every real radius. All support and
derivative-budget premises are derived with the same `R` and `A`
(`app:ch_regular_base:thm:actual-calculus` (2)–(3)). -/
theorem twoPositionCompactFrequencyL2Operator_adjoint (ρ : ℝ) :
    (twoPositionCompactFrequencyL2Operator hd R b hb hs A hbound ρ).adjoint =
      twoPositionCompactFrequencyL2Operator hd R (adjointAmplitude b)
        (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
        (hasAmplitudeDerivativeBound_adjointAmplitude
          (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) ρ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have h := adjoint_eq_integral_of_compactKernel
    (continuous_compactFrequencyAmplitudeKernel hb.continuous ρ)
    (hasCompactSupport_compactFrequencyAmplitudeKernel hs ρ)
    (twoPositionCompactFrequencyL2Operator hd R b hb hs A hbound ρ)
    (twoPositionCompactFrequencyL2Operator_ae_kernel hd R b hb hs A hbound ρ) f
  have h' := twoPositionCompactFrequencyL2Operator_ae_kernel hd R (adjointAmplitude b)
    (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
    (hasAmplitudeDerivativeBound_adjointAmplitude
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) ρ f
  exact h.trans (by simpa only [compactFrequencyAmplitudeKernel_adjointAmplitude] using h'.symm)

end Realization
end JanetCartan.Pseudodifferential
