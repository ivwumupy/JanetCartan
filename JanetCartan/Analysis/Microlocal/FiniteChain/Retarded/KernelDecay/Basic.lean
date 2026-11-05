module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Rescaling
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Regularity
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace

/-!
# Concrete normalized amplitudes for retarded decay

The normalization and compact-support bridge used to apply half-space integration
by parts in `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
The Boolean orientation selects the actual lower operator or its literal upper
adjoint; it does not denote a signed conjugate partner. Both Fourier measures and
their frequency Jacobian remain explicit.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize both covectors of the concrete amplitude, keeping the normal and
base variables fixed (`app:ch_regular:lem:finite-chain`). `upper = true` retains
the literal adjoint's scalar `-i` and exchanged weights. -/
def normalizedAmplitude (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℂ :=
  if upper then upperAmplitude α β mi mo r xi xo (x.1, x.2.1, ρ • x.2.2)
  else lowerAmplitude α β mi mo r xi xo (x.1, x.2.1, ρ • x.2.2)

/-- Select the lower phase or the literal reverse phase, retaining all input-base
equations (`app:ch_regular:lem:finite-chain`). -/
def literalPhase (upper : Bool) (xi xo : ℝ × E) : ℝ × TangentialVariables E → ℝ :=
  if upper then packedUpperPhase xi xo else packedPhase xi xo

/-- Smoothness after frequency normalization, for either literal orientation
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_normalizedAmplitude (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (xi xo : ℝ × E) :
    ContDiff ℝ ∞ (normalizedAmplitude upper ρ α β mi mo r xi xo) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
      (x.1, x.2.1, ρ • x.2.2)) := by fun_prop
  cases upper
  · exact (contDiff_lowerAmplitude α β mi mo r hα hβ hi ho hr xi xo).comp hc
  · exact (contDiff_upperAmplitude α β mi mo r hα hβ hi ho hr xi xo).comp hc

/-- The two literal phases are globally smooth
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_literalPhase (upper : Bool) (xi xo : ℝ × E) :
    ContDiff ℝ ∞ (literalPhase upper xi xo) := by
  cases upper
  · exact contDiff_packedPhase xi xo
  · exact contDiff_packedUpperPhase xi xo

/-- A common carrier constructed from the two weight supports and the two
normalized frequency supports (`app:ch_regular:lem:finite-chain`). In particular
the normal difference is bounded by the weight supports, independently of the
integration order. No compact support of `1 - mo` is asserted. -/
def amplitudeCarrier (Kα Kβ Ko Ki : Set (ℝ × E)) : Set (ℝ × TangentialVariables E) :=
  (fun p : (ℝ × E) × (ℝ × E) × (ℝ × E) × (ℝ × E) =>
    (p.1.1 - p.2.1.1, p.2.1, p.2.2)) '' (Kα ×ˢ Kβ ×ˢ Ko ×ˢ Ki)

omit [InnerProductSpace ℝ E] in
/-- Compact primitive carriers give a compact joint carrier for half-space
integration by parts (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_amplitudeCarrier {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hα : IsCompact Kα) (hβ : IsCompact Kβ) (ho : IsCompact Ko) (hi : IsCompact Ki) :
    IsCompact (amplitudeCarrier Kα Kβ Ko Ki) :=
  (hα.prod (hβ.prod (ho.prod hi))).image (by fun_prop)

/-- The actual normalized amplitudes have a common compact support, derived
from primitive weight and frequency support assumptions. The input and output
bases may vary without changing this carrier (`app:ch_regular:lem:finite-chain`). -/
theorem tsupport_normalizedAmplitude_subset (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hα : tsupport α ⊆ Kα) (hβ : tsupport β ⊆ Kβ)
    (hr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki) :
    tsupport (normalizedAmplitude upper ρ α β mi mo r xi xo) ⊆
      amplitudeCarrier Kα Kβ Ko Ki := by
  apply closure_minimal ?_ (isCompact_amplitudeCarrier hKα hKβ hKo hKi).isClosed
  intro x hx
  have hf : α (x.2.1.1 + x.1, x.2.1.2) ≠ 0 ∧ β x.2.1 ≠ 0 ∧
      r (ρ • x.2.2.1) ≠ 0 ∧ mi xi (ρ • x.2.2.2) ≠ 0 := by
    cases upper <;>
      (refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hz <;>
        simp [normalizedAmplitude, lowerAmplitude, upperAmplitude, hz] at hx)
  refine ⟨((x.2.1.1 + x.1, x.2.1.2), x.2.1, x.2.2),
    ⟨hα (subset_tsupport α hf.1), hβ (subset_tsupport β hf.2.1),
      hr (subset_tsupport _ hf.2.2.1), hi (subset_tsupport _ hf.2.2.2)⟩, ?_⟩
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance : (volume : Measure (ℝ × E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure E)
local instance : (volume : Measure ((ℝ × E) × (ℝ × E))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E)) (volume : Measure (ℝ × E))
local instance : (volume : Measure (TangentialVariables E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E))
    (volume : Measure ((ℝ × E) × (ℝ × E)))

/-- Exact conversion of the actual regularized Fourier kernels to the joint
half-space integral. Fubini follows from smoothness and the common compact
support. Both Fourier normalizations and the full two-frequency Jacobian are
retained (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem fourierKernel_eq_halfSpace (upper : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E)
    (ha : ContDiff ℝ ∞ (normalizedAmplitude upper ρ α β mi mo r xi xo))
    (hc : HasCompactSupport (normalizedAmplitude upper ρ α β mi mo r xi xo)) :
    (if upper then upperFourierKernel α β mi mo r xi xo
      else lowerFourierKernel α β mi mo r xi xo) =
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
        HalfSpace.halfSpaceOscillatoryIntegral volume ρ (literalPhase upper xi xo)
          (normalizedAmplitude upper ρ α β mi mo r xi xo) := by
  rw [HalfSpace.halfSpaceOscillatoryIntegral_eq_integral_slice
    (contDiff_literalPhase upper xi xo) ha hc]
  have hf (d : ℝ) : Integrable (fun z : TangentialVariables E =>
      Localization.phaseOscillation (ρ • literalPhase upper xi xo) (d, z) *
        normalizedAmplitude upper ρ α β mi mo r xi xo (d, z)) := by
    apply HalfSpace.integrable_slice hc tsupport_mul_subset_right
    have hF := (contDiff_literalPhase upper xi xo).continuous
    have hac := ha.continuous
    unfold Localization.phaseOscillation
    fun_prop
  have he (d : ℝ) :
      (∫ z : TangentialVariables E,
        Localization.phaseOscillation (ρ • literalPhase upper xi xo) (d, z) *
          normalizedAmplitude upper ρ α β mi mo r xi xo (d, z)) =
      ∫ b : ℝ × E, ∫ w : (ℝ × E) × (ℝ × E),
        Localization.phaseOscillation (ρ • literalPhase upper xi xo) (d, b, w) *
          normalizedAmplitude upper ρ α β mi mo r xi xo (d, b, w) :=
    integral_prod _ (hf d)
  simp_rw [he]
  cases upper
  · exact lowerFourierKernel_rescale α β mi mo r xi xo hρ
  · exact upperFourierKernel_rescale α β mi mo r xi xo hρ

end JanetCartan.FiniteChain.Retarded.KernelDecay
