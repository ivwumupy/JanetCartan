module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrating the squared slice estimate

The Fubini step of `app:ch_osc:prop:osc-channel`, on the full product output
measure. The hypotheses are a slice energy estimate and time support; this
lemma does not itself assert an oscillatory estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace JanetCartan.SingleChannel

variable {Y V : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite ν]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The L² energy of an actual representative, used to pass between the
integral and operator versions of `app:ch_osc:prop:osc-channel`. -/
theorem integral_norm_sq_eq_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp V 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- The same energy identity for a specified L² representative
(`app:ch_osc:prop:osc-channel`). -/
theorem integral_norm_sq_eq_toLp_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → V} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← integral_norm_sq_eq_norm_sq]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun v ↦ ‖v‖ ^ 2)).symm

omit [InnerProductSpace ℂ V] in
/-- Integrating a uniformly bounded slice energy over a bounded interval
proves the full-space energy estimate in `app:ch_osc:prop:osc-channel`.
The output is zero outside that interval; its L² space is not restricted to it. -/
theorem integral_norm_sq_le_of_slice_bound {a b B : ℝ} (hab : a ≤ b)
    {g : ℝ × Y → V} (hg : MemLp g 2 (volume.prod ν))
    (hsupport : ∀ t ∉ Ioo a b, ∀ y, g (t, y) = 0)
    (hbound : ∀ t ∈ Ioo a b, (∫ y, ‖g (t, y)‖ ^ 2 ∂ν) ≤ B) :
    (∫ x, ‖g x‖ ^ 2 ∂volume.prod ν) ≤ (b - a) * B := by
  have hi := hg.integrable_norm_pow (by norm_num)
  rw [integral_prod _ hi]
  have hEq : (fun t ↦ ∫ y, ‖g (t, y)‖ ^ 2 ∂ν) =
      (Ioo a b).indicator (fun t ↦ ∫ y, ‖g (t, y)‖ ^ 2 ∂ν) := by
    funext t
    by_cases ht : t ∈ Ioo a b
    · simp [ht]
    · simp [ht, hsupport t ht]
  rw [hEq, integral_indicator measurableSet_Ioo]
  calc
    (∫ t in Ioo a b, ∫ y, ‖g (t, y)‖ ^ 2 ∂ν) ≤ ∫ _t in Ioo a b, B := by
      apply integral_mono_ae hi.integral_prod_left.integrableOn (integrable_const B)
      exact (ae_restrict_mem measurableSet_Ioo).mono (fun t ht ↦ hbound t ht)
    _ = (b - a) * B := by simp [sub_nonneg.mpr hab]

end JanetCartan.SingleChannel
