module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Basic
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact normal coordinates for the literal fiber integrals

The substitutions below have absolute Jacobian one. They retain the fixed
positive input buffers and the transverse delta in
`app:ch_regular:lem:finite-chain`, “Retarded and signed factors”.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {Y : Type*}

/-- The lower fiber kernel in the nonnegative difference variable `d = t-s`
(`app:ch_regular:lem:finite-chain`). This is a measure-preserving substitution,
valid also under the Bochner undefined-integral convention. -/
theorem integral_lowerKernel_eq_normal (α β : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (t : ℝ) (y : Y) :
    (∫ s, lowerKernel α β t s y * f (s,y)) =
      ∫ d in Ici (0 : ℝ), (α (t,y) : ℂ) * (β (t-d,y) : ℂ) * f (t-d,y) := by
  rw [← integral_sub_left_eq_self (fun s => lowerKernel α β t s y * f (s,y)) volume t]
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [] with d
  by_cases hd : 0 ≤ d
  · simp [lowerKernel, Set.indicator_of_mem, hd, sub_le_self t hd]
  · have hdt : ¬ t-d ≤ t := by linarith
    simp [lowerKernel, hd, hdt]

/-- The upper fiber kernel uses `d = s-t`, with the transverse coordinate
unchanged (`app:ch_regular:lem:finite-chain`). -/
theorem integral_upperKernel_eq_normal (α β : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (t : ℝ) (y : Y) :
    (∫ s, upperKernel α β t s y * f (s,y)) =
      ∫ d in Ici (0 : ℝ), (β (t,y) : ℂ) * (α (t+d,y) : ℂ) * f (t+d,y) := by
  rw [← integral_add_left_eq_self (fun s => upperKernel α β t s y * f (s,y)) t]
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [] with d
  by_cases hd : 0 ≤ d
  · simp [upperKernel, hd, le_add_of_nonneg_right hd]
  · have hdt : ¬ t ≤ t+d := by linarith
    simp [upperKernel, hd, hdt]

/-- The actual lower operator, including its scalar `i`, in half-space
coordinates. The strictly positive fixed input buffer is explicit
(`app:ch_regular:lem:finite-chain`). -/
theorem imaginary_lower_eq_normal (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hβ : ∀ s y, s ≤ a+ε → β (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) (ht : a ≤ t) :
    Complex.I * JanetCartan.Retarded.lower a β α f (t,y) =
      ∫ d in Ici (0 : ℝ), Complex.I * (α (t,y) : ℂ) *
        (β (t-d,y) : ℂ) * f (t-d,y) := by
  rw [lower_eq_integral_kernel a ε hε α β hβ f t y ht,
    integral_lowerKernel_eq_normal, ← integral_const_mul]
  simp only [mul_assoc]

/-- The actual literal adjoint has scalar `-i`, exchanged weights, and
reversed translation. The upper input buffer belongs to `α`
(`app:ch_regular:lem:finite-chain`). -/
theorem imaginary_upper_eq_normal (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hα : ∀ s y, b-ε ≤ s → α (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) (ht : t ≤ b) :
    -Complex.I * JanetCartan.Retarded.upper b β α f (t,y) =
      ∫ d in Ici (0 : ℝ), -Complex.I * (β (t,y) : ℂ) *
        (α (t+d,y) : ℂ) * f (t+d,y) := by
  rw [upper_eq_integral_kernel b ε hε α β hα f t y ht,
    integral_upperKernel_eq_normal, ← integral_const_mul]
  simp only [mul_assoc]

/-- Conjugating the lower scalar and swapping the times gives the literal
upper kernel, including the minus sign (`app:ch_regular:lem:finite-chain`). -/
theorem imaginary_upperKernel_eq_conj_swap (α β : ℝ × Y → ℝ)
    (t s : ℝ) (y : Y) :
    -Complex.I * upperKernel α β t s y = conj (Complex.I * lowerKernel α β s t y) := by
  rw [map_mul, Complex.conj_I, upperKernel_eq_conj_swap]

/-- The positive lower input buffer also kills the reversed primitive below
the fixed endpoint. Thus the normal-coordinate identity holds at every output,
without an extra output-support premise (`app:ch_regular:lem:finite-chain`). -/
theorem imaginary_lower_eq_normal_of_input_buffer (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hβ : ∀ s y, s ≤ a+ε → β (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) :
    Complex.I * JanetCartan.Retarded.lower a β α f (t,y) =
      ∫ d in Ici (0 : ℝ), Complex.I * (α (t,y) : ℂ) *
        (β (t-d,y) : ℂ) * f (t-d,y) := by
  by_cases ht : a ≤ t
  · exact imaginary_lower_eq_normal a ε hε α β hβ f t y ht
  · have hzero : (∫ s in Ioc t a, (β (s,y) : ℂ) * f (s,y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simp [hβ s y (by linarith [hs.2])]
    have hnormal : (∫ d in Ici (0 : ℝ), Complex.I * (α (t,y) : ℂ) *
        (β (t-d,y) : ℂ) * f (t-d,y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with d hd
      simp [hβ (t-d) y (by have := hd; change 0 ≤ d at this; linarith)]
    rw [hnormal]
    simp [JanetCartan.Retarded.lower, intervalIntegral.integral_of_ge (le_of_not_ge ht), hzero]

/-- The upper input buffer makes the literal upper identity global as well:
above the fixed endpoint both sides vanish
(`app:ch_regular:lem:finite-chain`). -/
theorem imaginary_upper_eq_normal_of_input_buffer (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hα : ∀ s y, b-ε ≤ s → α (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) :
    -Complex.I * JanetCartan.Retarded.upper b β α f (t,y) =
      ∫ d in Ici (0 : ℝ), -Complex.I * (β (t,y) : ℂ) *
        (α (t+d,y) : ℂ) * f (t+d,y) := by
  by_cases ht : t ≤ b
  · exact imaginary_upper_eq_normal b ε hε α β hα f t y ht
  · have hzero : (∫ s in Ioc b t, (α (s,y) : ℂ) * f (s,y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simp [hα s y (by linarith [hs.1])]
    have hnormal : (∫ d in Ici (0 : ℝ), -Complex.I * (β (t,y) : ℂ) *
        (α (t+d,y) : ℂ) * f (t+d,y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with d hd
      simp [hα (t+d) y (by have := hd; change 0 ≤ d at this; linarith)]
    rw [hnormal]
    simp [JanetCartan.Retarded.upper, intervalIntegral.integral_of_ge (le_of_not_ge ht), hzero]

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
