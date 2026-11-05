module

public import JanetCartan.Analysis.Operator.Retarded
import Mathlib.Tactic.Linarith

/-!
# Removing the fixed endpoint from literal retarded kernels

`app:ch_regular:lem:finite-chain`, “Retarded and signed factors”. The hypotheses
state the fixed positive input buffers explicitly. The identities refer to the
actual `Retarded.lower` and `Retarded.upper` operators. The transverse delta is
implemented by evaluating the input on the same transverse fiber.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace JanetCartan.FiniteChain.Retarded

variable {Y : Type*}

/-- The lower fiber kernel of `app:ch_regular:lem:finite-chain`, before the
optional scalar `i` in the canonical inverse. -/
def lowerKernel (α β : ℝ × Y → ℝ) (t s : ℝ) (y : Y) : ℂ :=
  (α (t,y) : ℂ) * (if s ≤ t then 1 else 0) * (β (s,y) : ℂ)

/-- The literal adjoint fiber kernel: exchanged weights and reversed time
orientation (`app:ch_regular:lem:finite-chain`). -/
def upperKernel (α β : ℝ × Y → ℝ) (t s : ℝ) (y : Y) : ℂ :=
  (β (t,y) : ℂ) * (if t ≤ s then 1 else 0) * (α (s,y) : ℂ)

/-- The positive lower input buffer kills the fixed endpoint jump pointwise
(`app:ch_regular:lem:finite-chain`). -/
theorem lower_endpoint_jump_removed (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hβ : ∀ s y, s ≤ a+ε → β (s,y) = 0)
    (t s : ℝ) (y : Y) :
    (α (t,y) : ℂ) * ((if s ≤ t then 1 else 0) - (if s ≤ a then 1 else 0)) *
      (β (s,y) : ℂ) = lowerKernel α β t s y := by
  by_cases hs : s ≤ a
  · have hz := hβ s y (by linarith)
    simp [lowerKernel, hz]
  · simp [lowerKernel, hs]

/-- The positive upper input buffer kills the adjoint's fixed endpoint jump
(`app:ch_regular:lem:finite-chain`). It is the exchanged input weight `α`. -/
theorem upper_endpoint_jump_removed (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hα : ∀ s y, b-ε ≤ s → α (s,y) = 0)
    (t s : ℝ) (y : Y) :
    (β (t,y) : ℂ) * ((if t ≤ s then 1 else 0) - (if b ≤ s then 1 else 0)) *
      (α (s,y) : ℂ) = upperKernel α β t s y := by
  by_cases hs : b ≤ s
  · have hz := hα s y (by linarith)
    simp [upperKernel, hz]
  · simp [upperKernel, hs]

/-- The buffered lower integral is exactly the half-space fiber kernel of
`app:ch_regular:lem:finite-chain`. No endpoint value is dropped. -/
theorem lower_eq_integral_kernel (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hβ : ∀ s y, s ≤ a+ε → β (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) (ht : a ≤ t) :
    JanetCartan.Retarded.lower a β α f (t,y) =
      ∫ s, lowerKernel α β t s y * f (s,y) := by
  have he : (∫ s in Icc a t, if s ≤ t then (β (s,y) : ℂ) * f (s,y) else 0) =
      ∫ s, if s ≤ t then (β (s,y) : ℂ) * f (s,y) else 0 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    by_cases hst : s ≤ t
    · have hsa : s < a := by
        by_contra hn
        exact hs ⟨le_of_not_gt hn, hst⟩
      simp [hβ s y (by linarith)]
    · simp [hst]
  rw [JanetCartan.Retarded.integral_lower_triangle a t t ⟨ht, le_rfl⟩] at he
  simp only [JanetCartan.Retarded.lower]
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hst : s ≤ t <;> simp [lowerKernel, hst, mul_assoc]

/-- The buffered literal upper integral has the reversed half-space kernel
(`app:ch_regular:lem:finite-chain`). -/
theorem upper_eq_integral_kernel (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hα : ∀ s y, b-ε ≤ s → α (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) (ht : t ≤ b) :
    JanetCartan.Retarded.upper b β α f (t,y) =
      ∫ s, upperKernel α β t s y * f (s,y) := by
  have he : (∫ s in Icc t b, if t ≤ s then (α (s,y) : ℂ) * f (s,y) else 0) =
      ∫ s, if t ≤ s then (α (s,y) : ℂ) * f (s,y) else 0 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    by_cases hts : t ≤ s
    · have hbs : b < s := by
        by_contra hn
        exact hs ⟨hts, le_of_not_gt hn⟩
      simp [hα s y (by linarith)]
    · simp [hts]
  rw [JanetCartan.Retarded.integral_upper_triangle t b t ⟨le_rfl, ht⟩] at he
  simp only [JanetCartan.Retarded.upper]
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hts : t ≤ s <;> simp [upperKernel, hts, mul_assoc]

/-- The kernel adjoint exchanges its two time arguments
(`app:ch_regular:lem:finite-chain`). For an `i` multiple, the adjoint scalar is
`-i`, independently of any signed conjugate-partner convention. -/
theorem upperKernel_eq_conj_swap (α β : ℝ × Y → ℝ) (t s : ℝ) (y : Y) :
    upperKernel α β t s y = conj (lowerKernel α β s t y) := by
  by_cases h : t ≤ s <;> simp [upperKernel, lowerKernel, h, mul_comm]

/-- The actual canonical inverse with prefactor `i` has the manuscript's
`i α H β` kernel (`app:ch_regular:lem:finite-chain`). -/
theorem imaginary_lower_eq_integral_kernel (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × Y → ℝ) (hβ : ∀ s y, s ≤ a+ε → β (s,y) = 0)
    (f : ℝ × Y → ℂ) (t : ℝ) (y : Y) (ht : a ≤ t) :
    Complex.I * JanetCartan.Retarded.lower a β α f (t,y) =
      ∫ s, (Complex.I * lowerKernel α β t s y) * f (s,y) := by
  rw [lower_eq_integral_kernel a ε hε α β hβ f t y ht, ← integral_const_mul]
  simp only [mul_assoc]

end JanetCartan.FiniteChain.Retarded
