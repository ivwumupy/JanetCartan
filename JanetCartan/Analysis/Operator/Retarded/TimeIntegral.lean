module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Time-triangle Fubini identities

The time-triangle calculation underlying `app:ch_osc:eq:retarded-literal-adjoint`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace JanetCartan.Retarded

/-- The lower-time triangle represents the literal integral in
`app:ch_osc:setup:osc-retarded`. -/
theorem integral_lower_triangle (a b t : ℝ) (ht : t ∈ Icc a b) (f : ℝ → ℂ) :
    (∫ s in Icc a b, if s ≤ t then f s else 0) = ∫ s in a..t, f s := by
  change (∫ s in Icc a b, (Iic t).indicator f s) = _
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic t ∩ Icc a b = Icc a t := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · tauto
    · intro hs
      exact ⟨hs.2, hs.1, hs.2.trans ht.2⟩
  rw [hset, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1]

/-- The upper-time triangle represents the literal integral in
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem integral_upper_triangle (a b s : ℝ) (hs : s ∈ Icc a b) (g : ℝ → ℂ) :
    (∫ t in Icc a b, if s ≤ t then g t else 0) = ∫ t in s..b, g t := by
  change (∫ t in Icc a b, (Ici s).indicator g t) = _
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici s ∩ Icc a b = Icc s b := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · tauto
    · intro ht
      exact ⟨ht.1, hs.1.trans ht.1, ht.2⟩
  rw [hset, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs.2]

/-- Fubini on the time triangle, for
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem integral_triangle_swap (μ : Measure ℝ) [SFinite μ] (f g : ℝ → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ t, (∫ s, if s ≤ t then f s else 0 ∂μ) * g t ∂μ) =
      ∫ s, f s * (∫ t, if s ≤ t then g t else 0 ∂μ) ∂μ := by
  have hi : Integrable (fun p : ℝ × ℝ ↦ if p.1 ≤ p.2 then f p.1 * g p.2 else 0)
      (μ.prod μ) :=
    (hf.mul_prod hg).indicator (measurableSet_le measurable_fst measurable_snd)
  calc
    _ = ∫ t, ∫ s, if s ≤ t then f s * g t else 0 ∂μ ∂μ := by
      simp_rw [← integral_mul_const]
      congr 1
      funext t
      congr 1
      funext s
      split_ifs <;> simp
    _ = ∫ s, ∫ t, if s ≤ t then f s * g t else 0 ∂μ ∂μ :=
      (integral_integral_swap hi).symm
    _ = _ := by
      simp_rw [← integral_const_mul]
      congr 1
      funext s
      congr 1
      funext t
      split_ifs <;> simp

/-- Unweighted adjoint identity on the fixed interval, for
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem integral_lower_mul_eq_mul_upper (a b : ℝ) (f g : ℝ → ℂ)
    (hf : IntegrableOn f (Icc a b)) (hg : IntegrableOn g (Icc a b)) :
    (∫ t in Icc a b, (∫ s in a..t, f s) * g t) =
      ∫ s in Icc a b, f s * (∫ t in s..b, g t) := by
  calc
    _ = ∫ t in Icc a b, (∫ s in Icc a b, if s ≤ t then f s else 0) * g t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [integral_lower_triangle a b t ht]
    _ = ∫ s in Icc a b, f s * (∫ t in Icc a b, if s ≤ t then g t else 0) :=
      integral_triangle_swap _ f g hf hg
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [integral_upper_triangle a b s hs]

/-- Conjugation of the literal integral, used in
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem intervalIntegral_conj (a b : ℝ) (g : ℝ → ℂ) :
    (∫ t in a..b, conj (g t)) = conj (∫ t in a..b, g t) := by
  simp [intervalIntegral, integral_conj]

end JanetCartan.Retarded
