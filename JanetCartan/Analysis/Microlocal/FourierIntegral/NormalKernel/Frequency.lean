module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Oscillatory

/-!
# Physical covectors in the pure graph normal

The compact graph kernel is expressed in Mathlib's Fourier variable ξ, whereas
`app:ch_regular_base:eq:actual-normal-kernel` integrates the physical covector η.
This module proves the change η = 2πξ, including its precise Jacobian.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n : ℕ}

/-- The physical-covector kernel of a single graph matrix entry, before the
source Fourier transform (`app:ch_regular_base:eq:actual-normal-kernel`). -/
def physicalEntry (S : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → ℂ) (x η : Euclidean n) : ℂ :=
  Complex.exp (Complex.I * (S x η : ℂ)) * a x η

/-- The same entry in Mathlib's Fourier convention η = 2πξ
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
def frequencyEntry (S : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → ℂ) (x ξ : Euclidean n) : ℂ :=
  physicalEntry S a x ((2 * Real.pi) • ξ)

/-- Continuity of the compact frequency kernel used in the L² construction
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem continuous_frequencyEntry {S : Euclidean n → Euclidean n → ℝ}
    {a : Euclidean n → Euclidean n → ℂ}
    (hS : Continuous (Function.uncurry S)) (ha : Continuous (Function.uncurry a)) :
    Continuous (Function.uncurry (frequencyEntry S a)) := by
  have h : Continuous (Function.uncurry (physicalEntry S a)) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hS)).cexp.mul ha
  exact h.comp (show Continuous (fun p : Euclidean n × Euclidean n ↦
    (p.1, (2 * Real.pi) • p.2)) from
      continuous_fst.prodMk (continuous_snd.const_smul (2 * Real.pi)))

/-- Rescaling only the covector preserves compact joint amplitude support.
This supplies the actual compact-kernel input for the normal formula
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem hasCompactSupport_frequencyEntry (S : Euclidean n → Euclidean n → ℝ)
    {a : Euclidean n → Euclidean n → ℂ}
    (ha : HasCompactSupport (Function.uncurry a)) :
    HasCompactSupport (Function.uncurry (frequencyEntry S a)) := by
  let e : (Euclidean n × Euclidean n) ≃ₜ (Euclidean n × Euclidean n) :=
    { toFun := fun p ↦ (p.1, (2 * Real.pi) • p.2)
      invFun := fun p ↦ (p.1, (2 * Real.pi)⁻¹ • p.2)
      left_inv := by
        intro p
        simp only [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
      right_inv := by
        intro p
        simp only [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
      continuous_toFun := continuous_fst.prodMk (continuous_snd.const_smul (2 * Real.pi))
      continuous_invFun := continuous_fst.prodMk (continuous_snd.const_smul ((2 * Real.pi)⁻¹)) }
  have h : HasCompactSupport (Function.uncurry (physicalEntry S a)) := by
    unfold physicalEntry Function.uncurry
    exact HasCompactSupport.mul_left
      (f := fun p : Euclidean n × Euclidean n ↦ Complex.exp (Complex.I * (S p.1 p.2 : ℂ))) ha
  exact h.comp_isClosedEmbedding (g := e) e.isClosedEmbedding

/-- Exact phase subtraction for two matrix entries of the same real phase
(`app:ch_regular_base:eq:actual-normal-kernel`, and the cross-product sentence
following `app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem physicalEntry_mul_star (S : Euclidean n → Euclidean n → ℝ)
    (a b : Euclidean n → Euclidean n → ℂ) (x y η : Euclidean n) :
    physicalEntry S a x η * star (physicalEntry S b y η) =
      Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
        (a x η * star (b y η)) := by
  simpa [normalizedOscillatoryKernel, oscillatoryFactor, physicalEntry] using
    normalizedOscillatoryKernel_mul_star 1 1 S a b x y η

/-- The normal has exactly one factor `(2π)⁻ⁿ`, obtained from the Lebesgue
change of covector after Plancherel, not from formal oscillatory Fubini
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integral_frequencyEntry_mul_star (S : Euclidean n → Euclidean n → ℝ)
    (a b : Euclidean n → Euclidean n → ℂ) (x y : Euclidean n) :
    (∫ ξ, frequencyEntry S a x ξ * star (frequencyEntry S b y ξ)) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ *
        ∫ η, Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
          (a x η * star (b y η)) := by
  unfold frequencyEntry
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun η ↦ physicalEntry S a x η * star (physicalEntry S b y η))
    (2 * Real.pi) (hR := by positivity)]
  simp_rw [physicalEntry_mul_star]
  simp [finrank_euclideanSpace, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul]

end JanetCartan.FourierIntegral.NormalKernel
