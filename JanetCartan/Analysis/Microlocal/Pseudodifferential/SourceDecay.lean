module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Frequency
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Decay after integration in the physical source

For `app:ch_regular_base:thm:actual-calculus`, source integration makes a full
amplitude integrable in frequency. The estimate uses a finite number of source
derivatives. A polynomial growth order `m` requires only `m + dim + 1` such
derivatives; the decay constant and derivative budget are explicit.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

namespace JanetCartan.Pseudodifferential
variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: the finite integral budget for
source derivatives, including the undifferentiated amplitude. -/
def sourceDerivativeMass (f : V → F) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ∫ y, ‖iteratedFDeriv ℝ j f y‖

/-- `app:ch_regular_base:thm:actual-calculus`: source integration by parts
provides a dimension-independent explicit Fourier decay constant. -/
theorem pow_mul_norm_fourier_le_sourceDerivativeMass
    (f : V → F) (n : ℕ) (hf : ContDiff ℝ n f)
    (hi : ∀ j ≤ n, Integrable (iteratedFDeriv ℝ j f)) (ξ : V) :
    ‖ξ‖ ^ n * ‖𝓕 f ξ‖ ≤ 2 ^ n * sourceDerivativeMass f n := by
  have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := 0) (N := n) hf (fun k j hk hj ↦ ?_) (k := 0) (n := n) (by simp) (by simp) ξ
  · simp only [Finset.sum_product] at hh
    simpa [sourceDerivativeMass, norm_iteratedFDeriv_zero] using hh
  · have hk0 : k = 0 := by simpa using hk
    subst k
    simpa using (hi j (by exact_mod_cast hj)).norm

/-- `app:ch_regular_base:thm:actual-calculus`: the decay estimate also controls
bounded frequencies, without removing a neighborhood of zero. -/
theorem one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    (f : V → F) (n : ℕ) (hf : ContDiff ℝ n f)
    (hi : ∀ j ≤ n, Integrable (iteratedFDeriv ℝ j f)) (ξ : V) :
    (1 + ‖ξ‖) ^ n * ‖𝓕 f ξ‖ ≤
      (2 ^ (n - 1) * (1 + 2 ^ n)) * sourceDerivativeMass f n := by
  have hzero : (∫ y, ‖f y‖) ≤ sourceDerivativeMass f n := by
    simpa [sourceDerivativeMass, norm_iteratedFDeriv_zero] using
      (Finset.single_le_sum (f := fun j ↦ ∫ y, ‖iteratedFDeriv ℝ j f y‖)
        (fun j _ ↦ integral_nonneg (fun _ ↦ norm_nonneg _))
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
  have hsmall := (Real.norm_fourier_le_integral_norm f ξ).trans hzero
  have hlarge := pow_mul_norm_fourier_le_sourceDerivativeMass f n hf hi ξ
  calc
    _ ≤ (2 ^ (n - 1) * (1 + ‖ξ‖ ^ n)) * ‖𝓕 f ξ‖ := by
      gcongr
      simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg ξ) n
    _ = 2 ^ (n - 1) * (‖𝓕 f ξ‖ + ‖ξ‖ ^ n * ‖𝓕 f ξ‖) := by ring
    _ ≤ 2 ^ (n - 1) * (sourceDerivativeMass f n + 2 ^ n * sourceDerivativeMass f n) := by
      gcongr
    _ = _ := by ring

/-- `app:ch_regular_base:thm:actual-calculus`: the partial source Fourier
transform is measurable for a continuous full amplitude. -/
theorem stronglyMeasurable_sourceFourier (g : V → V → F)
    (hg : Continuous (Function.uncurry g)) :
    StronglyMeasurable (fun ξ ↦ 𝓕 (g ξ) ξ) := by
  simp only [Real.fourier_eq]
  apply StronglyMeasurable.integral_prod_right
  apply Continuous.stronglyMeasurable
  exact (Real.continuous_fourierChar.comp (by fun_prop)).smul hg

/-- `app:ch_regular_base:thm:actual-calculus`: polynomial growth of the finite
source-derivative budget gives absolute frequency integrability after source
integration. The derivative reserve is `n - m > dim V`. -/
theorem integrable_sourceFourier_of_derivativeMass
    (g : V → V → F) (hg : Continuous (Function.uncurry g)) (m n : ℕ)
    (hn : m + Module.finrank ℝ V < n)
    (hs : ∀ ξ, ContDiff ℝ n (g ξ))
    (hi : ∀ ξ j, j ≤ n → Integrable (iteratedFDeriv ℝ j (g ξ)))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass (g ξ) n ≤ A * (1 + ‖ξ‖) ^ m) :
    Integrable (fun ξ ↦ 𝓕 (g ξ) ξ) := by
  let C : ℝ := 2 ^ (n - 1) * (1 + 2 ^ n)
  have hn' : (Module.finrank ℝ V : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) + Module.finrank ℝ V < n := by exact_mod_cast hn
    linarith
  apply ((integrable_one_add_norm (μ := volume) hn').const_mul (C * A)).mono'
    (stronglyMeasurable_sourceFourier g hg).aestronglyMeasurable
  filter_upwards [] with ξ
  have hp : 0 < 1 + ‖ξ‖ := by positivity
  have hh := one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass (g ξ) n
    (hs ξ) (hi ξ) ξ
  have hb : (1 + ‖ξ‖) ^ n * ‖𝓕 (g ξ) ξ‖ ≤ C * (A * (1 + ‖ξ‖) ^ m) :=
    hh.trans (mul_le_mul_of_nonneg_left (hA ξ) (by positivity))
  have heq : (1 + ‖ξ‖) ^ (-((n : ℝ) - m)) = (1 + ‖ξ‖) ^ m / (1 + ‖ξ‖) ^ n := by
    rw [neg_sub, Real.rpow_sub hp, Real.rpow_natCast, Real.rpow_natCast]
  rw [heq, ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hp n)).mpr
  nlinarith [hb]

/-- `app:ch_regular_base:thm:actual-calculus`: compact source support discharges
all derivative integrability assumptions in the finite decay estimate. -/
theorem integrable_sourceFourier_of_compact_derivativeMass
    (g : V → V → F) (hg : Continuous (Function.uncurry g)) (m n : ℕ)
    (hn : m + Module.finrank ℝ V < n)
    (hs : ∀ ξ, ContDiff ℝ n (g ξ)) (hcompact : ∀ ξ, HasCompactSupport (g ξ))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass (g ξ) n ≤ A * (1 + ‖ξ‖) ^ m) :
    Integrable (fun ξ ↦ 𝓕 (g ξ) ξ) := by
  apply integrable_sourceFourier_of_derivativeMass g hg m n hn hs _ A hA
  intro ξ j hj
  exact ((hs ξ).continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
    ((hcompact ξ).iteratedFDeriv j)

end JanetCartan.Pseudodifferential
