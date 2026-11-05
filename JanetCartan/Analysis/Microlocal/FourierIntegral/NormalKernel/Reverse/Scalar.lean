module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Compact
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MultiplierKernel.IntegralFourier

/-!
# Scalar reverse graph representatives

The scalar inverse Fourier step consumed by `compactGraph_adjoint_ae_reverseIntegral`
for `app:ch_regular_base:eq:actual-normal-kernel`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter FourierTransform

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison AmplitudeBound

variable {n : ℕ} {t : Euclidean n → Euclidean n → ℂ}

/-- Compact frequency kernels have an L¹ adjoint representative even for L² input.
This supplies the inverse Fourier hypothesis in the reverse graph formula
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integrable_compact_adjoint_representative
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp (α := Euclidean n) ℂ 2) :
    Integrable (fun ξ ↦ ∫ x, star (t x ξ) * f x) := by
  have hs' : HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ star (t p.2 p.1)) :=
    (hs.comp_homeomorph (Homeomorph.prodComm _ _)).comp_left (star_zero ℂ)
  exact (continuous_compactKernel_integral_L2 (t := fun ξ x ↦ star (t x ξ))
    (ht.comp continuous_swap).star hs' f).integrable_of_hasCompactSupport (hasCompactSupport_compactKernel_integral_L2 hs' f)

/-- Inverse Fourier representation after the actual compact scalar adjoint;
consumed by the physical-covector reverse formula
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem inverseFourier_compact_adjoint_ae
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp (α := Euclidean n) ℂ 2) :
    (fourierL2 n).symm ((compactKernelOperator (μ := volume) (ν := volume) ht hs).adjoint f)
      =ᵐ[volume] fun y ↦ ∫ ξ, ∫ x,
        Complex.exp ((2 * Real.pi * inner ℝ ξ y : ℝ) * Complex.I) * star (t x ξ) * f x := by
  let g := (compactKernelOperator (μ := volume) (ν := volume) ht hs).adjoint f
  have he : g =ᵐ[volume] fun ξ ↦ ∫ x, star (t x ξ) * f x :=
    compactKernelOperator_adjoint_ae_integral ht hs f
  have hi : Integrable (g : Euclidean n → ℂ) volume :=
    (integrable_compact_adjoint_representative ht hs f).congr he.symm
  filter_upwards [fourierTransformInv_coeFn_ae_integral g hi] with y hy
  change (𝓕⁻ g : Lp ℂ 2 (volume : Measure (Euclidean n))) y = _
  rw [hy, Real.fourierInv_congr_ae he y, Real.fourierInv_eq']
  simp only [smul_eq_mul, ← integral_const_mul, mul_assoc]

/-- The inverse Fourier oscillation and conjugated forward phase combine to
exactly the reverse graph phase, including the conversion η = 2πξ
(`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem inverseFourier_phase_mul (S : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → ℂ) (x y ξ : Euclidean n) :
    Complex.exp ((2 * Real.pi * inner ℝ ξ y : ℝ) * Complex.I) *
      star (frequencyEntry S a x ξ) =
      star (graphOscillation S x y ((2 * Real.pi) • ξ)) *
        star (a x ((2 * Real.pi) • ξ)) := by
  simp only [frequencyEntry, physicalEntry, graphOscillation, ← starRingEnd_apply, map_mul,
    ← mul_assoc]
  congr 1
  simp only [← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add, inner_smul_right,
    Complex.ofReal_sub, Complex.ofReal_mul, map_sub]
  rw [real_inner_comm ξ y]
  congr 1
  ring

/-- The scalar actual adjoint is the literal normalized reverse integral.
This is the scalar channel of `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem graphBlock_adjoint_ae_reverseIntegral
    {S : Euclidean n → Euclidean n → ℝ} {a : Euclidean n → Euclidean n → ℂ}
    (hS : Continuous (Function.uncurry S)) (ha : Continuous (Function.uncurry a))
    (hs : HasCompactSupport (Function.uncurry a)) (f : Lp (α := Euclidean n) ℂ 2) :
    (fourierL2 n).symm ((compactKernelOperator (μ := volume) (ν := volume)
      (continuous_frequencyEntry hS ha) (hasCompactSupport_frequencyEntry S hs)).adjoint f)
      =ᵐ[volume] fun y ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η, ∫ x,
        star (graphOscillation S x y η) * star (a x η) * f x := by
  filter_upwards [inverseFourier_compact_adjoint_ae (continuous_frequencyEntry hS ha)
    (hasCompactSupport_frequencyEntry S hs) f] with y hy
  rw [hy]
  simp_rw [inverseFourier_phase_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun η ↦ ∫ x, star (graphOscillation S x y η) * star (a x η) * f x)
    (2 * Real.pi) (hR := by positivity)]
  simp [finrank_euclideanSpace, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul]

end JanetCartan.FourierIntegral.NormalKernel
