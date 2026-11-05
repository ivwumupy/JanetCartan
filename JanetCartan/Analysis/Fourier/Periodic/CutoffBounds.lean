module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Kernel
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Spectral
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Sobolev
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Convolution
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation

/-!
# Quantitative smoothing and high-frequency tails

For `main:lem:smoothing`, the fixed `periodicCutoff` family satisfies
`‖S_R f‖_{Cʳ} + ‖S_R f‖_{Hʳ} ≤ C_r Rʳ ‖f‖_{C⁰}` and
`‖f - S_R f‖_{C⁰} ≤ C_N R⁻ᴺ ‖f‖_{Cᴺ}` for `R ≥ 1`.
The constants are independent of the scale and input, and the same cutoff works
at every order, including zero. All norms use the shared unit-torus convention
and the closed fundamental cell.

The Cʳ and tail estimates hold for real Banach codomains. The combined estimate
uses a finite-dimensional real Hilbert codomain for Parseval. The kernel mass,
cancellation, convolution, and Fourier identities are proved in the imported
modules; none is an additional hypothesis of these estimates. Extension from
the manuscript's domain and the metric-defect application are separate steps.
-/

@[expose] public noncomputable section

universe u

namespace JanetCartan

/-- `main:eq:smoothing-low`: summing the uniform derivative bounds gives the Cʳ
estimate for a continuous input bounded by `M`. The nonnegative constant depends
only on the dimension and order, and works for every real Banach codomain. -/
theorem exists_periodicCutoff_cNorm_bound_of_bound (n r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {R : ℝ}, 1 ≤ R → ∀ {f : Torus n → F}, Continuous f →
        ∀ {M : ℝ}, 0 ≤ M → (∀ y, ‖f y‖ ≤ M) →
        cNorm (fundamentalCell n) r (periodicLift (periodicCutoff R f)) ≤
          C * R ^ r * M := by
  choose C hC hderiv using fun j ↦ exists_periodicCutoff_derivative_bound.{u} n j
  refine ⟨∑ j ∈ Finset.range (r + 1), C j,
    Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro F _ _ _ R hR f hf M hM hbound
  calc
    _ ≤ ∑ j ∈ Finset.range (r + 1), C j * R ^ r * M := by
      apply cNorm_le_sum_of_bounds (fun j _ ↦ mul_nonneg
        (mul_nonneg (hC j) (pow_nonneg (le_trans zero_le_one hR) r)) hM)
      intro j hj x _
      exact (hderiv j hR hf hM hbound x).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hj) (hC j)) hM)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- `main:eq:smoothing-low`: the fixed cutoff maps the C⁰ input norm to the Cʳ
output norm with growth `Rʳ`, uniformly over real Banach codomains. -/
theorem exists_periodicCutoff_cNorm_bound (n r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {R : ℝ}, 1 ≤ R → ∀ {f : Torus n → F}, IsSmoothPeriodic f →
        cNorm (fundamentalCell n) r (periodicLift (periodicCutoff R f)) ≤
          C * R ^ r * cNorm (fundamentalCell n) 0 (periodicLift f) := by
  obtain ⟨C, hC, hbound⟩ := exists_periodicCutoff_cNorm_bound_of_bound.{u} n r
  refine ⟨C, hC, ?_⟩
  intro F _ _ _ R hR f hf
  exact hbound hR hf.1 (cNorm_nonneg _ _ _) hf.norm_le_cNorm_zero

/-- `main:lem:smoothing`, `main:eq:smoothing-low`: the sum of the Cʳ and Hʳ
norms of the fixed cutoff is bounded by `C_r Rʳ` times the C⁰ input norm.
The constant is uniform over finite-dimensional real Hilbert codomains. -/
theorem exists_periodicCutoff_smoothing_bound (n r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [FiniteDimensional ℝ F] {R : ℝ}, 1 ≤ R →
        ∀ {f : Torus n → F}, IsSmoothPeriodic f →
        cNorm (fundamentalCell n) r (periodicLift (periodicCutoff R f)) +
          periodicSobolevNorm (r : ℝ) (periodicCutoff R f) ≤
            C * R ^ r * cNorm (fundamentalCell n) 0 (periodicLift f) := by
  obtain ⟨C, hC, hbound⟩ := exists_periodicCutoff_cNorm_bound.{u} n r
  refine ⟨C + Real.sqrt 5 ^ r, add_nonneg hC (by positivity), ?_⟩
  intro F _ _ _ R hR f hf
  calc
    _ ≤ C * R ^ r * cNorm (fundamentalCell n) 0 (periodicLift f) +
        Real.sqrt 5 ^ r * R ^ r * cNorm (fundamentalCell n) 0 (periodicLift f) :=
      add_le_add (hbound hR hf) (periodicSobolevNorm_periodicCutoff_le_cNorm_zero hf hR r)
    _ = _ := by ring

/-- `main:lem:smoothing`, `main:eq:smoothing-high`: taking the supremum of the
pointwise approximation bound gives the C⁰ tail with exactly `N` input
derivatives and `R⁻ᴺ` decay. This also holds at every positive scale. -/
theorem cNorm_sub_periodicCutoff_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (N : ℕ)
    {R : ℝ} (hR : 0 < R) :
    cNorm (fundamentalCell n) 0 (periodicLift (f - periodicCutoff R f)) ≤
      periodicCutoffApproximationConstant n N * (R ^ N)⁻¹ *
        cNorm (fundamentalCell n) N (periodicLift f) := by
  simp only [cNorm, zero_add, Finset.sum_range_one, norm_iteratedFDeriv_zero]
  apply csSup_le ((fundamentalCell_nonempty n).image _)
  rintro _ ⟨x, _, rfl⟩
  exact norm_periodicLift_sub_periodicCutoff_le hf N hR x

/-- `main:eq:smoothing-high` and, at `N = 0`, `main:eq:smoothing-small`: a
nonnegative constant independent of scale, input, and real Banach codomain
controls the C⁰ tail of the same fixed cutoff at every natural order. -/
theorem exists_periodicCutoff_tail_bound (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {R : ℝ}, 1 ≤ R → ∀ {f : Torus n → F}, IsSmoothPeriodic f →
        cNorm (fundamentalCell n) 0 (periodicLift (f - periodicCutoff R f)) ≤
          C * (R ^ N)⁻¹ * cNorm (fundamentalCell n) N (periodicLift f) := by
  refine ⟨periodicCutoffApproximationConstant n N,
    periodicCutoffApproximationConstant_nonneg n N, ?_⟩
  intro F _ _ _ R hR f hf
  exact cNorm_sub_periodicCutoff_le hf N (lt_of_lt_of_le zero_lt_one hR)

end JanetCartan
