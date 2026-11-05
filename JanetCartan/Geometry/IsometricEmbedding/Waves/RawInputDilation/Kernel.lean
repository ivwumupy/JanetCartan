module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Isometry
public import JanetCartan.Analysis.Microlocal.NormalComparison.FrequencyNormalization

/-!
# Half-derivative normalization on the literal annulus

The change of input preceding `app:ch_waves:eq:sampling-prefix-normal` combines
the `(n-1)`-dimensional Jacobian, the unitary input factor, and the half derivative.
It leaves the mask and amplitude evaluated at the physical frequency `K • θ`.
These are exact Bochner integral identities; operator boundedness and the actual
WKB amplitude are supplied by the raw-primary and masked-normal constructions.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputDilation
open RawInputRealization
variable {n : ℕ} {K : ℝ}

/-- The half derivative supplies the missing half power in the normalization of
`app:ch_waves:thm:sampling`. -/
theorem sqrt_jacobian_mul_sqrt (hn : 1 ≤ n) (hK : 0 < K) :
    Real.sqrt (K ^ (n - 1)) * Real.sqrt K = K ^ ((n : ℝ) / 2) := by
  rw [← Real.sqrt_mul (by positivity), ← pow_succ, Nat.sub_add_cancel hn,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast K n, ← Real.rpow_mul hK.le]
  congr 1
  ring

/-- The exact scalar identity after substitution in the half-derivative kernel
(`app:ch_waves:thm:sampling`). -/
theorem jacobian_mul_sqrt (hn : 1 ≤ n) (hK : 0 < K) :
    K ^ (n - 1) * Real.sqrt K =
      K ^ ((n : ℝ) / 2) * Real.sqrt (K ^ (n - 1)) := by
  rw [← sqrt_jacobian_mul_sqrt hn hK]
  calc
    _ = Real.sqrt (K ^ (n - 1)) ^ 2 * Real.sqrt K := by
      rw [Real.sq_sqrt (by positivity)]
    _ = _ := by ring

/-- The fixed Fourier scalar in `app:ch_waves:thm:sampling` produces exactly
`NormalComparison.normalOperatorScale`, without changing the annular measure. -/
theorem fourierScalar_mul_dilationScale (hK : 0 < K) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) * K ^ ((n : ℝ) / 2) =
      NormalComparison.normalOperatorScale n K := by
  rw [NormalComparison.normalOperatorScale, Real.div_rpow hK.le (by positivity)]
  rw [neg_div, Real.rpow_neg (by positivity)]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [IsScalarTower ℝ ℂ F] in
/-- The zero-extended literal density from `RawInputRealization` gives exactly
the restricted annular integral (`app:ch_waves:thm:individual`). -/
theorem integral_channelDensity_smul (β : Euclidean (n - 1) → ℂ)
    (a : Euclidean (n - 1) → F) (f : AnnularL2 n K) :
    (∫ η, channelDensity β f η • a η) =
      ∫ η, ((Real.sqrt ‖η‖ : ℂ) * β η * f η) • a η ∂annularMeasure n K := by
  simp only [channelDensity, ← Set.indicator_smul_left]
  exact integral_indicator (measurableSet_annulus n K)

/-- Exact half-derivative kernel substitution for `app:ch_waves:thm:sampling`.
The complex coefficient `b` may contain the oscillatory factor and every input
mask; `a` is the vector or matrix amplitude. The `|θ|^(1/2)` factor is retained. -/
theorem halfDerivative_integral_dilation (hn : 1 ≤ n) (hK : 0 < K)
    (b : Euclidean (n - 1) → ℂ) (a : Euclidean (n - 1) → F)
    (f : AnnularL2 n K) :
    (∫ η, ((Real.sqrt ‖η‖ : ℂ) * b η * f η) • a η ∂annularMeasure n K) =
      (K ^ ((n : ℝ) / 2) : ℝ) •
        ∫ θ, ((Real.sqrt ‖θ‖ : ℂ) * b (K • θ) * annularDilation n K hK f θ) •
          a (K • θ) ∂annularMeasure n 1 := by
  have hsub := integral_annular_smul hK 1
    (fun η ↦ ((Real.sqrt ‖η‖ : ℂ) * b η * f η) • a η)
  rw [mul_one] at hsub
  calc
    _ = K ^ (n - 1) •
        ∫ θ, ((Real.sqrt ‖K • θ‖ : ℂ) * b (K • θ) * f (K • θ)) •
          a (K • θ) ∂annularMeasure n 1 := by
      rw [hsub, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hK.ne'), one_smul]
    _ = _ := by
      rw [← integral_smul, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [annularDilation_apply_ae hK f] with θ hθ
      rw [hθ, norm_smul, Real.norm_eq_abs, abs_of_pos hK, Real.sqrt_mul hK.le]
      simp only [Complex.ofReal_mul, ← smul_assoc, Complex.real_smul]
      congr 1
      have hscalar : (K ^ (n - 1) : ℂ) * (Real.sqrt K : ℂ) =
          (K ^ ((n : ℝ) / 2) : ℝ) * (Real.sqrt (K ^ (n - 1)) : ℂ) := by
        exact_mod_cast jacobian_mul_sqrt hn hK
      simp only [Complex.ofReal_pow]
      linear_combination
        (Real.sqrt ‖θ‖ : ℂ) * b (K • θ) * f (K • θ) * hscalar

/-- Literal oscillatory kernel normalization with every mask evaluated at `Kθ`
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:actual-T`). The phase here is the
actual phase at the physical frequency; rewriting it as `K φ` is a separate
identity, not an implicit homogeneity assumption. -/
theorem normalized_halfDerivative_integral (hn : 1 ≤ n) (hK : 0 < K)
    (phase : Euclidean (n - 1) → ℝ) (β : Euclidean (n - 1) → ℂ)
    (a : Euclidean (n - 1) → F) (f : AnnularL2 n K) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      (∫ η, ((Real.sqrt ‖η‖ : ℂ) *
        (Complex.exp (Complex.I * (phase η : ℂ)) * β η) * f η) •
          a η ∂annularMeasure n K) =
    NormalComparison.normalOperatorScale n K •
      ∫ θ, ((Real.sqrt ‖θ‖ : ℂ) *
        (Complex.exp (Complex.I * (phase (K • θ) : ℂ)) * β (K • θ)) *
          annularDilation n K hK f θ) • a (K • θ) ∂annularMeasure n 1 := by
  rw [halfDerivative_integral_dilation hn hK, smul_smul, fourierScalar_mul_dilationScale hK]

end JanetCartan.RawInputDilation
