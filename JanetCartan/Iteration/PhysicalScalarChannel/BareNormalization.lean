module

public import JanetCartan.Iteration.PhysicalScalarChannel.BareInput
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandIntegral

/-!
# Exact Fourier normalization of the bare scalar channel

The original Fourier scalar is retained. Removing the half derivative leaves
one fixed factor `(2π)^(-1/2)` times the transverse normal-operator scale;
there is no residual dyadic half power. All substitutions are on the original
wide-band measures, not on an altered radial partition.
Consumer: `app:ch_mean_pairs:eq:raw-adjoint-moments`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace JanetCartan.PhysicalScalarChannel
open RawInputPartition RawInputDilation RawPrimary.SliceBounds RawPrimary.MaskProfiles NormalComparison

variable {n : ℕ}

/-- Exact cancellation with every original radial/detector mask, including
points outside the annulus where the original radial mask is zero. -/
theorem annularInverseHalf_mul_normalizedMask
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (j : ℕ) (θ : Euclidean (n - 1)) :
    annularInverseHalf θ * normalizedMask angular H j θ =
      weightedRadialBand (detectorMask angular H) j ((2 : ℝ) ^ j • θ) := by
  by_cases hθ : (1 / 2 : ℝ) ≤ ‖θ‖
  · rw [normalizedMask, ← mul_assoc, mul_comm (annularInverseHalf θ),
      sqrt_mul_annularInverseHalf hθ, one_mul]
  · have hr : radialBand n 0 θ = 0 :=
      scalarBand_eq_zero_of_le (by simpa [dyadicScale] using (le_of_not_ge hθ))
    simp [normalizedMask_eq_zero_of_le angular H j (le_of_not_ge hθ),
      weightedRadialBand, radialBand_dyadic_rescale, hr]

/-- The unweighted integral has only the square root of the original
transverse Jacobian. This is a literal all-input Bochner identity. -/
theorem bare_wideBand_integral_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (j : ℕ) (b : Euclidean (n - 1) → ℂ) (a : Euclidean (n - 1) → E)
    (f : WideBandL2 n j) :
    (∫ η in wideBand n j, (b η * f η) • a η) =
      Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) •
        ∫ θ in wideBand n 0,
          (b ((2 : ℝ) ^ j • θ) * wideBandDilation n j f θ) • a ((2 : ℝ) ^ j • θ) := by
  have hsub := integral_wideBand_smul j (fun η ↦ (b η * f η) • a η)
  calc
    _ = ((2 : ℝ) ^ j) ^ (n - 1) • ∫ θ in wideBand n 0,
        (b ((2 : ℝ) ^ j • θ) * f ((2 : ℝ) ^ j • θ)) • a ((2 : ℝ) ^ j • θ) := by
      rw [hsub, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    _ = _ := by
      rw [← integral_smul, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [wideBandDilation_apply_ae j f] with θ hθ
      rw [hθ]
      simp only [← smul_assoc, Complex.real_smul]
      congr 1
      have hscalar : ((((2 : ℝ) ^ j) ^ (n - 1) : ℝ) : ℂ) =
          (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) *
            (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) := by
        exact_mod_cast (Real.mul_self_sqrt (show 0 ≤ ((2 : ℝ) ^ j) ^ (n - 1) by positivity)).symm
      rw [hscalar]
      ring

/-- The missing physical dimension contributes a fixed Fourier constant,
not a growing half power of the input ceiling. -/
theorem bare_fourierScalar_mul_sqrtJacobian (hn : 1 ≤ n) {K : ℝ} (hK : 0 < K) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.sqrt (K ^ (n - 1)) =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) * normalOperatorScale (n - 1) K := by
  have hs : Real.sqrt (K ^ (n - 1)) = K ^ (((n - 1 : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast K (n - 1), ← Real.rpow_mul hK.le]
    congr 1
    ring
  have hn' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn
  have hp : 0 < 2 * Real.pi := by positivity
  have hc : (2 * Real.pi) ^ (-(n : ℝ) / 2) =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) *
        (2 * Real.pi) ^ (-((n - 1 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add hp]
    congr 1
    linarith
  rw [hs, hc, mul_assoc, RawInputDilation.fourierScalar_mul_dilationScale hK]

/-- The literal bare full quotient phase after unit-band dilation, with its
original physical Fourier convention and no half-weight substitution. -/
theorem normalized_bare_wideBand_rawPhase_integral
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (hn : 1 ≤ n) (j : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (S : X → Euclidean (n - 1) → ℝ) (ζ : Euclidean (n - 1)) (x : X)
    (β : Euclidean (n - 1) → ℂ) (a : Euclidean (n - 1) → E)
    (f : WideBandL2 n j) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      (∫ η in wideBand n j,
        ((Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) * β η) * f η) • a η) =
    ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * normalOperatorScale (n - 1) ((2 : ℝ) ^ j)) •
      ∫ θ in wideBand n 0,
        ((oscillatoryFactor ((2 : ℝ) ^ j)
          (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) x θ) * β ((2 : ℝ) ^ j • θ)) *
            wideBandDilation n j f θ) • a ((2 : ℝ) ^ j • θ) := by
  rw [bare_wideBand_integral_dilation j, smul_smul,
    bare_fourierScalar_mul_sqrtJacobian hn (by positivity)]
  simp only [rawPrimaryPhaseDifference_dilate S ζ hτ (show 0 < (2 : ℝ) ^ j by positivity),
    oscillatoryFactor, Complex.ofReal_mul]

end JanetCartan.PhysicalScalarChannel
