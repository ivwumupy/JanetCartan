module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.ProductBounds.Coefficient

/-!
# Primitive profile substitution for auxiliary products

The finite profile deduction used in `app:ch_background:eq:bg-Vaux-band`.
It does not assert a geometric realization: the geometric coefficients and
field profiles must still be supplied by the parent construction.
-/

@[expose] public noncomputable section

namespace JanetCartan.AuxiliaryRawBand

variable {n : ℕ}

/-- Profile constant fixed before coefficients, fields, scales and input size
in `app:ch_background:eq:bg-Vaux-band`. Only entries through `s` occur.
Absolute values allow arbitrary real upper-bound profiles. -/
def coefficientBandConstant (n s : ℕ) (a b : ℕ → ℝ) : ℝ :=
  coefficientProductConstant n s *
    ∑ r ∈ Finset.range (s+1), |a r| * |b (s-r)|

/-- Nonnegativity of the finite profile constant for
`app:ch_background:eq:bg-Vaux-band`. -/
theorem coefficientBandConstant_nonneg (n s : ℕ) (a b : ℕ → ℝ) :
    0 ≤ coefficientBandConstant n s a b :=
  mul_nonneg (coefficientProductConstant_nonneg n s)
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem profileSum_le (s : ℕ) (a b u v : ℕ → ℝ)
    (hv : ∀ j, 0 ≤ v j) {T K H : ℝ}
    (hT : 1 ≤ T) (hTK : T ≤ K) (hH : 0 ≤ H)
    (hu : ∀ r ≤ s, u r ≤ a r * T ^ r)
    (hb : ∀ j ≤ s, v j ≤ b j * K ^ j * H) :
    (∑ r ∈ Finset.range (s+1), u r * v (s-r)) ≤
      (∑ r ∈ Finset.range (s+1), |a r| * |b (s-r)|) * K ^ s * H := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hK0 : 0 ≤ K := hT0.trans hTK
  rw [mul_assoc, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  have hrs : r ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hu' : u r ≤ |a r| * T ^ r :=
    (hu r hrs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hT0 _))
  have hv' : v (s-r) ≤ |b (s-r)| * K ^ (s-r) * H :=
    (hb (s-r) (by omega)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hK0 _)) hH)
  have hp : T ^ r * K ^ (s-r) ≤ K ^ s := by
    calc
      _ ≤ K ^ r * K ^ (s-r) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hT0 hTK r) (pow_nonneg hK0 _)
      _ = K ^ s := by rw [← pow_add, Nat.add_sub_of_le hrs]
  calc
    _ ≤ (|a r| * T ^ r) * (|b (s-r)| * K ^ (s-r) * H) :=
      mul_le_mul hu' hv' (hv _) (by positivity)
    _ = (|a r| * |b (s-r)| * H) * (T ^ r * K ^ (s-r)) := by ring
    _ ≤ (|a r| * |b (s-r)| * H) * K ^ s :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The joint derivative budget absorbs `T^r K^(s-r)` into `K^s`.
This is the intermediate profile deduction for source multiplication and
geometric coefficient products in `app:ch_background:eq:bg-Vaux-band`. -/
theorem periodicSobolevNorm_bilinear_le_of_profiles
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (s : ℕ) (a b : ℕ → ℝ)
    (B : D →L[ℝ] E →L[ℝ] F) (hB : ‖B‖ ≤ 1)
    (A : Torus n → D) (f : Torus n → E)
    (hA : IsSmoothPeriodic A) (hf : IsSmoothPeriodic f)
    {T K H : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K) (hH : 0 ≤ H)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift A) ≤ a r * T ^ r)
    (hfield : ∀ j ≤ s, periodicSobolevNorm j f ≤ b j * K ^ j * H) :
    periodicSobolevNorm s (fun x ↦ B (A x) (f x)) ≤
      coefficientBandConstant n s a b * K ^ s * H := by
  apply (periodicSobolevNorm_bilinear_le B hB A f hA hf s).trans
  calc
    _ ≤ coefficientProductConstant n s *
        ((∑ r ∈ Finset.range (s+1), |a r| * |b (s-r)|) * K ^ s * H) :=
      mul_le_mul_of_nonneg_left
        (profileSum_le s a b (fun r ↦ cNorm (fundamentalCell n) r (periodicLift A))
          (fun j ↦ periodicSobolevNorm j f) (fun _ ↦ Real.sqrt_nonneg _)
          hT hTK hH hcoef hfield) (coefficientProductConstant_nonneg n s)
    _ = _ := by unfold coefficientBandConstant; ring

/-- Operator-valued primitive coefficient profiles imply the band estimate
needed by raising, Christoffel, stress and cutoff-error terms in
`app:ch_background:eq:bg-Vaux-band`. The constant precedes all actual fields. -/
theorem periodicSobolevNorm_clm_apply_le_of_profiles
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (s : ℕ) (a b : ℕ → ℝ)
    (A : Torus n → E →L[ℝ] F) (f : Torus n → E)
    (hA : IsSmoothPeriodic A) (hf : IsSmoothPeriodic f)
    {T K H : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K) (hH : 0 ≤ H)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift A) ≤ a r * T ^ r)
    (hfield : ∀ j ≤ s, periodicSobolevNorm j f ≤ b j * K ^ j * H) :
    periodicSobolevNorm s (fun x ↦ A x (f x)) ≤
      coefficientBandConstant n s a b * K ^ s * H :=
  periodicSobolevNorm_bilinear_le_of_profiles s a b
    (ContinuousLinearMap.id ℝ (E →L[ℝ] F)) ContinuousLinearMap.norm_id_le
    A f hA hf hT hTK hH hcoef hfield

/-- Scalar primitive profiles, valid for the source cutoff and the original
exterior multiplier `1-ψ` in `app:ch_background:eq:bg-Vaux-band`. -/
theorem periodicSobolevNorm_smul_le_of_profiles
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (s : ℕ) (a b : ℕ → ℝ) (χ : Torus n → ℝ) (f : Torus n → E)
    (hχ : IsSmoothPeriodic χ) (hf : IsSmoothPeriodic f)
    {T K H : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K) (hH : 0 ≤ H)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χ) ≤ a r * T ^ r)
    (hfield : ∀ j ≤ s, periodicSobolevNorm j f ≤ b j * K ^ j * H) :
    periodicSobolevNorm s (fun x ↦ χ x • f x) ≤
      coefficientBandConstant n s a b * K ^ s * H :=
  periodicSobolevNorm_bilinear_le_of_profiles s a b
    (ContinuousLinearMap.lsmul ℝ ℝ) ContinuousLinearMap.opNorm_lsmul_le
    χ f hχ hf hT hTK hH hcoef hfield

end JanetCartan.AuxiliaryRawBand
