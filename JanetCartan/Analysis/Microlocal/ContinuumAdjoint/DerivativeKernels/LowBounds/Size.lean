module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Kernel

/-!
# Cancellation of the two half-order factors

The zeroth-order calculation in `app:ch_background:prop:bg-adjoint`. The
degree-one conic Jacobian cancels the product of the two half-order amplitudes.
The higher mixed-jet estimate and operator realization are separate obligations;
this pointwise estimate alone is not an L² theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow ContinuumRow.TransportKernel

variable {n : ℕ}

/-- The two half-order amplitudes give exactly one power of the physical
covector, uniformly in a bounded regularization
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_modifiedNormalDensity_le
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) (u : CarrierVariable n) {A : ℝ} (hA : 0 ≤ A)
    (hm : |m u| ≤ 1)
    (hx : ‖a u.1 x u.2‖ ≤ A * Real.sqrt ‖u.2‖)
    (hy : ‖a u.1 y u.2‖ ≤ A * Real.sqrt ‖u.2‖) :
    ‖modifiedNormalDensity a m x y u‖ ≤ A ^ 2 * ‖u.2‖ := by
  have hm2 : |m u| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (m u)]
  simp only [modifiedNormalDensity, norm_mul, norm_pow, norm_star, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    _ ≤ 1 * ((A * Real.sqrt ‖u.2‖) * (A * Real.sqrt ‖u.2‖)) := by
      apply mul_le_mul hm2
        (mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hA (Real.sqrt_nonneg _)))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = A ^ 2 * ‖u.2‖ := by
      nlinarith [Real.sq_sqrt (norm_nonneg u.2)]

/-- Division by the actual degree-one determinant removes the frequency
growth, before spectator integration (`app:ch_background:prop:bg-adjoint`).
The gap is `c |η|`, not `c |η|^n`. -/
theorem norm_modifiedNormalDensity_div_jacobian_le
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) (u : CarrierVariable n) {A c j : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hu : u.2 ≠ 0)
    (hj : c * ‖u.2‖ ≤ |j|) (hm : |m u| ≤ 1)
    (hx : ‖a u.1 x u.2‖ ≤ A * Real.sqrt ‖u.2‖)
    (hy : ‖a u.1 y u.2‖ ≤ A * Real.sqrt ‖u.2‖) :
    ‖|j|⁻¹ • modifiedNormalDensity a m x y u‖ ≤ A ^ 2 / c := by
  have hjpos : 0 < |j| := (mul_pos hc (norm_pos_iff.mpr hu)).trans_le hj
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_inv_mul]
  apply (div_le_iff₀ hjpos).mpr
  apply (norm_modifiedNormalDensity_le a m x y u hA hm hx hy).trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith [mul_le_mul_of_nonneg_left hj (sq_nonneg A)]

/-- Uniform zeroth-order bound on the full zero-extended conic density.
Both positions retain their own amplitude (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_modifiedInverseDensity_le
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (k : Euclidean n) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hbound : ∀ k ∈ Ψ v '' D v,
      let u := chartCarrierVariable e v (U v k)
      u.2 ≠ 0 ∧ c * ‖u.2‖ ≤ |(J v (U v k)).det| ∧ |m u| ≤ 1 ∧
        ‖a u.1 x u.2‖ ≤ A * Real.sqrt ‖u.2‖ ∧
        ‖a u.1 y u.2‖ ≤ A * Real.sqrt ‖u.2‖) :
    ‖modifiedInverseDensity a m x y e D Ψ U J v k‖ ≤ A ^ 2 / c := by
  by_cases hk : k ∈ Ψ v '' D v
  · obtain ⟨hu, hj, hm, hx, hy⟩ := hbound k hk
    simp only [modifiedInverseDensity, indicator_of_mem hk]
    exact norm_modifiedNormalDensity_div_jacobian_le a m x y _ hA hc hu hj hm hx hy
  · simp only [modifiedInverseDensity, indicator_of_notMem hk, norm_zero]
    positivity

end JanetCartan.ContinuumAdjoint.DerivativeKernels
