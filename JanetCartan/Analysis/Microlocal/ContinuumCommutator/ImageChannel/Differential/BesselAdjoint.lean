module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.BesselOperators

/-!
# Actual adjoints of the constant image factors

The finite normal factorization in `app:ch_background:eq:bg-commutator`
uses the Hilbert adjoints of the literal `J` and `Dᵢ J` factors. The former
is already self-adjoint; the latter is skew-adjoint by its real-pair Fourier
symbol, with the original physical `2π` normalization.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open ContinuumRow PeriodicSobolevSpace

variable {n : ℕ}

private def l2Analysis : OutputL2 n →ₗᵢ[ℝ] PeriodicFourierL2 n (Euclidean n) :=
  (analysisIsometry 0).comp zeroEquivL2.symm.toLinearIsometry

private theorem l2Analysis_apply (u : OutputL2 n) (k : Fin n → ℤ) :
    l2Analysis u k = periodicL2FourierCoeff k u := by
  change periodicSobolevWeight 0 k • periodicL2FourierCoeff k u = _
  simp [periodicSobolevWeight]

/-- The derivative Bessel factor is skew-symmetric on the original real L²
space (`app:ch_background:eq:bg-commutator`). -/
theorem derivativeBessel_inner (i : Fin n) (u v : OutputL2 n) :
    ⟪derivativeBessel i u, v⟫ = -⟪u, derivativeBessel i v⟫ := by
  rw [← l2Analysis.inner_map_map (derivativeBessel i u) v,
    ← l2Analysis.inner_map_map u (derivativeBessel i v),
    lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
  apply tsum_congr
  intro k
  simp only [l2Analysis_apply, WithLp.prod_inner_apply, periodicL2FourierCoeff_apply,
    fourierCoeff_derivativeBessel,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The literal Hilbert adjoint of `Dᵢ J` is `-Dᵢ J`; there is no formal
adjoint premise (`app:ch_background:eq:bg-commutator`). -/
theorem derivativeBessel_adjoint (i : Fin n) :
    (derivativeBessel i).adjoint = -derivativeBessel i := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [neg_apply, inner_neg_left,
    derivativeBessel_inner, neg_neg]

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
