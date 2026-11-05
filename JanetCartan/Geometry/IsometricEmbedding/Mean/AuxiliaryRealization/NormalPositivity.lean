module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Output

/-!
# Positivity of the original cut auxiliary normal

The auxiliary term in `main:prop:canonical` is the actual image-plus-exterior
normal, with both Fourier cutoffs before the physical source multiplier.
Its positivity follows from the squared symbol on the original real L²
space. This discharges the auxiliary-positivity input of the canonical
comparison estimates without replacing the auxiliary channel or its masks.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan.AuxiliaryRealization

open ContinuumRow RawCutoffBounds

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The original real L² Fourier analysis for the raw auxiliary multiplier
in `app:ch_background:defn:bg-mixed`. -/
private def cutoffL2Analysis : PeriodicL2 n F →ₗᵢ[ℝ] PeriodicFourierL2 n F :=
  (PeriodicSobolevSpace.analysisIsometry 0).comp
    PeriodicSobolevSpace.zeroEquivL2.symm.toLinearIsometry

/-- The analysis retains the original coefficient convention of
`app:ch_background:defn:bg-mixed` at each frequency. -/
private theorem cutoffL2Analysis_apply (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    cutoffL2Analysis u k = periodicL2FourierCoeff k u := by
  change periodicSobolevWeight 0 k • periodicL2FourierCoeff k u = _
  simp [periodicSobolevWeight]

/-- The literal squared raw Fourier cutoff is positive on all of the
original real L² space (`app:ch_background:defn:bg-mixed`). No regularity
of the input or physical output cutoff is used. -/
theorem auxiliarySquaredCutoff_inner_nonneg {K : ℝ} (hK : 1 ≤ K)
    (u : PeriodicL2 n F) :
    0 ≤ ⟪auxiliarySquaredCutoffCLM hK u, u⟫ := by
  rw [← cutoffL2Analysis.inner_map_map, lp.inner_eq_tsum]
  apply tsum_nonneg
  intro k
  rw [cutoffL2Analysis_apply, cutoffL2Analysis_apply,
    auxiliarySquaredCutoffCLM_apply,
    auxiliarySquaredCutoff_coeff (zero_lt_one.trans_le hK), real_inner_smul_left]
  exact mul_nonneg (sq_nonneg _) real_inner_self_nonneg

/-- Both original auxiliary components have nonnegative energy
(`main:prop:canonical`, `app:ch_background:defn:bg-mixed`). In particular,
the exterior summand remains present on the whole output torus. This is
the actual auxiliary term consumed by `completeCanonicalNormal`. -/
theorem cutAuxiliaryNormal_inner_nonneg
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (u : OutputL2 n) :
    0 ≤ ⟪AuxiliaryRawBand.cutAuxiliaryNormal c χmeas χsrc ψ hK u, u⟫ := by
  simp only [AuxiliaryRawBand.cutAuxiliaryNormal, add_apply,
    ContinuousLinearMap.comp_apply, inner_add_left]
  rw [← ContinuousLinearMap.adjoint_inner_right (imageChannel c χmeas χsrc),
    ← ContinuousLinearMap.adjoint_inner_right (exteriorChannel ψ), exteriorChannel_adjoint]
  exact add_nonneg (auxiliarySquaredCutoff_inner_nonneg hK _)
    (auxiliarySquaredCutoff_inner_nonneg hK _)

end JanetCartan.AuxiliaryRealization
