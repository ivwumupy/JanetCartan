module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.Jets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Bounds

/-!
# Quantitative L² bound for the localized diagonal correction

The zero-order endpoint of the smoothing estimate following
`app:ch_background:eq:bg-real-symbol`, with the actual Euclidean measures.
The two finite-support estimates and Cauchy–Schwarz are reused from
`FiniteChain.Retarded.KernelSobolev`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel
open FiniteChain.Retarded.KernelSobolev
variable {n N : ℕ}

private theorem compact_kernel_norm_bound
    (t : Euclidean n → Euclidean n → ℂ)
    (ht : Continuous (Function.uncurry t)) (hts : HasCompactSupport (Function.uncurry t))
    {X Y : Set (Euclidean n)} (hX : IsCompact X) (hY : IsCompact Y)
    (hx : ∀ x y, x ∉ X → t x y = 0) (hy : ∀ x y, y ∉ Y → t x y = 0)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ x y, ‖t x y‖ ≤ A) :
    ‖compactKernelOperator (μ := volume) (ν := volume) ht hts‖ ≤
      A * compactSupportFactor volume volume Y X := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hA (compactSupportFactor_nonneg _ _ _ _))
  intro f
  have hrow (x : Euclidean n) : MemLp (t x) 2 volume :=
    memLp_of_support_bound (ht.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      hY.measurableSet hY.measure_ne_top hA (hb x) (hy x)
  have hpoint (x : Euclidean n) : ‖∫ y, t x y * f y‖ ≤
      (A * Real.sqrt (volume.real Y)) * ‖f‖ := by
    have h := norm_integral_mul_le_l2 (hrow x) (Lp.memLp f)
    rw [Lp.toLp_coeFn] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (norm_toLp_le_of_support_bound (hrow x) hY.measurableSet hY.measure_ne_top
        hA (hb x) (hy x)) (norm_nonneg _))
  have hm := memLp_compactKernel_integral_L2 (ν := volume) ht hts f
  have he : compactKernelOperator (μ := volume) (ν := volume) ht hts f = hm.toLp _ := by
    apply Lp.ext
    exact (compactKernelOperator_ae_integral ht hts f).trans hm.coeFn_toLp.symm
  rw [he]
  apply (norm_toLp_le_of_support_bound hm hX.measurableSet hX.measure_ne_top
    (mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (norm_nonneg f)) hpoint
    (fun x h ↦ by simp [hx x _ h])).trans_eq
  unfold compactSupportFactor
  ring

variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ β : Euclidean n → ℝ)
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β)

/-- Finite-support L² bound from the localized zero jet. The hypothesis is
produced, with one high norm, by
`exists_localizedDiagonalCorrectionKernel_bound_of_primitiveNorms` at order zero
(`app:ch_background:eq:bg-real-symbol`). -/
theorem norm_localizedDiagonalCorrectionOperator_le {A : ℝ} (hA : 0 ≤ A) (i j : Fin n)
    (hb : ∀ x y, ‖localizedDiagonalCorrectionKernel a J u Ω K χ β i j x y‖ ≤ A) :
    ‖localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC hcomparison
      hχ hβ hχs hβs i j‖ ≤
        A * compactSupportFactor volume volume (tsupport β) (tsupport χ) := by
  apply compact_kernel_norm_bound _ _ _ hχs hβs _ _ hA hb
  · intro x y hx
    simp [localizedDiagonalCorrectionKernel, diagonalCorrectionMask,
      image_eq_zero_of_notMem_tsupport hx]
  · intro x y hy
    simp [localizedDiagonalCorrectionKernel, diagonalCorrectionMask,
      image_eq_zero_of_notMem_tsupport hy]

/-- The Hilbert adjoint has the identical quantitative L² bound
(`app:ch_background:eq:bg-real-symbol`). Its literal kernel is identified in
`localizedDiagonalCorrectionOperator_adjoint_ae_integral`. -/
theorem norm_localizedDiagonalCorrectionOperator_adjoint_le
    {A : ℝ} (hA : 0 ≤ A) (i j : Fin n)
    (hb : ∀ x y, ‖localizedDiagonalCorrectionKernel a J u Ω K χ β i j x y‖ ≤ A) :
    ‖(localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC hcomparison
      hχ hβ hχs hβs i j).adjoint‖ ≤
        A * compactSupportFactor volume volume (tsupport β) (tsupport χ) := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact norm_localizedDiagonalCorrectionOperator_le a J u Ω K χ β he hone hC
    hcomparison hχ hβ hχs hβs hA i j hb

end JanetCartan.ContinuumRow.TransportKernel
