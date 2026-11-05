module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Sampled

/-!
# Whole-output hypotheses for the sampling concentration step

The compactness, continuity, centered-block norm and finite orthonormal trace
inputs to `HilbertOperatorBernstein` are consequences of the actual kernels.
This module proves no concentration or successful-sample selection, and does
not supply the stronger order-one expectation norm bound.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.SamplingKernelBounds

private theorem diagonal_le_of_compression_trace {n : ℕ}
    (A : Output n →L[ℂ] Output n) (τ : ℝ)
    (h : ∀ (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U],
      Complex.re (LinearMap.trace ℂ U (finiteCompression U A).toLinearMap) ≤ τ)
    (m : ℕ) (e : Fin m → Output n) (he : Orthonormal ℂ e) :
    ∑ j, Complex.re ⟪e j, A (e j)⟫_ℂ ≤ τ := by
  classical
  let U := Submodule.span ℂ (↑(Finset.univ.image e) : Set (Output n))
  let b := OrthonormalBasis.span he Finset.univ
  have hh := h U
  rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum] at hh
  change (∑ j, Complex.re (inner ℂ (b j) (finiteCompression U A (b j)))) ≤ τ at hh
  have hh' : (∑ j, Complex.re ⟪(b j : Output n), A (b j : Output n)⟫_ℂ) ≤ τ :=
    (Finset.sum_congr rfl (fun j _ ↦ congrArg Complex.re
      (finiteCompression_inner U A (b j) (b j)))).symm.trans_le hh
  simpa [b] using hh'

namespace BandKernelData
open RawInputRealization SeparatedSampling Sampling
variable {n J p : ℕ}
  (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
  {ι δ : Type*} [Countable ι] (a : HilbertBasis ι ℂ (Output n))
  (b : HilbertBasis δ ℂ (Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)))
  (s : Finset (Fin J)) {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}
  (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
  (hψc : Continuous ψ) (hwc : Continuous w)

/-- The exact finite-orthonormal-diagonal trace input to
`HilbertOperatorBernstein`, uniform over the whole output and every prefix
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem samplingFamily_diagonal_le (hn : 1 ≤ n) (hh : 0 < h) (hh₁ : h ≤ 1)
    {C_ceiling Λ : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ)
    (m : ℕ) (e : Fin m → Output n) (he : Orthonormal ℂ e) :
    ∑ j, Complex.re ⟪e j,
      (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation (e j)⟫_ℂ ≤
      ((D.squaredKernelConstant * C_ceiling ^ n) *
        (countConstant p B * (P * W ^ 3))) * Λ ^ n :=
  diagonal_le_of_compression_trace _ _
    (fun U _ ↦ D.samplingFamily_compression_trace_le a b s hw hψ hψc hwc hn hh hh₁ hceil U)
    m e he

/-- Multiplication by the block bound supplies the diagonal trace bound for
the variance upper operator `R E_h`; it supplies no bound on `‖E_h‖`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem samplingFamily_variance_diagonal_le (hn : 1 ≤ n) (hh : 0 < h) (hh₁ : h ≤ 1)
    {C_ceiling Λ R : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) (hR : 0 ≤ R)
    (m : ℕ) (e : Fin m → Output n) (he : Orthonormal ℂ e) :
    ∑ j, Complex.re ⟪e j,
      (R • (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation) (e j)⟫_ℂ ≤
      R * (((D.squaredKernelConstant * C_ceiling ^ n) *
        (countConstant p B * (P * W ^ 3))) * Λ ^ n) := by
  change (∑ j, diagonalCLM (e j)
    (R • (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation)) ≤ _
  simp only [map_smul, smul_eq_mul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (D.samplingFamily_diagonal_le a b s hw hψ hψc hwc hn hh hh₁ hceil m e he) hR


include a hw hψ hψc hwc in
omit b in
/-- Centered literal blocks are compact and satisfy the required bound, with
all operator-family premises discharged by the actual kernels and the sharp
single-band oscillatory input (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem centered_samplingBlock_bounds {C_op C_ceiling Λ : ℝ} (hC : 0 ≤ C_op)
    (hband : ∀ i c z, ‖D.operator ((2 : ℝ) ^ i.val) (i, (c, z))‖ ^ 2 ≤
      C_op * (2 : ℝ) ^ i.val)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) (hh : 0 ≤ h)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Lattice) (U : Ω → Point) (hU : Measurable U) (ω : Ω) :
    IsCompactOperator
      (atomicBlock p ψ w h (fun c z ↦ D.dyadicPrefix s (c, z)) q (U ω) -
        ∫ ω', atomicBlock p ψ w h (fun c z ↦ D.dyadicPrefix s (c, z)) q (U ω') ∂μ) ∧
    ‖atomicBlock p ψ w h (fun c z ↦ D.dyadicPrefix s (c, z)) q (U ω) -
        ∫ ω', atomicBlock p ψ w h (fun c z ↦ D.dyadicPrefix s (c, z)) q (U ω') ∂μ‖ ≤
      (nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * ((C_op * C_ceiling) * Λ) := by
  have hc c : Continuous (fun z ↦ D.dyadicPrefix s (c, z)) :=
    (D.continuous_dyadicPrefix s).comp (continuous_const.prodMk continuous_id)
  have hb c z := D.norm_dyadicPrefix_sq_le s (c, z) hC (fun i ↦ hband i c z) hceil
  refine ⟨(D.isCompactOperator_samplingBlock a s q (U ω)).sub ?_,
    norm_centered_atomicBlock_le hw hψ hh _ hb μ q U ω⟩
  exact isCompactOperator_integral _
    (integrable_atomicBlock hw hψ hwc hψc hh _ hc hb μ q U hU)
    (Filter.Eventually.of_forall (fun ω' ↦ D.isCompactOperator_samplingBlock a s q (U ω')))

end BandKernelData
end JanetCartan.SamplingKernelBounds
