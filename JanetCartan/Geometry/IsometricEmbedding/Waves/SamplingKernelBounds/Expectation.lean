module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Expectation.Blocks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis

/-!
# Whole-output sampling expectation bounds

The conditional expectation and trace deduction for
`app:ch_waves:eq:sampling-prefix-normal` and
`app:ch_waves:eq:sampling-operator-bounds`. The input is the actual finite Hilbert
sum `RawInputRealization.Input n radius`; the output is the full Euclidean L²
space `Output n`, without projection. A countable Hilbert basis of that full
output is used for the trace.

The parent must instantiate continuity, Hilbert–Schmidt summability, continuity
of its squared norm, and the uniform row bound using the annular operators and
finite-row deduction. The actual weights, color labels and nodes are retained.
No expectation integrability, compactness, or trace estimate is assumed. The
stronger bound `‖E_h‖ ≤ C` requires the independent normal-amplitude argument.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace JanetCartan.SamplingKernelBounds.Expectation
open SeparatedSampling Sampling RawInputRealization

/-- The complete conditional trace/compactness deduction on the original input
and full output, consumed by the parent sampling-kernel construction
(`app:ch_waves:eq:sampling-operator-bounds`). The parent must discharge all row
hypotheses; the scalar mass estimate is proved from the literal shift law. -/
theorem sampling_expectation_bounds
    {n p : ℕ} {J ι κ : Type*} [Fintype J] [Countable κ] {radius : J → ℝ}
    (b : HilbertBasis ι ℂ (Input n radius)) (a : HilbertBasis κ ℂ (Output n))
    {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}
    (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h) (hh₁ : h ≤ 1)
    (T : (Fin 3 → Fin (p + 1)) → Point → Input n radius →L[ℂ] Output n)
    (hTc : ∀ c, Continuous (T c)) (hTS : ∀ c z, IsHilbertSchmidt b (T c z))
    (hSq : ∀ c, Continuous (fun z ↦ hilbertSchmidtSq b (T c z)))
    (Λ C_HS : ℝ)
    (hHS : ∀ c z, hilbertSchmidtSq b (T c z) ≤ C_HS * Λ ^ n) :
    let D := blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq
    (∀ q : ShiftIndex p B h,
      Integrable (fun z ↦ (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z))) ∧
    (∀ q : ShiftIndex p B h,
      Integrable (fun z ↦ (ψ z * blockWeight w h q z) * hilbertSchmidtSq b (T (color p q) z))) ∧
    0 ≤ D.expectation ∧ IsCompactOperator D.expectation ∧
    (positiveTrace a D.expectation =
      ∑ q : ShiftIndex p B h, ∫ z,
        (ψ z * blockWeight w h q z) * hilbertSchmidtSq b (T (color p q) z)) ∧
    positiveTrace a D.expectation ≤
      (C_HS * (countConstant p B * (P * W ^ 3))) * Λ ^ n ∧
    (∀ (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U],
      Complex.re (LinearMap.trace ℂ U (finiteCompression U D.expectation).toLinearMap) ≤
        (C_HS * (countConstant p B * (P * W ^ 3))) * Λ ^ n) := by
  dsimp only
  let D := blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq
  refine ⟨D.integrable_normal, D.integrable_weightedTrace, D.expectation_nonneg,
    D.expectation_compact, D.trace_eq a, ?_, ?_⟩
  · exact blockFamily_trace_le_scale b hw hψ hψc hwc T hTc hTS hSq a hh hh₁ n Λ C_HS hHS
  · intro U _
    exact (D.trace_finiteCompression_le_trace a U).trans
      (blockFamily_trace_le_scale b hw hψ hψc hwc T hTc hTS hSq a hh hh₁ n Λ C_HS hHS)

end JanetCartan.SamplingKernelBounds.Expectation
