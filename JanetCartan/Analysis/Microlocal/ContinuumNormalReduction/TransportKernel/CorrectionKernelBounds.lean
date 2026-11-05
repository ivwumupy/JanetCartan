module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.CorrectionKernelBounds.Kernel

/-!
# Quantitative jets of the literal completion-error kernel

The bounded-frequency error following `app:ch_background:eq:bg-symbol` and
`app:ch_background:eq:bg-real-symbol` has uniformly bounded joint physical jets.
The explicit constant depends only on dimension, order, and the fixed frequency
radius. Lebesgue measure and the prefactor `(2π)⁻ⁿ` are retained exactly.

The amplitude inputs are produced by
`exists_reflectedCompletionError_bound_of_primitiveNorms` in `CompletionBounds`.
They enter linearly, so its single high norm and fixed shift two are preserved.
The parent transport normal construction must instantiate those primitive inputs
and assemble the operator estimates; no Sobolev gain is assumed here.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ComplexConjugate
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n N : ℕ}

section Completion
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hhigh : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)

include he hhigh hC hcomparison

/-- All physical jets of the actual completion-error integrand are absolutely
Lebesgue integrable (`app:ch_background:eq:bg-symbol`). -/
theorem integrable_completionErrorKernel_jet (i j : Fin n) (r : ℕ)
    (x : Euclidean n × Euclidean n) :
    Integrable (fun k ↦ iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (y.1 - y.2) k) *
        (reflectedCompletionError a J u Ω K (y.1, y.2, k) i j : ℂ)) x) :=
  integrable_correctionIntegrand_jet he
    (fun p hp ↦ reflectedCompletionError_eq_zero_of_large_frequency
      a J u Ω K hhigh hC hcomparison p hp.le) i j r x

/-- All physical derivatives of the actual normalized correction kernel are
the normalized Lebesgue integrals of the physical integrand derivatives
(`app:ch_background:eq:bg-symbol`). -/
theorem iteratedFDeriv_completionErrorKernel (i j : Fin n) (r : ℕ)
    (x : Euclidean n × Euclidean n) :
    iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
      completionErrorKernel a J u Ω K i j y.1 y.2) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ k,
        iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
          NormalComparison.oscillatoryFactor 1 (inner ℝ (y.1 - y.2) k) *
            (reflectedCompletionError a J u Ω K (y.1, y.2, k) i j : ℂ)) x :=
  iteratedFDeriv_normalizedCorrectionIntegral he
    (fun p hp ↦ reflectedCompletionError_eq_zero_of_large_frequency
      a J u Ω K hhigh hC hcomparison p hp.le) i j r x

/-- The finite joint physical derivative estimate for the actual normalized
Lebesgue kernel. Its constant is independent of both positions and geometry;
only amplitude jets through `r` are consumed (`app:ch_background:eq:bg-symbol`). -/
theorem norm_iteratedFDeriv_completionErrorKernel_le
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n) {A : ℝ}
    (hb : ∀ k, ‖k‖ ≤ max 2 (2 * C) → ∀ l ≤ r,
      ‖iteratedFDeriv ℝ l (reflectedCompletionError a J u Ω K) (x.1, x.2, k)‖ ≤ A) :
    ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
      completionErrorKernel a J u Ω K i j y.1 y.2) x‖ ≤
      correctionKernelJetConstant n r (max 2 (2 * C)) * A :=
  norm_iteratedFDeriv_compactCorrectionKernel_le he
    (fun p hp ↦ reflectedCompletionError_eq_zero_of_large_frequency
      a J u Ω K hhigh hC hcomparison p hp.le) i j r x hb

/-- The literal conjugate transpose has the identical finite jet constant.
The amplitude-kernel identity and the exact transposed-amplitude jet identity
from `CompletionBounds` discharge the adjoint step
(`app:ch_background:eq:bg-real-symbol`). -/
theorem norm_iteratedFDeriv_completionErrorKernel_adjoint_le
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n) {A : ℝ}
    (hb : ∀ k, ‖k‖ ≤ max 2 (2 * C) → ∀ l ≤ r,
      ‖iteratedFDeriv ℝ l (reflectedCompletionError a J u Ω K) (x.2, x.1, k)‖ ≤ A) :
    ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
      conj (completionErrorKernel a J u Ω K j i y.2 y.1)) x‖ ≤
      correctionKernelJetConstant n r (max 2 (2 * C)) * A := by
  let f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ :=
    fun q ↦ (reflectedCompletionError a J u Ω K (q.2.1, q.1, q.2.2)).transpose
  have hf : ContDiff ℝ ∞ f :=
    (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap.toContinuousLinearMap.contDiff.comp
      (he.comp (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)))
  have hs : ∀ p : TransportSymbol.Variables n, max 2 (2 * C) < ‖p.2.2‖ → f p = 0 := by
    intro p hp
    simp [f, reflectedCompletionError_eq_zero_of_large_frequency
      a J u Ω K hhigh hC hcomparison (p.2.1, p.1, p.2.2) hp.le]
  have hb' (k : Euclidean n) (hk : ‖k‖ ≤ max 2 (2 * C)) (l : ℕ) (hl : l ≤ r) :
      ‖iteratedFDeriv ℝ l f (x.1, x.2, k)‖ ≤ A := by
    rw [show f = (fun q : TransportSymbol.Variables n ↦
      (reflectedCompletionError a J u Ω K (q.2.1, q.1, q.2.2)).transpose) from rfl,
      norm_iteratedFDeriv_adjoint_reflectedCompletionError]
    exact hb k hk l hl
  have hid : (fun y : Euclidean n × Euclidean n ↦
      conj (completionErrorKernel a J u Ω K j i y.2 y.1)) =
      (fun y : Euclidean n × Euclidean n ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ *
        ∫ k, correctionIntegrand f i j (y, k)) := by
    funext y
    rw [completionErrorKernel_adjoint_eq_amplitudeKernel,
      amplitudeKernel_eq_physicalFrequency_integral
        (fun x y k ↦ (reflectedCompletionError a J u Ω K (y, x, k) j i : ℂ))]
    rfl
  rw [hid]
  exact norm_iteratedFDeriv_compactCorrectionKernel_le hf hs i j r x hb'

/-- Uniform finite jets of both literal kernels with a single common amplitude
bound. Substituting `A = C₀ * H` from
`exists_reflectedCompletionError_bound_of_primitiveNorms` preserves one factor
`H` and its fixed shift; the parent construction supplies that instantiation
(`app:ch_background:eq:bg-symbol`, `app:ch_background:eq:bg-real-symbol`). -/
theorem completionErrorKernel_jet_bounds_of_amplitude_bounds (s : ℕ) {A : ℝ}
    (hb : ∀ p : TransportSymbol.Variables n, ‖p.2.2‖ ≤ max 2 (2 * C) →
      ∀ l ≤ s, ‖iteratedFDeriv ℝ l (reflectedCompletionError a J u Ω K) p‖ ≤ A) :
    ∀ r ≤ s, ∀ i j : Fin n, ∀ x : Euclidean n × Euclidean n,
      ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
        completionErrorKernel a J u Ω K i j y.1 y.2) x‖ ≤
          correctionKernelJetConstant n r (max 2 (2 * C)) * A ∧
      ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
        conj (completionErrorKernel a J u Ω K j i y.2 y.1)) x‖ ≤
          correctionKernelJetConstant n r (max 2 (2 * C)) * A := by
  intro r hr i j x
  exact ⟨norm_iteratedFDeriv_completionErrorKernel_le a J u Ω K he hhigh hC hcomparison
      i j r x (fun k hk l hl ↦ hb (x.1, x.2, k) hk l (hl.trans hr)),
    norm_iteratedFDeriv_completionErrorKernel_adjoint_le a J u Ω K he hhigh hC hcomparison
      i j r x (fun k hk l hl ↦ hb (x.2, x.1, k) hk l (hl.trans hr))⟩

end Completion
end JanetCartan.ContinuumRow.TransportKernel
