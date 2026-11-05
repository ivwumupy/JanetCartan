module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.FourierBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.Kernel

/-!
# All-data integer smoothing for the literal diagonal correction

The operator and its literal Hilbert adjoint in
`app:ch_background:eq:bg-real-symbol` gain every requested integer order.
This leaf consumes the exact localized jets produced in `PrimitiveJets`;
`PrimitiveBounds` instantiates them and the smoothness from primitive data.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction Pseudodifferential
open FiniteChain.Retarded.KernelSobolev
variable {n N : ℕ}
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ β : Euclidean n → ℝ)
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β)

/-- The actual diagonal correction gains integer order `s` on every Euclidean
L² input. The localized jet premise is produced by
`exists_localizedDiagonalCorrectionKernel_bound_of_primitiveNorms`
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionOperator_sobolev_of_jets
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A) (i j : Fin n)
    (hb : ∀ r ≤ s, ∀ p, ‖iteratedFDeriv ℝ r (Function.uncurry
      (localizedDiagonalCorrectionKernel a J u Ω K χ β i j)) p‖ ≤ A)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    let T := localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC
      hcomparison hχ hβ hχs hβs i j
    MemFourierSobolev (s : ℝ) (T f) ∧
      fourierSobolevNorm (s : ℝ) (T f) ≤
        ((1 + (n : ℝ)) ^ s * A *
          compactSupportFactor volume volume (tsupport β) (tsupport χ)) * ‖f‖ := by
  apply PrincipalSobolev.compactKernel_fourierSobolev_bound _
    (localizedDiagonalCorrectionKernel_contDiff a J u Ω K χ β he hone hC
      hcomparison hχ hβ i j) hχs hβs _ _ s hA hb _
    (localizedDiagonalCorrectionOperator_ae_integral a J u Ω K χ β he hone hC
      hcomparison hχ hβ hχs hβs i j) f
  · intro x y hx
    simp [localizedDiagonalCorrectionKernel, diagonalCorrectionMask,
      image_eq_zero_of_notMem_tsupport hx]
  · intro x y hy
    simp [localizedDiagonalCorrectionKernel, diagonalCorrectionMask,
      image_eq_zero_of_notMem_tsupport hy]

/-- The literal Hilbert adjoint has the same gain, using the conjugated kernel
with positions and matrix indices exchanged. Both compact support factors
use Euclidean Lebesgue volume (`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionOperator_adjoint_sobolev_of_jets
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A) (i j : Fin n)
    (hb : ∀ r ≤ s, ∀ p, ‖iteratedFDeriv ℝ r (Function.uncurry
      (localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j)) p‖ ≤ A)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    let T := localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC
      hcomparison hχ hβ hχs hβs j i
    MemFourierSobolev (s : ℝ) (T.adjoint f) ∧
      fourierSobolevNorm (s : ℝ) (T.adjoint f) ≤
        ((1 + (n : ℝ)) ^ s * A *
          compactSupportFactor volume volume (tsupport χ) (tsupport β)) * ‖f‖ := by
  apply PrincipalSobolev.compactKernel_fourierSobolev_bound _
    (localizedDiagonalCorrectionAdjointKernel_contDiff a J u Ω K χ β he hone hC
      hcomparison hχ hβ i j) hβs hχs _ _ s hA hb _
    (localizedDiagonalCorrectionOperator_adjoint_ae_integral a J u Ω K χ β he hone hC
      hcomparison hχ hβ hχs hβs i j) f
  · intro x y hx
    simp [localizedDiagonalCorrectionAdjointKernel_eq, diagonalCorrectionMask,
      image_eq_zero_of_notMem_tsupport hx]
  · intro x y hy
    simp [localizedDiagonalCorrectionAdjointKernel_eq, diagonalCorrectionMask,
      image_eq_zero_of_notMem_tsupport hy]

end JanetCartan.ContinuumRow.TransportKernel
