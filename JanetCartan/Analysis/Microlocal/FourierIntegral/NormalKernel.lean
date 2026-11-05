module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Literal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Reverse
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Limits

/-!
# Pure graph normal kernels

For `app:ch_regular_base:eq:actual-normal-kernel` and the cross-product sentence
following `app:ch_regular_base:eq:actual-normal-amplitude`, this module assembles
the actual Euclidean L² graph maps, their literal forward and adjoint integrals,
and their pure cross-normal kernel. The weighted specialization uses
`χ_g j_S U⁻*` and recovers the literal `weightedReverseGraph`.

The construction assumes a continuous real phase (in particular, a smooth phase
suffices) and continuous jointly compactly supported amplitude entries. The
forward iterated Bochner formula holds on L¹ ∩ L²; the constructed maps, their
literal adjoints, and the normal formula act on every L² input. All measures are
Euclidean Lebesgue measures, with physical covectors `η = 2πξ` and factor `(2π)⁻ⁿ`.
There is no physical source cutoff.

`compactGraph_cross_tested_limit_amplitudes` supplies the limit-level identity
on continuous compactly supported tensor tests, including smooth such tests.
Its additional inputs are strong L² convergence of the actual adjoints on the
tests, a.e. convergence of the tested frequency densities, and an integrable
majorant. The finite pairing and Fubini identities are proved, not assumed.

The phase and geometry producers `jc-hamilton-phase` and
`jc-compatible-phase-geometry` must supply the phase/amplitude hypotheses.
Consumers `jc-finite-fio-calculus` and `jc-regular-sector` must instantiate them
and supply the limiting operators, compact regularizations, convergence, and
domination before applying the limit theorem to unregularized operators. This
module proves the stated conditional deductions, not that existence step or
the full finite calculus theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ}

/-- Construct the two actual graph maps together with their literal forward
formulas, Hilbert adjoints, and pure cross-normal kernel. This assembles
`app:ch_regular_base:eq:actual-normal-kernel` and its cross variant for the finite
FIO calculus and regular-sector consumers. Every operator is constructed from
the phase and compact amplitudes; no operator identity is an input. -/
theorem exists_graph_cross_normal
    {A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k)) :
    ∃ T_A T_B : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      (∀ (f : NormalOutputL2 n r), (∀ k, Integrable (f k : Euclidean n → ℂ)) →
        ∀ i, (T_A f) i =ᵐ[volume] fun x ↦
          graphOperator S (fun x _ η ↦ A x η) (fun y k ↦ f k y) x i) ∧
      (∀ (f : NormalOutputL2 n r), (∀ k, Integrable (f k : Euclidean n → ℂ)) →
        ∀ i, (T_B f) i =ᵐ[volume] fun x ↦
          graphOperator S (fun x _ η ↦ B x η) (fun y k ↦ f k y) x i) ∧
      (∀ (f : NormalOutputL2 n r) k, (T_A.adjoint f) k =ᵐ[volume] fun y ↦
        (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
          star (graphOscillation S x y η) •
            (A x η).conjTranspose.mulVec (fun i ↦ f i x)) k) ∧
      (∀ (f : NormalOutputL2 n r) k, (T_B.adjoint f) k =ᵐ[volume] fun y ↦
        (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
          star (graphOscillation S x y η) •
            (B x η).conjTranspose.mulVec (fun i ↦ f i x)) k) ∧
      (∀ (f : NormalOutputL2 n r) i,
        (T_A (T_B.adjoint f)) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y,
          (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
            Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
              (A x η * (B y η).conjTranspose) i j) * f j y) := by
  exact ⟨compactGraph hS hA hsA, compactGraph hS hB hsB,
    compactGraph_ae_graphOperator hS hA hsA,
    compactGraph_ae_graphOperator hS hB hsB,
    compactGraph_adjoint_ae_reverseIntegral hS hA hsA,
    compactGraph_adjoint_ae_reverseIntegral hS hB hsB,
    compactGraph_cross_ae hS hA hsA hB hsB⟩

/-- The weighted pure graph exists on the actual Euclidean L² space, its adjoint
is the literal weighted reverse graph with both spatial cutoffs equal to one,
and its normal retains the square of the frequency cutoff. This is the weighted
case of `app:ch_regular_base:eq:actual-normal-kernel`, using the weight in
`app:ch_regular_base:eq:actual-matrix-inverse`. The full weighted amplitude must
satisfy the displayed continuity and compact-support hypotheses; this theorem
does not produce phase geometry or assert an inverse estimate. -/
theorem exists_weightedGraph_normal
    (hS : Continuous (Function.uncurry S))
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ)
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦
      ((χg p.2 : ℂ) • weightedForwardAmplitude (phaseJacobian S p.1 p.2)
        (U p.1 p.2)) i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      ((χg p.2 : ℂ) • weightedForwardAmplitude (phaseJacobian S p.1 p.2)
        (U p.1 p.2)) i k)) :
    ∃ T : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      (∀ (f : NormalOutputL2 n r), (∀ k, Integrable (f k : Euclidean n → ℂ)) →
        ∀ i, (T f) i =ᵐ[volume] fun x ↦
          graphOperator S (fun x _ η ↦ (χg η : ℂ) •
            weightedForwardAmplitude (phaseJacobian S x η) (U x η))
              (fun y k ↦ f k y) x i) ∧
      (∀ (f : NormalOutputL2 n r) k, (T.adjoint f) k =ᵐ[volume] fun y ↦
        weightedReverseGraph S U (fun _ ↦ 1) (fun _ ↦ 1) χg (fun x i ↦ f i x) y k) ∧
      (∀ (f : NormalOutputL2 n r) i,
        (T (T.adjoint f)) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y,
          (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
            Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
              ((χg η : ℂ) ^ 2 •
                (weightedForwardAmplitude (phaseJacobian S x η) (U x η) *
                  reverseWeight (phaseJacobian S y η) (U y η))) i j) * f j y) := by
  let A (x η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
    (χg η : ℂ) • weightedForwardAmplitude (phaseJacobian S x η) (U x η)
  refine ⟨compactGraph (A := A) hS hA hsA,
    compactGraph_ae_graphOperator (A := A) hS hA hsA,
    compactGraph_adjoint_ae_weightedReverseGraph hS U χg hA hsA, ?_⟩
  intro f i
  simpa only [A, Matrix.conjTranspose_smul, weightedForwardAmplitude_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two] using
      compactGraph_cross_ae (A := A) (B := A) hS hA hsA hA hsA f i

end JanetCartan.FourierIntegral.NormalKernel
