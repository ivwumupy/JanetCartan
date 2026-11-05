module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Compact
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Reverse.Scalar
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Reverse.Integrability

/-!
# The literal adjoint and weighted reverse graph

The compact-frequency actual adjoint is the reverse integral in
`app:ch_regular_base:eq:actual-normal-kernel`. Specializing its matrix amplitude
recovers `app:ch_regular_base:eq:actual-matrix-inverse`, with no physical source
cutoff. The normal-kernel parent retains the final normal and limiting assembly.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}

/-- Evaluation of the actual vector-valued reverse integral commutes with its
finite matrix contraction. All integrability follows from compact support and L²
input; consumed by `compactGraph_adjoint_ae_reverseIntegral`
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem reverseMatrix_integral_apply
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (f : NormalOutputL2 n r) (y : Euclidean n) (k : Fin r) :
    (∫ η, ∫ x, star (graphOscillation S x y η) •
      (A x η).conjTranspose.mulVec (fun i ↦ f i x)) k =
      ∑ i, ∫ η, ∫ x, star (graphOscillation S x y η) * star (A x η i k) * f i x := by
  have hx (η : Euclidean n) (k : Fin r) : Integrable (fun x ↦
      (star (graphOscillation S x y η) •
        (A x η).conjTranspose.mulVec (fun i ↦ f i x)) k) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, Finset.mul_sum, ← mul_assoc] using
      integrable_finsetSum Finset.univ (fun i _ ↦
        integrable_reverseEntry_mul_L2 (a := fun x η ↦ A x η i k) hS (hA i k) (hsA i k) (f i) y η)
  have he (η : Euclidean n) (k : Fin r) :
      (∫ x, star (graphOscillation S x y η) •
        (A x η).conjTranspose.mulVec (fun i ↦ f i x)) k =
        ∑ i, ∫ x, star (graphOscillation S x y η) * star (A x η i k) * f i x := by
    rw [eval_integral (hx η)]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, Finset.mul_sum, ← mul_assoc]
    exact integral_finsetSum _ (fun i _ ↦
      integrable_reverseEntry_mul_L2 (a := fun x η ↦ A x η i k) hS (hA i k) (hsA i k) (f i) y η)
  have hη (k : Fin r) : Integrable (fun η ↦
      (∫ x, star (graphOscillation S x y η) •
        (A x η).conjTranspose.mulVec (fun i ↦ f i x)) k) :=
    (integrable_finsetSum Finset.univ (fun i _ ↦
      integrable_reverseEntry_integral_L2 (a := fun x η ↦ A x η i k) hS (hA i k) (hsA i k) (f i) y)).congr
        (Eventually.of_forall fun η ↦ (he η k).symm)
  rw [eval_integral hη]
  simp_rw [he]
  exact integral_finsetSum _ (fun i _ ↦
    integrable_reverseEntry_integral_L2 (a := fun x η ↦ A x η i k) hS (hA i k) (hsA i k) (f i) y)

/-- The actual Hilbert adjoint equals the literal reverse graph, coordinatewise
almost everywhere on Euclidean volume, for every L² input
(`app:ch_regular_base:eq:actual-normal-kernel`). The factor is exactly `(2π)⁻ⁿ`
and there is no physical source cutoff. -/
theorem compactGraph_adjoint_ae_reverseIntegral
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (f : NormalOutputL2 n r) (k : Fin r) :
    ((compactGraph hS hA hsA).adjoint f) k =ᵐ[volume] fun y ↦
      (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
        star (graphOscillation S x y η) •
          (A x η).conjTranspose.mulVec (fun i ↦ f i x)) k := by
  rw [compactGraph_adjoint, blocks_apply]
  have he (i : Fin r) := graphBlock_adjoint_ae_reverseIntegral (a := fun x η ↦ A x η i k) hS
    (hA i k) (hsA i k) (f i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    (fourierL2 n).symm ((compactKernelOperator (μ := volume) (ν := volume)
      (continuous_frequencyEntry (a := fun x η ↦ A x η i k) hS (hA i k))
      (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))).adjoint (f i))),
    ae_all_iff.mpr he] with y hy he
  change (∑ i, (fourierL2 n).symm ((compactKernelOperator (μ := volume) (ν := volume)
    (continuous_frequencyEntry (a := fun x η ↦ A x η i k) hS (hA i k))
    (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))).adjoint (f i))) y = _
  rw [hy]
  simp_rw [he]
  simp only [Pi.smul_apply, smul_eq_mul, reverseMatrix_integral_apply hS hA hsA,
    Finset.mul_sum]

/-- The weighted forward amplitude has precisely the weighted reverse graph as
its actual adjoint (`app:ch_regular_base:eq:actual-matrix-inverse`). Continuity
and joint compact support are required of the full cut amplitude. No source or
target position cutoff is inserted in this pure reverse formula. -/
theorem compactGraph_adjoint_ae_weightedReverseGraph
    (hS : Continuous (Function.uncurry S))
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ)
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦
      ((χg p.2 : ℂ) • weightedForwardAmplitude (phaseJacobian S p.1 p.2)
        (U p.1 p.2)) i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      ((χg p.2 : ℂ) • weightedForwardAmplitude (phaseJacobian S p.1 p.2)
        (U p.1 p.2)) i k))
    (f : NormalOutputL2 n r) (k : Fin r) :
    ((compactGraph (A := fun x η ↦ (χg η : ℂ) •
      weightedForwardAmplitude (phaseJacobian S x η) (U x η)) hS hA hsA).adjoint f) k =ᵐ[volume] fun y ↦
      weightedReverseGraph S U (fun _ ↦ 1) (fun _ ↦ 1) χg (fun x i ↦ f i x) y k := by
  convert compactGraph_adjoint_ae_reverseIntegral (A := fun x η ↦ (χg η : ℂ) •
    weightedForwardAmplitude (phaseJacobian S x η) (U x η)) hS hA hsA f k using 1
  simp only [Matrix.conjTranspose_smul, weightedForwardAmplitude_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mulVec, smul_smul,
    weightedReverseGraph, Complex.ofReal_one, one_smul, one_mul]

end JanetCartan.FourierIntegral.NormalKernel
