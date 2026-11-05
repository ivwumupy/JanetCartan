module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Integrability
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.OperatorIdentity

/-!
# Testing the regularized joint matrix kernel

Fubini is justified by primitive compact carriers for
`app:ch_regular:eq:joint-kernel-phase`. Matrix action and the input integral
commute with the full joint integral. This is an intermediate step in identifying
the literal composition; it does not identify an unregularized graph operator.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
private instance : IsNormableSpace ℂ (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (IsNormableSpace ℂ (Fin r → Fin r → ℂ))
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 256

/-- Testing the regularized joint kernel commutes with all five internal
integrations (`app:ch_regular:eq:joint-kernel-phase`). Absolute integrability is
proved from the primitive supports and continuity, not assumed of the operator. -/
theorem regularizedJointKernel_test_fubini (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A mi χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    (∫ y, (regularizedJointKernel backward S A mi mo χA χo x y).mulVec (f y)) =
      jointNormalization n • ∫ p : JointVariables (Euclidean n), ∫ y,
        (regularizedJointIntegrand backward S A mi mo χA χo x y p).mulVec (f y) := by
  have hm (y : Euclidean n) :
      (∫ p, regularizedJointIntegrand backward S A mi mo χA χo x y p).mulVec (f y) =
        ∫ p, (regularizedJointIntegrand backward S A mi mo χA χo x y p).mulVec (f y) :=
    (((sourceMatrixAction (r := r)).flip (f y)).integral_comp_comm
      (regularizedJointIntegrand_integrable backward S A mi mo χA χo
        hS hA hi ho hg hc c x y)).symm
  simp only [regularizedJointKernel, Matrix.smul_mulVec, hm, integral_smul]
  congr 1
  exact (integral_integral_swap (regularizedJointIntegrand_test_integrable
    backward S A mi mo χA χo hS hA hi ho hg hc c f hf x)).symm

/-- Exact norm of the oscillatory matrix integrand. The Frobenius matrix norm
and both physical amplitude positions are retained in the majorant consumed by
`app:ch_regular:eq:chain-tail`. -/
theorem norm_regularizedJointIntegrand (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (p : JointVariables (Euclidean n)) :
    ‖regularizedJointIntegrand backward S A mi mo χA χo x y p‖ =
      |χA p.2.1 * χo p.2.2.2 * (1 - mo (x, p.2.2.2)) * mi (y, p.2.2.1)| *
        ‖A p.1.1 p.1.2 p.2.1‖ := by
  simp only [regularizedJointIntegrand, regularizedJointAmplitude, norm_smul,
    mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- The finite channel action is controlled using its actual continuous bilinear
matrix action, retaining the dimension-dependent channel constant. Consumer:
pointwise tested-kernel majorants for `app:ch_regular:eq:chain-tail`. -/
theorem norm_regularizedJointIntegrand_mulVec_le (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (p : JointVariables (Euclidean n)) (v : Fin r → ℂ) :
    ‖(regularizedJointIntegrand backward S A mi mo χA χo x y p).mulVec v‖ ≤
      (sourceMatrixAction (r := r)).opNorm *
        (|χA p.2.1 * χo p.2.2.2 * (1 - mo (x, p.2.2.2)) * mi (y, p.2.2.1)| *
          ‖A p.1.1 p.1.2 p.2.1‖) * ‖v‖ := by
  have h := (sourceMatrixAction (r := r)).le_opNorm₂
      (regularizedJointIntegrand backward S A mi mo χA χo x y p) v
  rw [norm_regularizedJointIntegrand] at h
  exact h

end JanetCartan.FiniteChain.Graph.KernelLimits
