module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Fubini
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The limiting action of summable graph kernel shells

The zeroth-output-jet bound for `app:ch_regular:eq:chain-tail` is an explicit
conditional input, to be supplied by `jc-graph-factor-kernel-estimates` and
instantiated by the parent localization construction. From it we prove actual
convergence on integrable test inputs. The shell index includes bounded
frequencies and all source shoulders; no part of the kernel is discarded.
No compact output support of the regularized identity kernels is needed here.
This test-input limit alone is not the Sobolev extension or the factor estimate.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Measurability of the actual integrated matrix kernel in its source base,
needed for shell summation in `app:ch_regular:eq:chain-tail`. -/
theorem regularizedJointKernel_aestronglyMeasurable (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo) (x : Euclidean n) :
    AEStronglyMeasurable (regularizedJointKernel backward S A mi mo χA χo x) := by
  have hcont : Continuous (fun q : Euclidean n × JointVariables (Euclidean n) =>
      regularizedJointIntegrand backward S A mi mo χA χo x q.1 q.2) :=
    (regularizedJointIntegrand_continuous backward S A mi mo χA χo hS hA hi ho hg hc).comp
      (f := fun q : Euclidean n × JointVariables (Euclidean n) => ((x, q.1), q.2))
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hmeas : StronglyMeasurable (fun y => ∫ p,
      regularizedJointIntegrand backward S A mi mo χA χo x y p) :=
    hcont.stronglyMeasurable.integral_prod_right
  exact (hmeas.const_smul (jointNormalization n)).aestronglyMeasurable

/-- Summable zeroth-output-jet bounds imply convergence to the integral of the
actual summed matrix kernel. The finite channel action retains its operator
norm, and each shell retains both amplitude positions and `1-mo`.
Consumer: test-input identification for `app:ch_regular:eq:chain-tail`. -/
theorem hasSum_regularizedJointKernel_test {ι : Type*} [Countable ι]
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ι → Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ j, Continuous (χo j))
    (C : ι → ℝ) (hs : Summable C)
    (hb : ∀ j x y, ‖regularizedJointKernel backward S A mi mo (χA j) (χo j) x y‖ ≤ C j)
    (f : Euclidean n → Fin r → ℂ) (hf : Integrable f) (x : Euclidean n) :
    HasSum (fun j => ∫ y,
      (regularizedJointKernel backward S A mi mo (χA j) (χo j) x y).mulVec (f y))
      (∫ y, (∑' j, regularizedJointKernel backward S A mi mo (χA j) (χo j) x y).mulVec
        (f y)) := by
  let K := fun j => regularizedJointKernel backward S A mi mo (χA j) (χo j) x
  let L := sourceMatrixAction (r := r)
  apply hasSum_integral_of_dominated_convergence
    (fun j y => (L.opNorm * C j) * ‖f y‖)
  · intro j
    exact L.continuous₂.comp_aestronglyMeasurable
      ((regularizedJointKernel_aestronglyMeasurable backward S A mi mo (χA j) (χo j)
        hS hA hi ho (hg j) (hc j) x).prodMk hf.aestronglyMeasurable)
  · intro j
    filter_upwards [] with y
    exact (L.le_opNorm₂ (K j y) (f y)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb j x y) L.opNorm_nonneg) (norm_nonneg _))
  · exact Eventually.of_forall fun y => (hs.mul_left L.opNorm).mul_right ‖f y‖
  · simpa only [tsum_mul_right] using hf.norm.const_mul (∑' j, L.opNorm * C j)
  · filter_upwards [] with y
    exact (L.flip (f y)).hasSum (hs.of_norm_bounded (fun j => hb j x y)).hasSum

end JanetCartan.FiniteChain.Graph.KernelLimits
