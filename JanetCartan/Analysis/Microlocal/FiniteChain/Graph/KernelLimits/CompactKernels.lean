module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.TestOutputs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Smooth compact graph kernels for the Cartesian completion

For `app:ch_regular:eq:chain-tail`, a fixed smooth physical output cutoff makes
each joint regularization a supported kernel. `SummedSupport` proves that a
cutoff equal to one on the recovered carrier preserves the genuine limit.
Smoothness here is derived from primitive data, including phases smooth only
away from zero. Both physical amplitude positions and every matrix entry remain.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral Retarded.KernelDecay Retarded.KernelSobolev AmplitudeBound
variable {n r d : ℕ}
attribute [local fun_prop] ContDiff.inner ContDiffAt.inner
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Joint smoothness of the actual integrand away from the graph-frequency
origin; the graph regularizer removes that origin. This is the regularity
input for the compact-kernel bridge in `app:ch_regular:eq:chain-tail`. -/
theorem contDiff_regularizedJointIntegrand (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo)
    (hg0 : (0 : Euclidean n) ∉ tsupport χA) :
    ContDiff ℝ ∞ (fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
      regularizedJointIntegrand backward S A mi mo χA χo q.1.1 q.1.2 q.2) := by
  change ContDiff ℝ ∞ (mi : Euclidean n × Euclidean n → ℝ) at hi
  change ContDiff ℝ ∞ (mo : Euclidean n × Euclidean n → ℝ) at ho
  change Euclidean n × Euclidean n → ℝ at mi mo
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q.2.2.1 = 0
  · apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : Matrix (Fin r) (Fin r) ℂ))
    have hn : ∀ᶠ p : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) in 𝓝 q,
        p.2.2.1 ∉ tsupport χA :=
      ((isClosed_tsupport χA).isOpen_compl.preimage (by fun_prop)).mem_nhds (by simpa [hq])
    filter_upwards [hn] with p hp
    simp [regularizedJointIntegrand, regularizedJointAmplitude,
      image_eq_zero_of_notMem_tsupport hp]
  · have hs : ContDiffAt ℝ ∞
        (fun p : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
          S p.2.1.1 p.2.2.1) q :=
      (hS q.2.1.1 q.2.2.1 hq).comp q
        (contDiffAt_snd.fst.fst.prodMk contDiffAt_snd.snd.fst)
    have ha : ContDiffAt ℝ ∞
        (fun p : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
          A p.2.1.1 p.2.1.2 p.2.2.1) q := hA.contDiffAt.comp q (contDiffAt_snd.fst.prodMk contDiffAt_snd.snd.fst)
    have hp : ContDiffAt ℝ ∞
        (fun p : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
          jointPhase backward S p.1.1 p.1.2 p.2) q := by
      cases backward <;>
        simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true, forwardPhase, reversePhase] <;>
        fun_prop
    have hb : ContDiff ℝ ∞
        (fun p : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
          χA p.2.2.1 * χo p.2.2.2.2 * (1 - mo (p.1.1, p.2.2.2.2)) *
            mi (p.1.2, p.2.2.2.1)) := by fun_prop
    exact ((contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp q hp)).cexp).smul
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp q hb.contDiffAt).smul ha)

/-- Smoothness in both external bases follows by differentiating the actual
compact primitive integral; no smoothness premise on its output is required
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_regularizedJointKernel (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo)
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo)
    (hg0 : (0 : Euclidean n) ∉ tsupport χA) :
    ContDiff ℝ ∞ (Function.uncurry (regularizedJointKernel backward S A mi mo χA χo)) :=
  (contDiff_integral_commonCarrier
    (contDiff_regularizedJointIntegrand backward S A mi mo χA χo hS hA hi ho hg hc hg0)
    c.compact_jointCarrier (fun q p hp => c.integrand_zero backward S mo q.1 q.2 p
      (fun h => hp h.1))).const_smul _

/-- Smooth coordinate transfer of a cutoff matrix entry, consumed by
`supportedJointKernelEntry` (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_cutMatrixEntry_coordinates
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (K : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (hK : ContDiff ℝ ∞ (Function.uncurry K)) (ψ : Euclidean n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (a b : Fin r) :
    ContDiff ℝ ∞ (fun p : (ℝ × (Fin d → ℝ)) × ((Fin d → ℝ) × ℝ) =>
      (ψ (J p.1) : ℂ) * K (J p.1) (J (p.2.2, p.2.1)) a b) := by
  have he : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n => K p.1 p.2 a b) :=
    (matrixEntryEvaluation a b).contDiff.comp hK
  have hp : ContDiff ℝ ∞ (fun p : (ℝ × (Fin d → ℝ)) × ((Fin d → ℝ) × ℝ) =>
      (J p.1, J (p.2.2, p.2.1))) :=
    (J.contDiff.comp contDiff_fst).prodMk
      (J.contDiff.comp (contDiff_snd.snd.prodMk contDiff_snd.fst))
  exact (Complex.ofRealCLM.contDiff.comp (hψ.comp (J.contDiff.comp contDiff_fst))).mul
    (he.comp hp)

/-- An actual matrix channel of the joint kernel in Cartesian coordinates,
with a fixed output cutoff. The coordinate equivalence is explicit, and the
consumer supplies the corresponding integration measure
(`app:ch_regular:eq:chain-tail`). -/
def supportedJointKernelEntry (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo ψ : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo)
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo)
    (hg0 : (0 : Euclidean n) ∉ tsupport χA)
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ) (a b : Fin r) :
    SupportedSmoothKernel d d where
  toFun x y := (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo χA χo
    (J x) (J (y.2, y.1)) a b
  smooth := contDiff_cutMatrixEntry_coordinates J (regularizedJointKernel backward S A mi mo χA χo)
    (contDiff_regularizedJointKernel backward S A mi mo χA χo c hS hA hi ho hg hc hg0)
    ψ hψ a b
  inputSupport := (fun y => J (y.2, y.1)) ⁻¹' c.inputBase
  outputSupport := J ⁻¹' tsupport ψ
  compact_inputSupport :=
    ((Homeomorph.prodComm _ _).trans J.toHomeomorph).isCompact_preimage.mpr c.compact_inputBase
  compact_outputSupport := J.toHomeomorph.isCompact_preimage.mpr hsψ
  zero_off_input x y hy := by
    rw [regularizedJointKernel_zero_off_input backward S A mi mo χA χo c _ _ hy]
    simp
  zero_off_output x y hx := by simp [image_eq_zero_of_notMem_tsupport hx]

end JanetCartan.FiniteChain.Graph.KernelLimits
