module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.FiniteKernels

/-! # Joint continuity of finite elapsed shell representatives

Compact primitive carriers give continuity in elapsed time and physical
output, including the noncompact regularized identity contribution.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => JointVariables E
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
attribute [local instance] matrixContinuousENorm matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem continuous_parameter_jointIntegrand_all
    (backward : Bool) (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude (d + 1) q)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ S p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo) :
    Continuous (fun p : (ℝ × (E × E)) × P ↦
      regularizedJointIntegrand backward (S p.1.1) (A p.1.1) mi mo χA χo p.1.2.1 p.1.2.2 p.2) := by
  change Continuous (mi : E × E → ℝ) at hi
  change Continuous (mo : E × E → ℝ) at ho
  change E × E → ℝ at mi mo
  have hs : Continuous (fun p : (ℝ × (E × E)) × P ↦ S p.1.1 p.2.1.1 p.2.2.1) :=
    hS.comp (f := fun p : (ℝ × (E × E)) × P ↦ (p.1.1, p.2.1.1, p.2.2.1)) (by fun_prop)
  have ha : Continuous (fun p : (ℝ × (E × E)) × P ↦ A p.1.1 p.2.1.1 p.2.1.2 p.2.2.1) :=
    hA.comp (f := fun p : (ℝ × (E × E)) × P ↦ (p.1.1, p.2.1, p.2.2.1)) (by fun_prop)
  have hp : Continuous (fun p : (ℝ × (E × E)) × P ↦ jointPhase backward (S p.1.1) p.1.2.1 p.1.2.2 p.2) := by
    cases backward <;>
      simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true, forwardPhase, reversePhase] <;>
      fun_prop
  have hb : Continuous (fun p : (ℝ × (E × E)) × P ↦ χA p.2.2.1 * χo p.2.2.2.2 *
      (1 - mo (p.1.2.1, p.2.2.2.2)) * mi (p.1.2.2, p.2.2.2.1)) := by fun_prop
  exact (Complex.continuous_exp.comp ((continuous_const (y := Complex.I)).mul
    (Complex.continuous_ofReal.comp hp))).smul ((Complex.continuous_ofReal.comp hb).smul ha)

private theorem continuous_parameter_jointKernel_all
    (backward : Bool) (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude (d + 1) q)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ S p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r, RegularizedCarriers (A r) mi χA χo)
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier) :
    Continuous (fun p : ℝ × (E × E) ↦ regularizedJointKernel backward (S p.1) (A p.1)
      mi mo χA χo p.2.1 p.2.2) := by
  have he (r : ℝ) (x y : E) : regularizedJointKernel backward (S r) (A r) mi mo χA χo x y =
      jointNormalization (d + 1) • ∫ p in (c 0).jointCarrier,
        regularizedJointIntegrand backward (S r) (A r) mi mo χA χo x y p := by
    unfold regularizedJointKernel
    congr 1
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    apply (c r).integrand_zero backward (S r) mo x y p
    intro h
    exact hp ((hcommon r) ▸ h.1)
  simp_rw [he]
  exact (continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (z : ℝ × (E × E)) (p : P) ↦ regularizedJointIntegrand backward (S z.1) (A z.1) mi mo χA χo z.2.1 z.2.2 p)
    (continuous_parameter_jointIntegrand_all backward S A mi mo χA χo hS hA hi ho hg hc)
    (c 0).compact_jointCarrier).const_smul (jointNormalization (d + 1))

/-- The finite physical kernel acting on a continuous input is jointly
continuous in elapsed time and output. Its primitive source carrier is compact;
its output need not be. Consumer: identifying the actual bounded elapsed
integral in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_finiteJointKernel_test
    (backward : Bool) (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude (d + 1) q)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ S p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r, RegularizedCarriers (A r) mi χA χo)
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier)
    (hinput : ∀ r, (c r).inputBase = (c 0).inputBase)
    (f : E → Fin q → ℂ) (hf : Continuous f) :
    Continuous (fun p : ℝ × E ↦ WithLp.toLp 2 (∫ y,
      (regularizedJointKernel backward (S p.1) (A p.1) mi mo χA χo p.2 y).mulVec (f y))) := by
  have hK := continuous_parameter_jointKernel_all backward S A mi mo χA χo
    hS hA hi ho hg hc c hcommon
  have hi' : Continuous (fun p : (ℝ × E) × E ↦
      (regularizedJointKernel backward (S p.1.1) (A p.1.1) mi mo χA χo p.1.2 p.2).mulVec
        (f p.2)) :=
    (hK.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).matrix_mulVec
      (hf.comp continuous_snd)
  have he (r : ℝ) (x : E) :
      (∫ y, (regularizedJointKernel backward (S r) (A r) mi mo χA χo x y).mulVec (f y)) =
        ∫ y in (c 0).inputBase,
          (regularizedJointKernel backward (S r) (A r) mi mo χA χo x y).mulVec (f y) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [regularizedJointKernel_zero_off_input _ _ _ _ _ _ _ (c r) x y
      (by simpa only [hinput r] using hy)]
    simp
  simp_rw [he]
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_parametric_integral_of_continuous hi' (c 0).compact_inputBase)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
