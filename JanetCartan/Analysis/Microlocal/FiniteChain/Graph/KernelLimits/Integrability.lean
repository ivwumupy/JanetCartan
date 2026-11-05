module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Algebra

/-!
# Absolute integrability from primitive carriers

For `app:ch_regular:eq:joint-kernel-phase`, compact primitive carriers imply
absolute integrability of the regularized matrix kernel and its tested version.
No compact output support is asserted for the complementary output symbol.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256

local instance matrixContinuousENorm : ContinuousENorm (Matrix (Fin r) (Fin r) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin r) (Fin r) ℂ) inferInstance).toContinuousENorm

local instance matrixPseudoMetrizableSpace : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin r → Fin r → ℂ))

/-- Primitive carriers for `app:ch_regular:eq:joint-kernel-phase`. The amplitude
has two compact base positions, the right symbol has compact source/frequency
carriers, and the two regularizers have compact frequency support. There is no
output carrier field: a regularized identity kernel can have output tails. -/
structure RegularizedCarriers (A : FullAmplitude n r) (mi : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) where
  amplitudeBase : Set (Euclidean n × Euclidean n)
  inputBase : Set (Euclidean n)
  inputFrequency : Set (Euclidean n)
  compact_amplitudeBase : IsCompact amplitudeBase
  compact_inputBase : IsCompact inputBase
  compact_inputFrequency : IsCompact inputFrequency
  compact_graphCutoff : HasCompactSupport χA
  compact_outputCutoff : HasCompactSupport χo
  amplitude_zero : ∀ u z ξ, (u, z) ∉ amplitudeBase → A u z ξ = 0
  input_zero : ∀ y η, (y, η) ∉ inputBase ×ˢ inputFrequency → mi (y, η) = 0

/-- The compact integration carrier, excluding the external output variable
(`app:ch_regular:eq:joint-kernel-phase`). -/
def RegularizedCarriers.jointCarrier {A : FullAmplitude n r}
    {mi : LocalizerSymbol n} {χA χo : Euclidean n → ℝ}
    (c : RegularizedCarriers A mi χA χo) : Set (JointVariables (Euclidean n)) :=
  c.amplitudeBase ×ˢ (tsupport χA ×ˢ (c.inputFrequency ×ˢ tsupport χo))

/-- The five joint integration variables range over a compact carrier
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem RegularizedCarriers.compact_jointCarrier {A : FullAmplitude n r}
    {mi : LocalizerSymbol n} {χA χo : Euclidean n → ℝ}
    (c : RegularizedCarriers A mi χA χo) : IsCompact c.jointCarrier :=
  c.compact_amplitudeBase.prod
    (c.compact_graphCutoff.prod (c.compact_inputFrequency.prod c.compact_outputCutoff))

/-- Vanishing off the primitive integration carrier, including source shoulders
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem RegularizedCarriers.integrand_zero {A : FullAmplitude n r}
    {mi : LocalizerSymbol n} {χA χo : Euclidean n → ℝ}
    (c : RegularizedCarriers A mi χA χo) (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (mo : LocalizerSymbol n)
    (x y : Euclidean n) (p : JointVariables (Euclidean n))
    (hp : (p, y) ∉ c.jointCarrier ×ˢ c.inputBase) :
    regularizedJointIntegrand backward S A mi mo χA χo x y p = 0 := by
  by_cases hA : p.1 ∈ c.amplitudeBase
  · by_cases hg : p.2.1 ∈ tsupport χA
    · by_cases hi : p.2.2.1 ∈ c.inputFrequency
      · by_cases ho : p.2.2.2 ∈ tsupport χo
        · have hy : y ∉ c.inputBase := fun hy => hp ⟨⟨hA, hg, hi, ho⟩, hy⟩
          have hm := c.input_zero y p.2.2.1 (fun h => hy h.1)
          simp [regularizedJointIntegrand, regularizedJointAmplitude, hm]
        · simp [regularizedJointIntegrand, regularizedJointAmplitude,
            image_eq_zero_of_notMem_tsupport ho]
      · have hm := c.input_zero y p.2.2.1 (fun h => hi h.2)
        simp [regularizedJointIntegrand, regularizedJointAmplitude, hm]
    · simp [regularizedJointIntegrand, regularizedJointAmplitude,
        image_eq_zero_of_notMem_tsupport hg]
  · simp [regularizedJointIntegrand, regularizedJointAmplitude,
      c.amplitude_zero p.1.1 p.1.2 p.2.1 hA]

/-- Continuity of the full regularized integrand follows from the primitive
phase, symbols and amplitude (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointIntegrand_continuous (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo) :
    Continuous (fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
      regularizedJointIntegrand backward S A mi mo χA χo q.1.1 q.1.2 q.2) := by
  change Continuous (mi : Euclidean n × Euclidean n → ℝ) at hi
  change Continuous (mo : Euclidean n × Euclidean n → ℝ) at ho
  change Euclidean n × Euclidean n → ℝ at mi mo
  have hs : Continuous (fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
      S q.2.1.1 q.2.2.1) := hS.comp (f := fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) => (q.2.1.1, q.2.2.1)) (by fun_prop)
  have ha : Continuous (fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
      A q.2.1.1 q.2.1.2 q.2.2.1) := hA.comp (f := fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) => (q.2.1, q.2.2.1)) (by fun_prop)
  have hp : Continuous (fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
      jointPhase backward S q.1.1 q.1.2 q.2) := by
    cases backward <;>
      simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true, forwardPhase, reversePhase] <;>
      fun_prop
  have hb : Continuous (fun q : (Euclidean n × Euclidean n) × JointVariables (Euclidean n) =>
      χA q.2.2.1 * χo q.2.2.2.2 * (1 - mo (q.1.1, q.2.2.2.2)) *
        mi (q.1.2, q.2.2.2.1)) := by fun_prop
  have he := Complex.continuous_exp.comp ((continuous_const (y := Complex.I)).mul (Complex.continuous_ofReal.comp hp))
  have hm := (Complex.continuous_ofReal.comp hb).smul ha
  exact he.smul hm

/-- The matrix joint integral is absolutely integrable at every pair of external
base points (`app:ch_regular:eq:joint-kernel-phase`). Smooth primitive data imply
the displayed continuity hypotheses. -/
theorem regularizedJointIntegrand_integrable (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A mi χA χo) (x y : Euclidean n) :
    Integrable (regularizedJointIntegrand backward S A mi mo χA χo x y) := by
  unfold JointVariables at *
  have hcont : Continuous (regularizedJointIntegrand backward S A mi mo χA χo x y) :=
    (regularizedJointIntegrand_continuous backward S A mi mo χA χo
      hS hA hi ho hg hc).comp (f := fun p => ((x, y), p))
        (continuous_const.prodMk continuous_id)
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro c.compact_jointCarrier
  intro p hp
  exact c.integrand_zero backward S mo x y p (fun h => hp h.1)

/-- Test inputs may be continuous without compact support: the right symbol
provides the compact source carrier. This is the full product integrability
needed for Fubini in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem regularizedJointIntegrand_test_integrable (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A mi χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    Integrable (fun q : JointVariables (Euclidean n) × Euclidean n =>
      (regularizedJointIntegrand backward S A mi mo χA χo x q.2 q.1).mulVec (f q.2)) (volume.prod volume) := by
  unfold JointVariables at *
  have hcont : Continuous (fun q : JointVariables (Euclidean n) × Euclidean n =>
      regularizedJointIntegrand backward S A mi mo χA χo x q.2 q.1) :=
    (regularizedJointIntegrand_continuous backward S A mi mo χA χo
      hS hA hi ho hg hc).comp (f := fun q : JointVariables (Euclidean n) × Euclidean n => ((x, q.2), q.1))
        ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)
  apply (hcont.matrix_mulVec (hf.comp continuous_snd)).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (c.compact_jointCarrier.prod c.compact_inputBase)
  intro q hq
  simp only [c.integrand_zero backward S mo x q.2 q.1 hq, Matrix.zero_mulVec]

/-- The right input base support survives integration, for either literal
orientation (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointKernel_zero_off_input (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (x y : Euclidean n) (hy : y ∉ c.inputBase) :
    regularizedJointKernel backward S A mi mo χA χo x y = 0 := by
  have he : regularizedJointIntegrand backward S A mi mo χA χo x y = 0 :=
    funext fun p => c.integrand_zero backward S mo x y p (fun h => hy h.2)
  simp [regularizedJointKernel, he]

end JanetCartan.FiniteChain.Graph.KernelLimits
