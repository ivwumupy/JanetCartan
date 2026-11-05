module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Repacking
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Shells

/-!
# Finite frequency cutoffs and genuine composition limits

Finite sums of graph and output frequency shells are actual cutoffs in the
literal composition of `app:ch_regular:eq:joint-kernel-phase`. Their limit is
identified from the summable pointwise matrix-kernel estimate, whose producer is
`jc-graph-factor-kernel-estimates`. No convergence or composition identity is
assumed. The shell families must include the bounded frequencies and shoulders.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Testing a regularized joint kernel is absolutely integrable in the source
base, even without a compactly supported datum, since the right symbol supplies
that carrier (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointKernel_test_integrable (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A mi χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    Integrable (fun y => (regularizedJointKernel backward S A mi mo χA χo x y).mulVec
      (f y)) := by
  have hm (y : Euclidean n) :
      (∫ p, regularizedJointIntegrand backward S A mi mo χA χo x y p).mulVec (f y) =
        ∫ p, (regularizedJointIntegrand backward S A mi mo χA χo x y p).mulVec (f y) :=
    (((sourceMatrixAction (r := r)).flip (f y)).integral_comp_comm
      (regularizedJointIntegrand_integrable backward S A mi mo χA χo
        hS hA hi ho hg hc c x y)).symm
  simp only [regularizedJointKernel, Matrix.smul_mulVec, hm]
  exact (regularizedJointIntegrand_test_integrable backward S A mi mo χA χo
    hS hA hi ho hg hc c f hf x).integral_prod_right.smul (jointNormalization n)

/-- Finite independent graph/output frequency sums preserve the exact joint
kernel (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointKernel_finset_cutoffs {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA : ι → Euclidean n → ℝ) (χo : κ → Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k)) (x y : Euclidean n) :
    regularizedJointKernel backward S A mi mo (fun ξ => ∑ j ∈ s, χA j ξ)
      (fun ζ => ∑ k ∈ t, χo k ζ) x y =
      ∑ j ∈ s, ∑ k ∈ t, regularizedJointKernel backward S A mi mo (χA j) (χo k) x y := by
  have he : regularizedJointIntegrand backward S A mi mo (fun ξ => ∑ j ∈ s, χA j ξ)
      (fun ζ => ∑ k ∈ t, χo k ζ) x y = fun p =>
        ∑ j ∈ s, ∑ k ∈ t, regularizedJointIntegrand backward S A mi mo (χA j) (χo k) x y p := by
    funext p
    simp only [regularizedJointIntegrand, regularizedJointAmplitude, Finset.sum_mul,
      Finset.mul_sum, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
    exact Finset.sum_comm
  have hint j k := regularizedJointIntegrand_integrable backward S A mi mo (χA j) (χo k)
    hS hA hi ho (hg j) (hc k) (c j k) x y
  simp only [regularizedJointKernel, he]
  rw [integral_finsetSum s (fun j _ => integrable_finsetSum t (fun k _ => hint j k))]
  simp_rw [integral_finsetSum t (fun k _ => hint _ k), Finset.smul_sum]

private theorem tendsto_finset_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] :
    Tendsto (fun q : Finset ι × Finset κ => q.1 ×ˢ q.2) atTop atTop := by
  apply Monotone.tendsto_atTop_atTop
  · intro a b hab p hp
    simp only [Finset.mem_product] at hp ⊢
    exact ⟨hab.1 hp.1, hab.2 hp.2⟩
  · intro s
    refine ⟨(s.image Prod.fst, s.image Prod.snd), ?_⟩
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩


/-- Testing commutes with both finite frequency partitions. This identifies
finite sums of shells with actual regularized actions, rather than defining an
unrelated kernel series (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointKernel_test_finset_cutoffs {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA : ι → Euclidean n → ℝ) (χo : κ → Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    (∫ y, (regularizedJointKernel backward S A mi mo (fun ξ => ∑ j ∈ s, χA j ξ)
      (fun ζ => ∑ k ∈ t, χo k ζ) x y).mulVec (f y)) =
      ∑ j ∈ s, ∑ k ∈ t, ∫ y,
        (regularizedJointKernel backward S A mi mo (χA j) (χo k) x y).mulVec (f y) := by
  simp_rw [regularizedJointKernel_finset_cutoffs s t backward S A mi mo χA χo
    hS hA hi ho hg hc c, Matrix.sum_mulVec]
  have hint j k := regularizedJointKernel_test_integrable backward S A mi mo (χA j) (χo k)
    hS hA hi ho (hg j) (hc k) (c j k) f hf x
  rw [integral_finsetSum s (fun j _ => integrable_finsetSum t (fun k _ => hint j k))]
  simp_rw [integral_finsetSum t (fun k _ => hint _ k)]

/-- The limit of the actual independently truncated graph/output frequency
integrals on test inputs, under the summable zeroth-output-jet estimate supplied
by `jc-graph-factor-kernel-estimates` (`app:ch_regular:eq:chain-tail`). Output
tails of the regularized identity are included in this convergence statement. -/
theorem tendsto_regularizedJointKernel_test_cutoffs
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo (χA j) (χo k) x y‖ ≤ C (j,k))
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (hfi : Integrable f) (x : Euclidean n) :
    Tendsto (fun q : Finset ℕ × Finset ℕ => ∫ y,
      (regularizedJointKernel backward S A mi mo (fun ξ => ∑ j ∈ q.1, χA j ξ)
        (fun ζ => ∑ k ∈ q.2, χo k ζ) x y).mulVec (f y)) atTop
      (𝓝 (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
        (χA p.1) (χo p.2) x y).mulVec (f y))) := by
  have hsum := hasSum_regularizedJointKernel_test backward S A mi mo
    (fun p : ℕ × ℕ => χA p.1) (fun p : ℕ × ℕ => χo p.2) hS hA hi ho
    (fun p => hg p.1) (fun p => hc p.2) C hs (fun p => hb p.1 p.2) f hfi x
  have ht := hsum.comp (tendsto_finset_product (ι := ℕ) (κ := ℕ))
  simpa only [Function.comp_def, Finset.sum_product, regularizedJointKernel_test_finset_cutoffs _ _ backward
    S A mi mo χA χo hS hA hi ho hg hc c f hf x] using ht

/-- Primitive carriers for finite frequency sums. The amplitude/source
carriers are retained, including source shoulders; no output carrier is added
(`app:ch_regular:eq:joint-kernel-phase`). -/
def RegularizedCarriers.finsetCutoffs
    {A : FullAmplitude n r} {mi : LocalizerSymbol n} {χA χo : ℕ → Euclidean n → ℝ}
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k)) (s t : Finset ℕ) :
    RegularizedCarriers A mi (fun ξ => ∑ j ∈ s, χA j ξ) (fun ζ => ∑ k ∈ t, χo k ζ) where
  amplitudeBase := (c 0 0).amplitudeBase
  inputBase := (c 0 0).inputBase
  inputFrequency := (c 0 0).inputFrequency
  compact_amplitudeBase := (c 0 0).compact_amplitudeBase
  compact_inputBase := (c 0 0).compact_inputBase
  compact_inputFrequency := (c 0 0).compact_inputFrequency
  compact_graphCutoff := by
    convert (HasCompactSupport.finset_sum
      (fun j (_ : j ∈ s) => (c j 0).compact_graphCutoff)) using 1
    ext ξ
    simp
  compact_outputCutoff := by
    convert (HasCompactSupport.finset_sum
      (fun k (_ : k ∈ t) => (c 0 k).compact_outputCutoff)) using 1
    ext ζ
    simp
  amplitude_zero := (c 0 0).amplitude_zero
  input_zero := (c 0 0).input_zero

/-- Genuine pointwise limit of the literal forward compositions with finite
graph/output frequency cutoffs. The only quantitative premise is the summable
pointwise kernel bound from `jc-graph-factor-kernel-estimates`; no convergence or
operator identity is assumed (`app:ch_regular:eq:chain-tail`). The resulting
limit is not identified with a raw Bochner operator for a nonintegrable symbol. -/
theorem tendsto_forward_composition_cutoffs
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖regularizedJointKernel false S A mi mo (χA j) (χo k) x y‖ ≤ C (j,k))
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (hfi : Integrable f) (x : Euclidean n) :
    Tendsto (fun q : Finset ℕ × Finset ℕ =>
      leftLocalizer 1 (fun p => (∑ k ∈ q.2, χo k p.2) * (1 - mo p))
        (graphOperator S (fun u z ξ => ((∑ j ∈ q.1, χA j ξ) : ℂ) • A u z ξ)
          (rightLocalizer 1 mi f)) x) atTop
      (𝓝 (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel false S A mi mo
        (χA p.1) (χo p.2) x y).mulVec (f y))) := by
  have he (q : Finset ℕ × Finset ℕ) := forward_composition_eq_jointKernel S A mi mo
    (fun ξ => ∑ j ∈ q.1, χA j ξ) (fun ζ => ∑ k ∈ q.2, χo k ζ)
    hS hA hi ho (continuous_finsetSum _ (fun j _ => hg j))
    (continuous_finsetSum _ (fun k _ => hc k)) (RegularizedCarriers.finsetCutoffs c q.1 q.2)
    f hf x
  exact (tendsto_regularizedJointKernel_test_cutoffs false S A mi mo χA χo
    hS hA hi ho hg hc c C hs hb f hf hfi x).congr' (Eventually.of_forall (fun q => by simpa only [Complex.ofReal_sum] using (he q).symm))

/-- Genuine pointwise limit of the literal reverse compositions with finite
graph/output frequency cutoffs. The only quantitative premise is the summable
pointwise kernel bound from `jc-graph-factor-kernel-estimates`; no convergence or
operator identity is assumed (`app:ch_regular:eq:chain-tail`). The resulting
limit is not identified with a raw Bochner operator for a nonintegrable symbol. -/
theorem tendsto_reverse_composition_cutoffs
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖regularizedJointKernel true S A mi mo (χA j) (χo k) x y‖ ≤ C (j,k))
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (hfi : Integrable f) (x : Euclidean n) :
    Tendsto (fun q : Finset ℕ × Finset ℕ =>
      leftLocalizer 1 (fun p => (∑ k ∈ q.2, χo k p.2) * (1 - mo p))
        (reverseGraphOperator S (fun u z ξ => ((∑ j ∈ q.1, χA j ξ) : ℂ) • A u z ξ)
          (rightLocalizer 1 mi f)) x) atTop
      (𝓝 (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel true S A mi mo
        (χA p.1) (χo p.2) x y).mulVec (f y))) := by
  have he (q : Finset ℕ × Finset ℕ) := reverse_composition_eq_jointKernel S A mi mo
    (fun ξ => ∑ j ∈ q.1, χA j ξ) (fun ζ => ∑ k ∈ q.2, χo k ζ)
    hS hA hi ho (continuous_finsetSum _ (fun j _ => hg j))
    (continuous_finsetSum _ (fun k _ => hc k)) (RegularizedCarriers.finsetCutoffs c q.1 q.2)
    f hf x
  exact (tendsto_regularizedJointKernel_test_cutoffs true S A mi mo χA χo
    hS hA hi ho hg hc c C hs hb f hf hfi x).congr' (Eventually.of_forall (fun q => by simpa only [Complex.ofReal_sum] using (he q).symm))
end JanetCartan.FiniteChain.Graph.KernelLimits
