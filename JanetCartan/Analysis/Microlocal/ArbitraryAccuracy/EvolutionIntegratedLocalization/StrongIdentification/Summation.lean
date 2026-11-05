module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.FiniteKernels

/-!
# Testing the summed bounded elapsed kernel

The quantitative input is exactly a summable, pointwise Frobenius majorant
for `elapsedPhysicalShellKernel`, after elapsed integration. Its producers
are `ShellSummation` and `UniformDecay`; no fixed-r estimate or operator tail
bound is assumed. `ActualOperator` identifies this physical action with the
localized strong L² limit. The parent must discharge the majorant.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph RegularSector.Characteristic.EvolutionIntegral
open KernelLimits
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
attribute [local instance] matrixContinuousENorm matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The summable pointwise bound on the ACTUAL bounded elapsed shells permits
summation under a test integral. `C` bounds the Frobenius norm after elapsed
integration; its producers are `ShellSummation` and `UniformDecay`, and its
instantiation remains the parent's obligation. Consumer: identifying the
summed kernel in `app:ch_regular:eq:chain-tail`. -/
theorem hasSum_elapsedPhysicalShellKernel_test {ι : Type*} [Countable ι]
    (backward : Bool) (ρ Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : ι → E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ j, Continuous (χo j))
    (c : ∀ r j, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (χA j) (χo j))
    (hcommon : ∀ r j, (c r j).jointCarrier = (c 0 j).jointCarrier)
    (C : ι → ℝ) (hs : Summable C)
    (hb : ∀ j x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
      mi mo (χA j) (χo j) x y‖ ≤ C j)
    (f : E → Fin q → ℂ) (hf : Integrable f) (x : E) :
    HasSum (fun j ↦ ∫ y, (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (χA j) (χo j) x y).mulVec (f y))
      (∫ y, (∑' j, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (χA j) (χo j) x y).mulVec (f y)) := by
  let K := fun j ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
    mi mo (χA j) (χo j) x
  let L := sourceMatrixAction (r := q)
  apply hasSum_integral_of_dominated_convergence
    (fun j y ↦ (L.opNorm * C j) * ‖f y‖)
  · intro j
    exact L.continuous₂.comp_aestronglyMeasurable
      ((continuous_elapsedPhysicalShellKernel_source backward ρ Δ Ψ b χout χsource β
        mi mo (χA j) (χo j) hS hA hi ho (hg j) (hc j) (fun r ↦ c r j)
        (fun r ↦ hcommon r j) x).aestronglyMeasurable.prodMk hf.aestronglyMeasurable)
  · intro j
    filter_upwards [] with y
    exact (L.le_opNorm₂ (K j y) (f y)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb j x y) L.opNorm_nonneg) (norm_nonneg _))
  · exact Eventually.of_forall (fun y ↦ (hs.mul_left L.opNorm).mul_right ‖f y‖)
  · simpa only [tsum_mul_right] using hf.norm.const_mul (∑' j, L.opNorm * C j)
  · filter_upwards [] with y
    exact (L.flip (f y)).hasSum (hs.of_norm_bounded (fun j ↦ hb j x y)).hasSum

/-- Independent finite graph and output cutoffs converge on every L¹ input
to testing the SAME summed elapsed shell kernel. Arbitrary countable indices
allow the contracting graph shells and the zeroth output-frequency piece.
Only the pointwise summable elapsed-shell majorant from `ShellSummation` /
`UniformDecay` is quantitative; no operator estimate is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem tendsto_elapsedPhysicalShellKernel_test_cutoffs
    {ι κ : Type*} [Countable ι] [Countable κ]
    (backward : Bool) (ρ Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA : ι → E → ℝ) (χo : κ → E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ r j k, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (χA j) (χo k))
    (hcommon : ∀ r j k, (c r j k).jointCarrier = (c 0 j k).jointCarrier)
    (C : ι × κ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
      mi mo (χA j) (χo k) x y‖ ≤ C (j, k))
    (f : E → Fin q → ℂ) (hf : Integrable f) (x : E) :
    Tendsto (fun s : Finset ι × Finset κ ↦ ∫ y,
      (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (fun ξ ↦ ∑ j ∈ s.1, χA j ξ) (fun ζ ↦ ∑ k ∈ s.2, χo k ζ) x y).mulVec (f y)) atTop
      (𝓝 (∫ y, (∑' p : ι × κ, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (χA p.1) (χo p.2) x y).mulVec (f y))) := by
  let L := sourceMatrixAction (r := q)
  have hint (j : ι) (k : κ) : Integrable (fun y ↦
      (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (χA j) (χo k) x y).mulVec (f y)) := by
    apply (hf.norm.const_mul (L.opNorm * C (j, k))).mono'
    · exact L.continuous₂.comp_aestronglyMeasurable
        ((continuous_elapsedPhysicalShellKernel_source backward ρ Δ Ψ b χout χsource β
          mi mo (χA j) (χo k) hS hA hi ho (hg j) (hc k) (fun r ↦ c r j k)
          (fun r ↦ hcommon r j k) x).aestronglyMeasurable.prodMk hf.aestronglyMeasurable)
    · filter_upwards [] with y
      exact (L.le_opNorm₂ _ (f y)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb j k x y) L.opNorm_nonneg) (norm_nonneg _))
  have he (s : Finset ι × Finset κ) :
      (∫ y, (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (fun ξ ↦ ∑ j ∈ s.1, χA j ξ) (fun ζ ↦ ∑ k ∈ s.2, χo k ζ) x y).mulVec (f y)) =
      ∑ j ∈ s.1, ∑ k ∈ s.2, ∫ y, (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (χA j) (χo k) x y).mulVec (f y) := by
    simp_rw [elapsedPhysicalShellKernel_finset_cutoffs s.1 s.2 backward ρ Δ Ψ b χout χsource β
      mi mo χA χo hS hA hi ho hg hc c hcommon, Matrix.sum_mulVec]
    rw [integral_finsetSum s.1 (fun j _ ↦ integrable_finsetSum s.2 (fun k _ ↦ hint j k))]
    simp_rw [integral_finsetSum s.2 (fun k _ ↦ hint _ k)]
  have hsum := hasSum_elapsedPhysicalShellKernel_test backward ρ Δ Ψ b χout χsource β mi mo
    (fun p : ι × κ ↦ χA p.1) (fun p : ι × κ ↦ χo p.2) hS hA hi ho
    (fun p ↦ hg p.1) (fun p ↦ hc p.2) (fun r p ↦ c r p.1 p.2)
    (fun r p ↦ hcommon r p.1 p.2) C hs (fun p ↦ hb p.1 p.2) f hf x
  simpa only [Function.comp_def, Finset.sum_product, he] using
    hsum.comp (tendsto_finsetProd_atTop (ι := ι) (ι' := κ))

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
