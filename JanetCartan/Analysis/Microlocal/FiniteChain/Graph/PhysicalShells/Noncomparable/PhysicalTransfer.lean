module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PairEstimate
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.PhaseExtension

/-!
# Transfer to the physical cutoff kernels

Support agreement justifies the smooth phase extension used in the
noncomparable part of `app:ch_regular:eq:joint-kernel-phase`. These equalities
preserve the actual evaluated output derivatives and every normalization.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
open FourierIntegral
variable {n r : ℕ}

/-- In dimension zero each actual graph annulus vanishes. Thus no summation
of a constant low-frequency volume is needed
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem graphBranchCutoff_dim_zero (low : Bool) (j : ℕ) (ξ : Euclidean 0) :
    graphBranchCutoff low j ξ = 0 := by
  have hξ : ξ = 0 := Subsingleton.elim _ _
  subst ξ
  cases low <;> simp [graphBranchCutoff, highGraphCutoff, lowGraphCutoff,
    expandingCutoff, contractingCutoff]

/-- The physical pairs are identically zero in dimension zero; the
positive-dimensional summable weights cover all remaining cases
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalPair_dim_zero (backward : Bool)
    (S : Euclidean 0 → Euclidean 0 → ℝ) (A : FullAmplitude 0 r)
    (mi mo : LocalizerSymbol 0) (low : Bool) (j k : ℕ) (x y : Euclidean 0) :
    KernelLimits.regularizedJointKernel backward S A mi mo
      (graphBranchCutoff low j) (outputCutoff k) x y = 0 := by
  simp [KernelLimits.regularizedJointKernel, KernelLimits.regularizedJointIntegrand,
    KernelLimits.regularizedJointAmplitude, graphBranchCutoff_dim_zero]

/-- A physical phase extension leaves the literal cutoff kernel unchanged
when it agrees on the amplitude/cutoff support. No global agreement or
homogeneity of the original phase is required for this step
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem physicalJointKernel_congr_phase (backward : Bool)
    (S Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (hphase : ∀ u z ξ, A u z ξ ≠ 0 → χA ξ ≠ 0 → S u ξ = Φ u ξ) :
    KernelLimits.regularizedJointKernel backward S A mi mo χA χo x y =
      KernelLimits.regularizedJointKernel backward Φ A mi mo χA χo x y := by
  unfold KernelLimits.regularizedJointKernel
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hA : A p.1.1 p.1.2 p.2.1 = 0
  · simp [KernelLimits.regularizedJointIntegrand, KernelLimits.regularizedJointAmplitude, hA]
  by_cases hg : χA p.2.1 = 0
  · simp [KernelLimits.regularizedJointIntegrand, KernelLimits.regularizedJointAmplitude, hg]
  have hp : jointPhase backward S x y p = jointPhase backward Φ x y p := by
    cases backward <;> simp [jointPhase, forwardPhase, reversePhase,
      hphase p.1.1 p.1.2 p.2.1 hA hg]
  simp only [KernelLimits.regularizedJointIntegrand, hp]

/-- Actual physical output derivatives of either graph branch with independent
output index equal the normalized derivatives estimated in
`exists_normalizedPair_derivative_bound`. The original phase need agree with
the smooth extension only where the physical integrand contributes. The
extension's derivative profiles remain obligations of the phase producer;
the identity assumes no bound or shell decomposition
(`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_physicalPair_eq_normalized_extension (backward : Bool)
    (S Φ φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (low : Bool) (j k : ℕ) (x y : Euclidean n)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hphase : ∀ u z ξ, A u z ξ ≠ 0 → graphBranchCutoff low j ξ ≠ 0 → S u ξ = Φ u ξ)
    (hhom : ∀ u ξ, Φ u (ρ • ξ) = ρ * φ u ξ)
    (hΦ : Continuous (Function.uncurry Φ))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (c : KernelLimits.RegularizedCarriers A mi (graphBranchCutoff low j) (outputCutoff k))
    (m : ℕ) (v : Fin m → Euclidean n) :
    iteratedFDeriv ℝ m
        (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2))
            (graphBranchCutoff low j) (outputCutoff k) t y) x v =
      iteratedFDeriv ℝ m
        (fun t => KernelEstimates.regularizedJointKernel backward ρ φ A mi mo
          (graphBranchCutoff low j) (outputCutoff k) t y) x v := by
  have he : (fun t => KernelLimits.regularizedJointKernel backward S A
        (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) =
      (fun t => KernelLimits.regularizedJointKernel backward Φ A
        (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) := by
    funext t
    exact physicalJointKernel_congr_phase backward S Φ A _ _ _ _ t y hphase
  rw [he]
  exact iteratedFDeriv_physicalJointKernel_eq_normalized backward Φ φ A mi mo
    (graphBranchCutoff low j) (outputCutoff k) x y hρ hhom hΦ hA hi ho
    (contDiff_graphBranchCutoff low j).continuous (contDiff_outputCutoff k).continuous c m v

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
