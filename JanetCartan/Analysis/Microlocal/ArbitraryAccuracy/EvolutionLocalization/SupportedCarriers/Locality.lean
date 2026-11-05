module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers.PhaseExtension
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.ConicLimits.Support

/-!
# Removing the auxiliary phase from both exported graph actions

These identities transfer both conclusions of the primitive graph theorem:
the physical summed-kernel test action and the limit of the literal localized
compositions. The two-position amplitude, physical Fourier normalization,
source shoulders and the identity contribution of `1 - mo` are unchanged.
All equalities hold for either literal orientation and arbitrary cutoff
families, so no shell is dropped during the transfer.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelLimits

variable {d q : ℕ}

section Locality
variable (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
  (χout χsource β : Euclidean (d + 1) → ℂ)
  {F : Set (Euclidean d)} (hF : IsClosed F)
  (hb : ∀ t s y η, η ∉ F → b t s y η = 0) (r : ℝ)
  (S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
  (he : ∀ u ∈ tsupport χout, ∀ ξ ∈ elapsedFrequencyCarrier β F,
    S' u ξ = elapsedPhase Ψ r u ξ)

include hF hb he

/-- The extension agrees on every nonzero original amplitude, using exactly
the original spatial support and masks
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem supported_elapsedPhase_eq_on_amplitude
    (u z ξ : Euclidean (d + 1))
    (hA : elapsedAmplitude b χout χsource β r u z ξ ≠ 0) :
    S' u ξ = elapsedPhase Ψ r u ξ := by
  have hc := elapsedAmplitude_mem_carrier b χout χsource β hF hb r hA
  exact he u hc.1.1 ξ hc.2

/-- Every physical regularized joint kernel is unchanged, in both literal
orientations and for independent graph/output cutoffs. The physical `2*pi`
normalization is retained by the existing kernel congruence
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem elapsed_regularizedJointKernel_phase_congr
    (backward : Bool) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1)) :
    regularizedJointKernel backward S' (elapsedAmplitude b χout χsource β r)
      mi mo χA χo x y =
    regularizedJointKernel backward (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r)
      mi mo χA χo x y := by
  apply PhysicalShells.Noncomparable.physicalJointKernel_congr_phase
  intro u z ξ hA _
  exact supported_elapsedPhase_eq_on_amplitude Ψ b χout χsource β hF hb r S' he u z ξ hA

/-- The summed physical joint-kernel test action is exactly the original
action. This is the first identification exported by the primitive graph
theorem; no convergence or desired leakage bound is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem elapsed_summedJointKernel_test_phase_congr
    (backward : Bool) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : ℕ → Euclidean (d + 1) → ℝ)
    (f : Euclidean (d + 1) → Fin q → ℂ) (x : Euclidean (d + 1)) :
    (∫ y, (∑' jk : ℕ × ℕ,
      regularizedJointKernel backward S' (elapsedAmplitude b χout χsource β r)
        mi mo (χA jk.1) (χo jk.2) x y).mulVec (f y)) =
    ∫ y, (∑' jk : ℕ × ℕ,
      regularizedJointKernel backward (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r)
        mi mo (χA jk.1) (χo jk.2) x y).mulVec (f y) := by
  simp_rw [elapsed_regularizedJointKernel_phase_congr Ψ b χout χsource β hF hb r S' he]

/-- Each localized, frequency-regularized composition is unchanged. In
particular the output multiplier is still the full `χo * (1 - mo)`, with
its identity term, and the source mask remains on the right
(`app:ch_regular:eq:chain-tail`). -/
theorem elapsed_regularizedComposition_phase_congr
    (backward : Bool) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ)
    (f : Euclidean (d + 1) → Fin q → ℂ) :
    leftLocalizer 1 (fun z => χo z.2 * (1 - mo z))
      ((if backward then reverseGraphOperator else graphOperator) S'
        (fun u z ξ => (χA ξ : ℂ) • elapsedAmplitude b χout χsource β r u z ξ)
        (rightLocalizer 1 mi f)) =
    leftLocalizer 1 (fun z => χo z.2 * (1 - mo z))
      ((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
        (fun u z ξ => (χA ξ : ℂ) • elapsedAmplitude b χout χsource β r u z ξ)
        (rightLocalizer 1 mi f)) := by
  rw [ConicLimits.regularized_orientedGraph_phase_congr backward (elapsedPhase Ψ r) S'
    (elapsedAmplitude b χout χsource β r) χA
    (fun u z ξ hA _ =>
      supported_elapsedPhase_eq_on_amplitude Ψ b χout χsource β hF hb r S' he u z ξ hA)]

/-- The same candidate limit realizes the same original localized operator
after removing the extension. This is the second identification exported by
the primitive graph theorem, with both independent finite regularizations
and arbitrary target value (`app:ch_regular:eq:chain-tail`). -/
theorem elapsed_regularizationLimit_phase_congr
    (backward : Bool) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : ℕ → Euclidean (d + 1) → ℝ)
    (f : Euclidean (d + 1) → Fin q → ℂ) (x : Euclidean (d + 1))
    (a : Fin q) (v : ℂ) :
    Tendsto (fun jk : Finset ℕ × Finset ℕ =>
      leftLocalizer 1 (fun z => (∑ k ∈ jk.2, χo k z.2) * (1 - mo z))
        ((if backward then reverseGraphOperator else graphOperator) S'
          (fun u z ξ => ((∑ j ∈ jk.1, χA j ξ) : ℂ) •
            elapsedAmplitude b χout χsource β r u z ξ)
          (rightLocalizer 1 mi f)) x a) atTop (𝓝 v) ↔
    Tendsto (fun jk : Finset ℕ × Finset ℕ =>
      leftLocalizer 1 (fun z => (∑ k ∈ jk.2, χo k z.2) * (1 - mo z))
        ((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
          (fun u z ξ => ((∑ j ∈ jk.1, χA j ξ) : ℂ) •
            elapsedAmplitude b χout χsource β r u z ξ)
          (rightLocalizer 1 mi f)) x a) atTop (𝓝 v) := by
  apply tendsto_congr
  intro jk
  simpa only [Complex.ofReal_sum] using
    congrArg (fun g : Euclidean (d + 1) → Fin q → ℂ => g x a)
    (elapsed_regularizedComposition_phase_congr Ψ b χout χsource β hF hb r S' he
      backward mi mo (fun ξ => ∑ j ∈ jk.1, χA j ξ) (fun ξ => ∑ k ∈ jk.2, χo k ξ) f)

/-- The supported extension also gives exactly the existing bounded elapsed
graph and its literal reverse full-graph realization. Existence and estimates
for those realizations remain separate analytic obligations
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsed_fullGraph_phase_congr :
    FullLowBounds.fullGraphOperator S' (elapsedAmplitude b χout χsource β r) =
        elapsedGraph Ψ b χout χsource β r ∧
      FullLowBounds.reverseFullGraphOperator S' (elapsedAmplitude b χout χsource β r) =
        FullLowBounds.reverseFullGraphOperator (elapsedPhase Ψ r)
          (elapsedAmplitude b χout χsource β r) := by
  have h := supported_elapsedPhase_eq_on_amplitude Ψ b χout χsource β hF hb r S' he
  exact ⟨FullLowBounds.fullGraphOperator_phase_congr _ _ _ h,
    FullLowBounds.reverseFullGraphOperator_phase_congr _ _ _ h⟩

end Locality

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
