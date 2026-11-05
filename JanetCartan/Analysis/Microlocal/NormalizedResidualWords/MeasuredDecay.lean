module

public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Decay
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Measured

/-!
# Finite summation on the actual local inverse space

The words below retain the zero-extension/restriction factors of the measured
operator. The finite alphabet is fixed before Q/B, history and source frequency.
Consumers: `rapidDecayAt_inverse_of_finite_chains.hchain` and the same-reference
application in `FixedDomainInverse.FullSource`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedResidualWords
open NormalizedSolver Realization FiniteMasks.ActualFamily FiniteAssembly
open FiniteEvolution Characteristic.PdoRealization FinitePdo FiniteAlgebraic
open FiniteResidual.FiniteIdentity FourierIntegral FourierIntegral.LowBounds
open Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open ArbitraryAccuracy ResponseTransfer ArbitraryAccuracy.ResidualLocalization
open LocalSobolev SmallSupport

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)

variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
variable (output : Euclidean (d+1) → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
variable (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
variable (hsupp : tsupport output ⊆ ball x f.physicalRadius)
variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (L : ι → ℝ)
variable (Q : ι → Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
variable (B : ι → Euclidean (d+1) → MetricTensor (d+1))
variable (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
variable (T : ι → f.centers → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1)) (R C : ι → f.centers → ℝ)
variable (hb : ∀ i p, GraphNormalAmplitudeBounds
  (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
    (selectedAlgebraicSymbol f p (2*L i) (Q i) (B i) 1)) (R i p) (C i p))
local notation "Alphabet" => ((f.centers × Fin 3) ⊕ Unit) × Bool
local notation "retarded" => fun i ↦ (sourceCutMultiplier output ho hob).comp
  ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (T i)).comp
    (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
local notation "letters" => fun i ↦ selectedFullPhysicalResidualTerm
  f hK (L i) (Q i) (B i) (W₁ i) output ho hob hib (T i)

variable (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
variable (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
variable {U : Set (Euclidean (d+1))} (hU : MeasurableSet U)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "J" => fun i a ↦ localRetardedOperator hU U
  (measuredOperator μ ν hμ hν hμb hνb (letters i a))
local notation "P" => fun i ↦ measuredOperator μ ν hμ hν hμb hνb
  (pairedResidual f hK (L i) (Q i) (B i) output ho hob (W₁ i) (retarded i))
include hsupp R C hb

/-- Sum the uniform observations of the literal LOCAL signed complex words
into `hchain` for the actual measured real residual. Real part occurs only
at the end of each word (`app:ch_regular:eq:chain-tail`). -/
theorem measured_realResidual_hchain_of_words
    (G : GradedScale F) (s : ℕ) (ρ A : ι → ℝ)
    (D : ι → LocalL2 U RF →ₗ[ℝ] F) (u : ι → LocalL2 U RF)
    (hword : ∀ j (w : Fin j → Alphabet), RapidDecayAt G s ρ A
      (fun i ↦ D i (l2RealPart (volume.restrict U)
        ((List.ofFn (fun k ↦ J i (w k))).prod
          (l2ComplexInclusion (volume.restrict U) (u i)))))) :
    ∀ j, RapidDecayAt G s ρ A (fun i ↦ D i
      ((localRealCompression hU U (P i) ^ j) (u i))) := by
  classical
  intro j
  have he i : D i ((localRealCompression hU U (P i) ^ j) (u i)) =
      ∑ w : Fin j → Alphabet, D i (l2RealPart (volume.restrict U)
        ((List.ofFn (fun k ↦ J i (w k))).prod
          (l2ComplexInclusion (volume.restrict U) (u i)))) := by
    rw [measured_realResidual_pow_eq_sum_words f hK (L i) (Q i) (B i) (W₁ i)
      output ho hob hib (T i) hsupp (R i) (C i) (hb i)]
    exact map_sum _ _ _
  simp_rw [he]
  exact rapidDecayAt_chain_sum Finset.univ s (fun w _ ↦ hword j w)

/-- The actual angular observation follows zero extension from the inverse's
local space and subtracts one identity. Constants for the finite sum precede
the varying family (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem angular_measured_realResidual_hchain_of_words
    (G : GradedScale F) (s : ℕ) (ρ A : ι → ℝ)
    (D : RH →ₗ[ℝ] F) (u : ι → LocalL2 U RF)
    (hword : ∀ j (w : Fin j → Alphabet), RapidDecayAt G s ρ A
      (fun i ↦ D ((realSource f hK (L i) output ho hob - 1)
        (zeroExtend hU (l2RealPart (volume.restrict U)
          ((List.ofFn (fun k ↦ J i (w k))).prod
            (l2ComplexInclusion (volume.restrict U) (u i)))))))) :
    ∀ j, RapidDecayAt G s ρ A (fun i ↦ D ((realSource f hK (L i) output ho hob - 1)
      (zeroExtend hU ((localRealCompression hU U (P i) ^ j) (u i))))) :=
  measured_realResidual_hchain_of_words f hK output ho hob hib hsupp L Q B W₁ T R C hb
    μ ν hμ hν hμb hνb hU G s ρ A
    (fun i ↦ (D.comp (realSource f hK (L i) output ho hob - 1).toLinearMap).comp
      (zeroExtend hU).toLinearMap) u hword

end JanetCartan.RegularSector.NormalizedResidualWords
