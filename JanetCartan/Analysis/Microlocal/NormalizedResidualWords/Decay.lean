module

public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Actual

/-!
# Uniform finite summation of the actual residual words

`finiteChain_observation_rapidDecayAt` supplies the analytic estimate for each
ordered word. Finite summation supplies exactly `hchain` of
`rapidDecayAt_inverse_of_finite_chains`. The alphabet and geometry precede the
family index, which may encode Q/B, admissible histories and source frequency.
The accuracy-dependent constants therefore still precede that index.

The source tail, localizers, leakage, polynomial costs and terminal angular
estimate remain producer obligations of `both-localized-response` and
`both-response-transfer`. No existence theorem gains a chain-decay premise.
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
open Characteristic.EvolutionIntegral ArbitraryAccuracy ResponseTransfer

/-- Match the existing chain recursion to a word in application order.
The finite-chain analytic theorem can act on the underlying real space of
complex data, with inclusion before the chain and real part only in the
terminal observation (`app:ch_regular:lem:finite-chain`). -/
theorem factorChain_eq_orderedWord {α ι X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (T : α → ι → X →L[ℝ] X) (w : ℕ → α)
    (u : ι → X) (j : ℕ) (i : ι) :
    factorChain (fun k i ↦ (T (w k) i).toLinearMap) u j i =
      orderedWord (fun a ↦ T a i) (fun k : Fin j ↦ w k) (u i) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [factorChain, orderedWord_succ]
    change T (w j) i
      (factorChain (fun k i ↦ (T (w k) i).toLinearMap) u j i) = T (w j) i _
    rw [ih]
    rfl

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

include hsupp R C hb

/-- Finite summation of exact ordered words supplies the inverse theorem's
`hchain` for the actual normalized residual. Every word estimate is uniform
over the same varying family; no constants are chosen after its index
(`app:ch_regular:eq:finite-observation`, `app:ch_regular:eq:chain-tail`). -/
theorem realResidual_hchain_of_orderedWords
    (G : GradedScale F) (s : ℕ) (ρ A : ι → ℝ) (D : ι → RH →ₗ[ℝ] F) (u : ι → RH)
    (hword : ∀ j (w : Fin j → Alphabet), RapidDecayAt G s ρ A
      (fun i ↦ D i (realCompression (orderedWord (letters i) w) (u i)))) :
    ∀ j, RapidDecayAt G s ρ A (fun i ↦ D i
      ((realResidual f hK (L i) (Q i) (B i) output ho hob (W₁ i) (retarded i) ^ j) (u i))) := by
  classical
  intro j
  have he i := observation_realResidual_pow_eq_sum f hK (L i) (Q i) (B i) (W₁ i)
    output ho hob hib (T i) hsupp (R i) (C i) (hb i) (D i) j (u i)
  simp_rw [he]
  exact rapidDecayAt_chain_sum Finset.univ s (fun w _ ↦ hword j w)

/-- The exact terminal source discrepancy, with one identity subtraction
and any fixed real linear restriction, satisfies `hchain` once the analytic
producer proves the individual complete-word observations
(`app:ch_regular:eq:resolved-angular-tail`). This is a deduction, not an
unconditional arbitrary-accuracy or inverse construction. -/
theorem angular_realResidual_hchain_of_orderedWords
    (G : GradedScale F) (s : ℕ) (ρ A : ι → ℝ) (D : RH →ₗ[ℝ] F) (u : ι → RH)
    (hword : ∀ j (w : Fin j → Alphabet), RapidDecayAt G s ρ A
      (fun i ↦ D ((realSource f hK (L i) output ho hob - 1)
        (realCompression (orderedWord (letters i) w) (u i))))) :
    ∀ j, RapidDecayAt G s ρ A (fun i ↦ D ((realSource f hK (L i) output ho hob - 1)
      ((realResidual f hK (L i) (Q i) (B i) output ho hob (W₁ i) (retarded i) ^ j) (u i)))) :=
  realResidual_hchain_of_orderedWords f hK output ho hob hib hsupp L Q B W₁ T R C hb
    G s ρ A (fun i ↦ D.comp (realSource f hK (L i) output ho hob - 1).toLinearMap) u hword

end JanetCartan.RegularSector.NormalizedResidualWords
