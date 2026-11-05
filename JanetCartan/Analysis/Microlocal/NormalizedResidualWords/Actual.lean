module

public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Algebra

/-!
# Words of the actual corrected normalized residual

The alphabet is exactly `selectedFullPhysicalResidualTerm`: all three
characteristic terms on every selected chart, the global elliptic term, and
both physical signs with their external halves. The only decomposition inputs
are the support and algebraic normal-amplitude bounds of its published producer.
Consumer: `ArbitraryAccuracy.rapidDecayAt_inverse_of_finite_chains.hchain`.
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
open Characteristic.EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)

variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
variable (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
variable (B : Euclidean (d+1) → MetricTensor (d+1))
variable (W₁ : f.centers → TwoTimeAmplitude d (d+1))
variable (output : Euclidean (d+1) → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)

/-- Reality of the entire corrected residual follows from its actual
normalized pairing (`real-sector-normalization`). It is not a premise on
each signed letter. -/
theorem pairedResidual_conjugation (retarded : H →L[ℂ] H) :
    conjugateOperator (pairedResidual f hK L Q B output ho hob W₁ retarded).toLinearMap =
      (pairedResidual f hK L Q B output ho hob W₁ retarded).toLinearMap :=
  normalizedPair_conjugation _

/-- Powers of the actual real residual compress the whole complex power
(`app:ch_regular:eq:chain-tail`). This uses the proved reality of the pair. -/
theorem realResidual_pow_eq_compression (retarded : H →L[ℂ] H) (j : ℕ) :
    realResidual f hK L Q B output ho hob W₁ retarded ^ j =
      realCompression (pairedResidual f hK L Q B output ho hob W₁ retarded ^ j) :=
  realCompression_pow _ (pairedResidual_conjugation f hK L Q B W₁ output ho hob retarded) j

variable (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
variable (T : f.centers → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1))
local notation "retarded" => (sourceCutMultiplier output ho hob).comp
  ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
    (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
local notation "letters" => selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T
local notation "Alphabet" => ((f.centers × Fin 3) ⊕ Unit) × Bool

variable (hsupp : tsupport output ⊆ ball x f.physicalRadius) (R C : f.centers → ℝ)
variable (hb : ∀ p, GraphNormalAmplitudeBounds
  (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
    (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
include hsupp R C hb

/-- Identify `pairedResidual` on the original retarded sum with the published
full signed alphabet (`energy-complete-residual`). No geometry is reselected. -/
theorem pairedResidual_eq_sum_terms :
    pairedResidual f hK L Q B output ho hob W₁ retarded = ∑ a, letters a :=
  selectedFullResidual_physicalPair_eq_sum_terms f hK L Q B W₁ output ho hob
    hib hsupp R C hb T

/-- Every power of the actual corrected residual is the sum of ALL ordered
mixed words, including the empty word (`app:ch_regular:lem:finite-chain`). -/
theorem pairedResidual_pow_eq_sum_orderedWord (j : ℕ) :
    pairedResidual f hK L Q B output ho hob W₁ retarded ^ j =
      ∑ w : Fin j → Alphabet, orderedWord letters w := by
  rw [pairedResidual_eq_sum_terms f hK L Q B W₁ output ho hob hib T hsupp R C hb]
  exact sum_pow_eq_sum_orderedWord letters j

/-- The adjoint of the actual power is the sum of the reversed literal
adjoint words (`measured-adjoint`, `app:ch_regular:lem:finite-chain`). -/
theorem pairedResidual_pow_adjoint_eq_sum (j : ℕ) :
    (pairedResidual f hK L Q B output ho hob W₁ retarded ^ j).adjoint =
      ∑ w : Fin j → Alphabet,
        (List.ofFn (fun k ↦ (letters (w k)).adjoint)).prod := by
  rw [pairedResidual_pow_eq_sum_orderedWord f hK L Q B W₁ output ho hob hib T hsupp R C hb]
  simp only [map_sum, orderedWord_adjoint]

/-- Each term is the compression of one WHOLE complex word. There is no real
projection between its signed factors (`app:ch_regular:eq:chain-tail`). -/
theorem realResidual_pow_eq_sum_compressed_orderedWord (j : ℕ) :
    realResidual f hK L Q B output ho hob W₁ retarded ^ j =
      ∑ w : Fin j → Alphabet, realCompression (orderedWord letters w) := by
  rw [realResidual_pow_eq_compression,
    pairedResidual_pow_eq_sum_orderedWord f hK L Q B W₁ output ho hob hib T hsupp R C hb,
    realCompression_sum]

/-- Apply any real linear observation only after the whole-word compression.
This includes fixed restriction to the original measured domain
(`app:ch_regular:eq:finite-observation`). -/
theorem observation_realResidual_pow_eq_sum {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : RH →ₗ[ℝ] F) (j : ℕ) (u : RH) :
    D ((realResidual f hK L Q B output ho hob W₁ retarded ^ j) u) =
      ∑ w : Fin j → Alphabet, D (realCompression (orderedWord letters w) u) := by
  rw [realResidual_pow_eq_sum_compressed_orderedWord f hK L Q B W₁ output ho hob
    hib T hsupp R C hb]
  simp only [sum_apply, map_sum]

/-- The terminal angular observation is exactly `realSource - 1`, followed
by the supplied real restriction. One identity is subtracted, also for the
zero-length word (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem angular_observation_realResidual_pow_eq_sum
    {F : Type*} [AddCommGroup F] [Module ℝ F] (D : RH →ₗ[ℝ] F) (j : ℕ) (u : RH) :
    D ((realSource f hK L output ho hob - 1)
      ((realResidual f hK L Q B output ho hob W₁ retarded ^ j) u)) =
      ∑ w : Fin j → Alphabet, D ((realSource f hK L output ho hob - 1)
        (realCompression (orderedWord letters w) u)) :=
  observation_realResidual_pow_eq_sum f hK L Q B W₁ output ho hob hib T hsupp R C hb
    (D.comp (realSource f hK L output ho hob - 1).toLinearMap) j u

end JanetCartan.RegularSector.NormalizedResidualWords
