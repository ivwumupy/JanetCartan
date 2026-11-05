module

public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Actual
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.Real
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectConstruction.Localization

/-!
# The literal measured residual and its signed complex words

Reuse the existing local signed-word theorem. Its list order is composition
order (the last list entry acts first). Every letter is the original measured
operator followed by restriction, with zero extension on its input. Products
therefore retain an inserted zero-extension/restriction between adjacent
global factors. No support absorption is asserted.

The final theorem identifies the actual L²-to-Lᵖ implementation used by
`FixedDomainInverse.FullSource`, using its proved a.e. identification.
Sources: `app:ch_regular:thm:exact-correction`, `app:ch_regular:lem:finite-chain`.
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
open ArbitraryAccuracy.ResidualLocalization LocalSobolev SmallSupport
open JanetCartan.CharacteristicTransport.CompleteResidual

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "RH" => Lp RF 2 (volume : Measure E)

variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
variable (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
variable (B : Euclidean (d+1) → MetricTensor (d+1))
variable (W₁ : f.centers → TwoTimeAmplitude d (d+1))
variable (output : Euclidean (d+1) → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
variable (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
variable (T : f.centers → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1))
variable (hsupp : tsupport output ⊆ ball x f.physicalRadius) (R C : f.centers → ℝ)
variable (hb : ∀ p, GraphNormalAmplitudeBounds
  (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
    (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
variable (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
variable (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
variable {U : Set (Euclidean (d+1))} (hU : MeasurableSet U)

local notation "retarded" => (sourceCutMultiplier output ho hob).comp
  ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
    (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
local notation "letters" => selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T
local notation "Alphabet" => ((f.centers × Fin 3) ⊕ Unit) × Bool
local notation "J" => fun a : Alphabet ↦ localRetardedOperator hU U
  (measuredOperator μ ν hμ hν hμb hνb (letters a))
local notation "P" => measuredOperator μ ν hμ hν hμb hνb
  (pairedResidual f hK L Q B output ho hob W₁ retarded)

include hsupp R C hb

/-- The real local power is compression of the whole signed complex words
on the SAME local measure. Each `J` retains its literal restriction and zero
extension (`app:ch_regular:eq:chain-tail`). This instantiates the published
local word producer at the actual corrected `pairedResidual`. -/
theorem measured_realResidual_pow_eq_sum_words (j : ℕ) (u : LocalL2 U RF) :
    ((localRealCompression hU U P) ^ j) u =
      ∑ w : Fin j → Alphabet, l2RealPart (volume.restrict U)
        ((List.ofFn (fun k ↦ J (w k))).prod (l2ComplexInclusion (volume.restrict U) u)) := by
  have he := selectedFullResidual_measured_real_pow_eq_sum_words
    f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU j u
  dsimp only at he
  rw [physicalPair_measuredOperator] at he
  have hr := congrArg (l2RealPart (volume.restrict U)) he
  simpa only [realPart_inclusion, map_sum, pairedResidual, normalizedPair] using hr

/-- Literal real adjunction reverses the entire local word and exchanges
the measurement masks in each factor (`measured-adjoint`). -/
theorem measured_realResidual_pow_adjoint_eq_sum_words (j : ℕ) (u : LocalL2 U RF) :
    ((localRealCompression hU U P) ^ j).adjoint u =
      ∑ w : Fin j → Alphabet, l2RealPart (volume.restrict U)
        (((List.ofFn (fun k ↦ J (w k))).reverse.map (fun S ↦ S.adjoint)).prod
          (l2ComplexInclusion (volume.restrict U) u)) := by
  have he := selectedFullResidual_measured_real_pow_adjoint_eq_sum_words
    f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU j u
  dsimp only at he
  rw [physicalPair_measuredOperator] at he
  have hr := congrArg (l2RealPart (volume.restrict U)) he
  simpa only [realPart_inclusion, map_sum, pairedResidual, normalizedPair] using hr

/-- Observe a measured power only after zero extension to the source's
actual global domain. The terminal angular operator subtracts exactly one
identity, and the supplied final real restriction is left in place
(`app:ch_regular:eq:finite-observation`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem angular_observation_measured_pow_eq_sum
    {F : Type*} [AddCommGroup F] [Module ℝ F] (D : RH →ₗ[ℝ] F)
    (j : ℕ) (u : LocalL2 U RF) :
    D ((realSource f hK L output ho hob - 1)
      (zeroExtend hU (((localRealCompression hU U P) ^ j) u))) =
      ∑ w : Fin j → Alphabet, D ((realSource f hK L output ho hob - 1)
        (zeroExtend hU (l2RealPart (volume.restrict U)
          ((List.ofFn (fun k ↦ J (w k))).prod
            (l2ComplexInclusion (volume.restrict U) u))))) := by
  rw [measured_realResidual_pow_eq_sum_words f hK L Q B W₁ output ho hob hib T hsupp R C hb]
  simp only [map_sum]

omit hsupp R C hb in
/-- Identify the actual cutoff inverse residual with the measured normalized
pair. This uses the existing Lᵖ-to-L² representative theorem and its precise
output-support hypothesis; it does not identify local and global powers
(`app:ch_regular:thm:exact-correction`). -/
theorem localizedResidual_normalized_eq_measured
    (c : E) {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ U)
    (hmem : ∀ u, MemRestrictionSobolev (ball c r) 1
      (localRealCompression hU (ball c r)
        (pairedResidual f hK L Q B output ho hob W₁ retarded) u))
    {budget : ℝ} (hbudget : 0 ≤ budget)
    (hbound : ∀ u, restrictionSobolevNorm (ball c r) 1
      (localRealCompression hU (ball c r)
        (pairedResidual f hK L Q B output ho hob W₁ retarded) u) ≤ budget * ‖u‖)
    (χ₂ χ₃ : ContDiffBump x) (hs₂ : tsupport (χ₂ : E → ℝ) ⊆ ball c r) :
    localizedResidual (two_lt_ballSobolevExponent c hr).le
      χ₂ χ₃ isOpen_ball.measurableSet
      (FixedDomainInverse.residualToLpOnBall c hr hball _ hmem hbudget hbound) =
      localRealCompression hU U
        (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
          (pairedResidual f hK L Q B output ho hob W₁ retarded)) := by
  simpa only [physicalPair_measuredOperator, pairedResidual, normalizedPair] using
    FixedDomainInverse.localizedResidual_eq_real_measuredOperator hU c hr hball
      ((1/2 : ℂ) • (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
        (sourceCutMultiplier output ho hob).comp (EllipticComplement.ellipticResidual f hK L Q B)))
      hmem hbudget hbound χ₂ χ₃ hs₂

end JanetCartan.RegularSector.NormalizedResidualWords
