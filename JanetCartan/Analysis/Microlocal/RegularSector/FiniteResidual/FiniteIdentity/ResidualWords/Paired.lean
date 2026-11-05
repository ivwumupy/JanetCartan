module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.Real
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators

/-!
# Complete residual words grouped by literal conjugate pairs

The primitive leakage estimates apply to each complete physical conjugate
pair. Group the existing signed alphabet into exactly those pairs before
real compression. Distributivity then retains every ordered characteristic,
elliptic and reflected word in the original normalized residual. The same
measurement masks stay inside every factor, and adjunction reverses words.
Consumers: `finiteChain_observation_rapidDecayAt` and
`rapidDecayAt_inverse_of_finite_chains` (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.PdoRealization FiniteAssembly FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds Realization
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.RetardedLocalization LocalSobolev
open ArbitraryAccuracy.ResidualLocalization NormalizedSolver
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))

/-- One complete conjugate pair from the existing signed alphabet. Each
summand retains its external half, full B and physical masks. This is a
regrouping of the same residual, not a new selection
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def selectedFullPairedResidualTerm
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (a : (f.centers × Fin 3) ⊕ Unit) : H →L[ℂ] H :=
  selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T (a, false) +
    selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T (a, true)

/-- Each grouped letter is exactly the physical pair consumed by the
primitive leakage estimates (`app:ch_regular:eq:chain-tail`). -/
theorem selectedFullPairedResidualTerm_eq_physicalPair
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (a : (f.centers × Fin 3) ⊕ Unit) :
    selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a =
      physicalPairedSectorSum {()} (fun _ : Unit ↦
        selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T (a, false)) := by
  simp only [selectedFullPairedResidualTerm, selectedFullPhysicalResidualTerm,
    physicalPairedSectorSum, Finset.sum_singleton, Bool.false_eq_true, ↓reduceIte]

/-- The elliptic letter uses the published global residual on the same
family, with the common output before the external half and conjugation
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selectedFullPairedResidualTerm_elliptic
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H) :
    selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T (Sum.inr ()) =
      normalizedPair ((sourceCutMultiplier output ho hob).comp
        (EllipticComplement.ellipticResidual f hK L Q B)) := by
  rw [selectedFullPairedResidualTerm_eq_physicalPair]
  rfl

/-- A complete pair preserves real data in the finite chain
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
private theorem pairedResidual_physicalPair_star (S : H →L[ℂ] H) (v : H) :
    physicalPairedSectorSum {()} (fun _ : Unit ↦ S) (star v) =
      star (physicalPairedSectorSum {()} (fun _ : Unit ↦ S) v) := by
  simp only [physicalPairedSectorSum, Finset.sum_singleton]
  change S (star v) + star (S (star (star v))) = star (S v + star (S (star v)))
  simp only [star_add, star_star]
  exact add_comm _ _

/-- Each measured grouped letter preserves real data in both literal
orientations. No reflection of the selected chart label is used
(`app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFullPairedResidualTerm_measured_direction_star
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool) (u : H) :
    let P := measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a)
    (if backward then P.adjoint else P) (star u) =
      star ((if backward then P.adjoint else P) u) := by
  intro P
  dsimp only [P]
  rw [selectedFullPairedResidualTerm_eq_physicalPair, ← physicalPair_measuredOperator]
  cases backward
  · exact pairedResidual_physicalPair_star _ _
  · simp only [ite_true, physicalPairedSectorSum_adjoint_eq]
    exact pairedResidual_physicalPair_star _ _

/-- The actual normalized residual is the sum of all grouped
characteristic and elliptic letters, retaining the original algebraic
certificate (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selectedFullResidual_eq_sum_paired_terms
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    pairedResidual f hK L Q B output ho hob W₁ retarded =
      ∑ a, selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a := by
  classical
  intro retarded
  rw [pairedResidual, normalizedPair,
    selectedFullResidual_physicalPair_eq_sum_terms f hK L Q B W₁ output ho hob hib hsupp R C hb T]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, selectedFullPairedResidualTerm]
  apply Finset.sum_congr rfl
  intro a _
  exact add_comm _ _

/-- Real compression is additive over complete conjugate pairs, on the
original measured domain (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_measured_real_eq_sum_paired_terms
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : (f.centers × Fin 3) ⊕ Unit ↦ localRealCompression hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a))
    let P := localRealCompression hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (pairedResidual f hK L Q B output ho hob W₁ retarded))
    P = ∑ a, J a := by
  classical
  intro retarded J P
  dsimp only [P]
  rw [selectedFullResidual_eq_sum_paired_terms f hK L Q B W₁ output ho hob hib hsupp R C hb T]
  ext1 u
  simp only [J, localRealCompression, localRetardedOperator, measuredOperator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', sum_apply, map_sum]

/-- Distributivity preserves ordered factors in the grouped expansion
(`app:ch_regular:lem:finite-chain`). -/
private theorem pairedResidual_pow_sum {α R : Type*} [Fintype α] [Semiring R]
    (T : α → R) (n : ℕ) :
    (∑ a, T a) ^ n = ∑ w : Fin n → α, (List.ofFn (fun j ↦ T (w j))).prod := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)) _ _
      (fun w ↦ by simp [List.ofFn_succ])

/-- Literal adjunction reverses every ordered grouped word
(`app:ch_regular_base:eq:measured-adjoint`). -/
private theorem pairedResidual_adjoint_word {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (l : List (X →L[ℝ] X)) :
    l.prod.adjoint = (l.reverse.map (fun S ↦ S.adjoint)).prod := by
  induction l with
  | nil => simp
  | cons T l ih =>
    change (T.comp l.prod).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, ih]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rfl

/-- Every power of the actual real residual contains every ordered
word of complete conjugate pairs. Expanding each pair recovers all reflected
and mixed characteristic/elliptic words; no chartwise power replaces the
full sum (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_measured_real_pow_eq_sum_paired_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (n : ℕ) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : (f.centers × Fin 3) ⊕ Unit ↦ localRealCompression hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a))
    let P := localRealCompression hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (pairedResidual f hK L Q B output ho hob W₁ retarded))
    P^n = ∑ w : Fin n → (f.centers × Fin 3) ⊕ Unit,
      (List.ofFn (fun j ↦ J (w j))).prod := by
  classical
  intro retarded J P
  rw [show P = ∑ a, J a from selectedFullResidual_measured_real_eq_sum_paired_terms
    f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU]
  exact pairedResidual_pow_sum J n

/-- The literal adjoint reverses each complete real word and all its
measurement factors (`app:ch_regular_base:eq:measured-adjoint`,
`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_measured_real_pow_adjoint_eq_sum_paired_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (n : ℕ) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : (f.centers × Fin 3) ⊕ Unit ↦ localRealCompression hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a))
    let P := localRealCompression hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (pairedResidual f hK L Q B output ho hob W₁ retarded))
    (P^n).adjoint = ∑ w : Fin n → (f.centers × Fin 3) ⊕ Unit,
      ((List.ofFn (fun j ↦ J (w j))).reverse.map (fun S ↦ S.adjoint)).prod := by
  classical
  intro retarded J P
  rw [show P^n = _ from selectedFullResidual_measured_real_pow_eq_sum_paired_words
    f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact pairedResidual_adjoint_word _

/-- Real inclusion intertwines each grouped measured letter with its
actual complex operator. This justifies composing the real letters used by
`finiteChain_observation_rapidDecayAt`; individual nonreal signed summands
are never compressed before composition (`app:ch_regular:eq:chain-tail`). -/
theorem selectedFullPairedResidualTerm_inclusion_localRealCompression
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool)
    {U : Set E} (hU : MeasurableSet U) (u : LocalL2 U RF) :
    let P := measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPairedResidualTerm f hK L Q B W₁ output ho hob hib T a)
    let D := if backward then P.adjoint else P
    l2ComplexInclusion (volume.restrict U) (localRealCompression hU U D u) =
      localRetardedOperator hU U D (l2ComplexInclusion (volume.restrict U) u) := by
  intro P D
  exact ArbitraryAccuracy.SelectedLocalization.inclusion_localRealCompression_of_star
    hU D (selectedFullPairedResidualTerm_measured_direction_star
      f hK L Q B W₁ output ho hob hib T μ ν hμ hν hμb hνb a backward) u

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
