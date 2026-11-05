module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualTerms
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn

/-!
# All ordered words of the same measured residual

Every finite power contains every ordered chart/term/conjugate word. The
original measurement and source masks remain inside each letter. Literal
adjunction reverses the whole word, as well as every factor's physical masks.
These are exact identities for the characteristic branch and the literal
half-scaled characteristic-plus-elliptic sum, consumed
by `finiteChain_observation_rapidDecayAt` and ultimately
`rapidDecayAt_inverse_of_finite_chains`. Analytic leakage estimates, the
normalized solver PDE construction and analytic bounds for all mixed words
remain separate obligations. The additional full-residual identities below
instantiate the published elliptic operator and retain both external halves.
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
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Distributivity retains every ordered word, without a commutativity
assumption (`app:ch_regular:lem:finite-chain`). -/
private theorem sum_pow_ordered {α R : Type*} [Fintype α] [Semiring R]
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

/-- Adjoint of a literal ordered composition, including the reversed order
(`app:ch_regular_base:eq:adjoint-integrated-term`). -/
private theorem adjoint_list_prod {X : Type*} [NormedAddCommGroup X]
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

/-- The actual measured plus pair is the sum of all selected
chart/term/conjugate letters, with zero extension and restriction in their
original places. No containment or plateau is needed for this operator identity
(`app:ch_regular:lem:finite-chain`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFiniteDirectResidual_measured_physicalPair_eq_sum_terms
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
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
    let J := fun a : (f.centers × Fin 3) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedPhysicalResidualTerm f L Q B W₁ output ho hob hib T a))
    localRetardedOperator hU U (physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded))) = ∑ a, J a := by
  classical
  intro retarded J
  rw [physicalPair_measuredOperator,
    selectedFiniteDirectResidual_physicalPair_eq_sum_terms f L Q B W₁ output ho hob hib
      hsupp R C hb T]
  ext1 u
  simp only [J, localRetardedOperator, measuredOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', sum_apply, map_sum]

/-- The nth power of the actual measured residual includes every ordered
word, including mixed characteristic charts, the three distinct residual
terms, and literal conjugates. The empty word is the identity. This supplies
the exact sum for `rapidDecayAt_inverse_of_finite_chains`; no wordwise decay
is assumed or asserted (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFiniteDirectResidual_measured_physicalPair_pow_eq_sum_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
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
    let J := fun a : (f.centers × Fin 3) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedPhysicalResidualTerm f L Q B W₁ output ho hob hib T a))
    (localRetardedOperator hU U (physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded)))) ^ n =
      ∑ w : Fin n → (f.centers × Fin 3) × Bool,
        (List.ofFn (fun j ↦ J (w j))).prod := by
  classical
  intro retarded J
  rw [selectedFiniteDirectResidual_measured_physicalPair_eq_sum_terms
    f L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU]
  exact sum_pow_ordered J n

/-- Literal adjunction reverses each complete measured residual word.
In particular every intermediate right/left measurement mask is retained;
the forward word is never silently reused as its adjoint
(`app:ch_regular_base:eq:adjoint-integrated-term`,
`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:lem:finite-chain`). -/
theorem selectedFiniteDirectResidual_measured_physicalPair_pow_adjoint_eq_sum_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
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
    let J := fun a : (f.centers × Fin 3) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedPhysicalResidualTerm f L Q B W₁ output ho hob hib T a))
    ((localRetardedOperator hU U (physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded)))) ^ n).adjoint =
      ∑ w : Fin n → (f.centers × Fin 3) × Bool,
        ((List.ofFn (fun j ↦ J (w j))).reverse.map (fun S ↦ S.adjoint)).prod := by
  classical
  intro retarded J
  rw [selectedFiniteDirectResidual_measured_physicalPair_pow_eq_sum_words
    f L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact adjoint_list_prod _

/-- The externally normalized complete measured pair is the sum of all
characteristic, elliptic and conjugate letters, with zero extension and
restriction in their original places. No containment or plateau is needed for this identity
(`app:ch_regular:lem:finite-chain`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFullResidual_measured_physicalPair_eq_sum_terms
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
    let J := fun a : ((f.centers × Fin 3) ⊕ Unit) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a))
    localRetardedOperator hU U (physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        ((1 / 2 : ℂ) •
          (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
            (sourceCutMultiplier output ho hob).comp
              (EllipticComplement.ellipticResidual f hK L Q B))))) = ∑ a, J a := by
  classical
  intro retarded J
  rw [physicalPair_measuredOperator,
    selectedFullResidual_physicalPair_eq_sum_terms f hK L Q B W₁ output ho hob hib
      hsupp R C hb T]
  ext1 u
  simp only [J, localRetardedOperator, measuredOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', sum_apply, map_sum]

/-- Every power of the actual half-scaled characteristic-plus-elliptic
residual includes every ordered mixed word, including both orientations and
the three distinct characteristic terms. Each letter retains its own half.
The empty word is the identity. This supplies
the exact sum for `rapidDecayAt_inverse_of_finite_chains`; no wordwise decay
is assumed or asserted (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_measured_physicalPair_pow_eq_sum_words
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
    let J := fun a : ((f.centers × Fin 3) ⊕ Unit) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a))
    (localRetardedOperator hU U (physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        ((1 / 2 : ℂ) •
          (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
            (sourceCutMultiplier output ho hob).comp
              (EllipticComplement.ellipticResidual f hK L Q B)))))) ^ n =
      ∑ w : Fin n → ((f.centers × Fin 3) ⊕ Unit) × Bool,
        (List.ofFn (fun j ↦ J (w j))).prod := by
  classical
  intro retarded J
  rw [selectedFullResidual_measured_physicalPair_eq_sum_terms
    f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU]
  exact sum_pow_ordered J n

/-- Literal adjunction reverses each normalized complete residual word,
including every mixed characteristic/elliptic and reflected word.
In particular every intermediate right/left measurement mask is retained;
the forward word is never silently reused as its adjoint
(`app:ch_regular_base:eq:adjoint-integrated-term`,
`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_measured_physicalPair_pow_adjoint_eq_sum_words
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
    let J := fun a : ((f.centers × Fin 3) ⊕ Unit) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a))
    ((localRetardedOperator hU U (physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        ((1 / 2 : ℂ) •
          (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
            (sourceCutMultiplier output ho hob).comp
              (EllipticComplement.ellipticResidual f hK L Q B)))))) ^ n).adjoint =
      ∑ w : Fin n → ((f.centers × Fin 3) ⊕ Unit) × Bool,
        ((List.ofFn (fun j ↦ J (w j))).reverse.map (fun S ↦ S.adjoint)).prod := by
  classical
  intro retarded J
  rw [selectedFullResidual_measured_physicalPair_pow_eq_sum_words
    f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact adjoint_list_prod _

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
