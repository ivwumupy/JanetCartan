module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.Operators
public import JanetCartan.Analysis.Microlocal.EllipticComplement.Symbol

/-!
# Literal terms of one selected physical residual

Split the actual characteristic residual into its endpoint, retarded, and
full-B algebraic derivative terms, then retain their whole physical conjugates.
The same selected family, two physical masks and enlarged radial collar occur
in every term. These identities supply the factors for the ordered-word
expansion required by `app:ch_regular:lem:finite-chain`. The full alphabet also
includes the published elliptic residual on the same family, with the external
one-half factors. These identities assert no decay of the angular discrepancy
or normalized solver PDE construction.
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

/-- Additivity exposes the literal conjugate label in each finite residual
letter (`app:ch_regular_base:eq:signed-physical-normalization`). -/
private theorem physicalPair_sum_eq_signed_sum {α : Type*} [Fintype α]
    (T : α → H →L[ℂ] H) :
    physicalPairedSectorSum {()} (fun _ : Unit ↦ ∑ a, T a) =
      ∑ a : α × Bool, if a.2 then boundedConjugate (T a.1) else T a.1 := by
  classical
  ext1 u
  simp only [physicalPairedSectorSum, Finset.sum_singleton, Fintype.sum_prod_type,
    Fintype.sum_bool, ite_true, sum_apply, add_apply]
  change (∑ a, T a u) + star ((∑ a, T a) (star u)) =
    ∑ a, (star (T a (star u)) + T a u)
  rw [sum_apply, star_sum, Finset.sum_add_distrib]
  exact add_comm _ _

/-- The three literal common-chart residual terms: the retained W₁ endpoint,
the retarded PW₁ factor, and the derivative of the algebraic inverse with full B.
The original input mask and the identical `2*L` collar remain in place.
Consumer: the residual-word expansion for `app:ch_regular:lem:finite-chain`;
source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def selectedCommonChartResidualTerm
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : H →L[ℂ] H) :
    Fin 3 → H →L[ℂ] H :=
  ![maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p L Q W₁),
    selectedCommonChartRetarded f p output ho hob hib T,
    (1 / Complex.I) • maskedPhysicalPDO
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedAlgebraicSymbol f p (2*L) Q B 1)]

/-- Splitting the actual common-chart residual retains all three terms and
the physical scalar `1/i` (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selectedCommonChartResidual_eq_sum_terms
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : H →L[ℂ] H) :
    selectedCommonChartResidual f p L Q B W₁ output ho hob hib T =
      ∑ j, selectedCommonChartResidualTerm f p L Q B W₁ output ho hob hib T j := by
  simp [selectedCommonChartResidual, selectedCommonChartResidualTerm,
    Fin.sum_univ_succ, add_assoc]

/-- The original-coordinate residual term or its literal whole-operator
conjugate. The Boolean labels operators, not another selected chart. This is the
finite alphabet for the measured residual words in `app:ch_regular:lem:finite-chain`.
All physical and Fourier multipliers remain inside the original factor. -/
def selectedPhysicalResidualTerm
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (a : (f.centers × Fin 3) × Bool) : H →L[ℂ] H :=
  let S := physicalOperator (f.chart a.1.1).index
    (selectedCommonChartResidualTerm f a.1.1 L Q B (W₁ a.1.1) output ho hob hib
      (T a.1.1) a.1.2)
  if a.2 then boundedConjugate S else S

/-- The actual unpaired analytic residual is the sum of its three terms on
every selected chart. The algebraic normal bound is retained by the protected
direct constructor. Consumer: the complete residual-word expansion
(`app:ch_regular_base:eq:energy-complete-residual`, `app:ch_regular:lem:finite-chain`). -/
theorem selectedFiniteDirectResidual_eq_sum_terms
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
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
    selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded =
      ∑ a : f.centers × Fin 3, physicalOperator (f.chart a.1).index
        (selectedCommonChartResidualTerm f a.1 L Q B (W₁ a.1) output ho hob hib (T a.1) a.2) := by
  intro retarded
  rw [show selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded = _ from
    selectedFiniteDirectResidual_eq_commonChartSum f L Q B W₁ output ho hob hib hsupp R C hb T]
  let P (a : f.centers × Fin 3) := physicalOperator (f.chart a.1).index
    (selectedCommonChartResidualTerm f a.1 L Q B (W₁ a.1) output ho hob hib (T a.1) a.2)
  have hsum : finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ selectedCommonChartResidual f p L Q B (W₁ p) output ho hob hib (T p)) =
      ∑ a, P a := by
    simp_rw [selectedCommonChartResidual_eq_sum_terms]
    ext1 u
    simp only [finitePhysicalOperator, P, Fintype.sum_prod_type, sum_apply,
      physicalOperator_apply, map_sum]
  exact hsum

/-- Expand the same selected analytic residual into all chart/term/sign
labels. The sole amplitude certificate is the algebraic normal bound already
retained by the protected direct constructor. This is an exact decomposition of
the old physical plus pair; its angular identity discrepancy remains separate.
Consumer: measured residual powers in `app:ch_regular:lem:finite-chain` and
`app:ch_regular:eq:chain-tail`. -/
theorem selectedFiniteDirectResidual_physicalPair_eq_sum_terms
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
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
    physicalPairedSectorSum {()} (fun _ : Unit ↦
      selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded) =
      ∑ a, selectedPhysicalResidualTerm f L Q B W₁ output ho hob hib T a := by
  intro retarded
  rw [selectedFiniteDirectResidual_eq_sum_terms f L Q B W₁ output ho hob hib hsupp R C hb T]
  exact physicalPair_sum_eq_signed_sum _

/-- One letter of the externally normalized complete residual. The left
label is a characteristic chart/term; the right label is the actual published
elliptic residual with the same common output. Each original or whole-conjugate
letter retains its external one-half factor. This defines the alphabet for
`app:ch_regular:lem:finite-chain`, not another solver or mask selection. -/
def selectedFullPhysicalResidualTerm
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (a : ((f.centers × Fin 3) ⊕ Unit) × Bool) : H →L[ℂ] H :=
  let S := Sum.elim
    (fun a : f.centers × Fin 3 ↦ physicalOperator (f.chart a.1).index
      (selectedCommonChartResidualTerm f a.1 L Q B (W₁ a.1) output ho hob hib (T a.1) a.2))
    (fun _ : Unit ↦ (sourceCutMultiplier output ho hob).comp
      (EllipticComplement.ellipticResidual f hK L Q B)) a.1
  if a.2 then boundedConjugate ((1 / 2 : ℂ) • S) else (1 / 2 : ℂ) • S

/-- Decompose the literal half-scaled characteristic-plus-elliptic residual
and its conjugate into all original branch labels. The elliptic operator is
instantiated from the same f; no residual estimate or normalization identity
is assumed. The order-zero source discrepancy remains outside this analytic
residual (`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_physicalPair_eq_sum_terms
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
    physicalPairedSectorSum {()} (fun _ : Unit ↦ (1 / 2 : ℂ) •
      (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
        (sourceCutMultiplier output ho hob).comp (EllipticComplement.ellipticResidual f hK L Q B))) =
      ∑ a, selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a := by
  classical
  intro retarded
  let P : (f.centers × Fin 3) ⊕ Unit → H →L[ℂ] H := Sum.elim
    (fun a : f.centers × Fin 3 ↦ physicalOperator (f.chart a.1).index
      (selectedCommonChartResidualTerm f a.1 L Q B (W₁ a.1) output ho hob hib (T a.1) a.2))
    (fun _ : Unit ↦ (sourceCutMultiplier output ho hob).comp
      (EllipticComplement.ellipticResidual f hK L Q B))
  have hsum : selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
      (sourceCutMultiplier output ho hob).comp (EllipticComplement.ellipticResidual f hK L Q B) =
      ∑ a, P a := by
    rw [selectedFiniteDirectResidual_eq_sum_terms f L Q B W₁ output ho hob hib hsupp R C hb T]
    simp only [P, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_unique]
  rw [hsum, Finset.smul_sum]
  exact physicalPair_sum_eq_signed_sum (fun a ↦ (1 / 2 : ℂ) • P a)

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
