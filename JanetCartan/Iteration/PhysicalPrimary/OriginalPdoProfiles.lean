module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.AlgebraicSums
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPdoProfilesTemplate

/-!
# Actual native endpoint and algebraic symbol profiles

Retain the ORIGINAL regular endpoint constants and select the ORIGINAL algebraic
certificate tuple once, before the physical history. Only their fixed finite
center profiles are majorized. The same full Q/B, order-one endpoint amplitude,
phase/chart/operator, source and masks are unchanged.

Consumers are `PhysicalEllipticWords.exists_physical_history_measured_residual_hstep`
and `PhysicalPrimary.exists_physical_history_paired_solver_hstep`
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_regular_base:eq:energy-complete-residual`, `complement-symbol`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 12000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalPdoProfiles
open FourierIntegral Pseudodifferential AmplitudeBound
open RegularSector.FinitePdo RegularSector.FiniteAlgebraic RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.AlgebraicSymbols RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.PdoRealization RegularSector.Characteristic.AmplitudeBounds
open CharacteristicTransport.CompleteResidual

/-- Only the fixed original finite centers enter this profile; it is selected
before all histories, frequencies and source parameters (`new:sec:order-of-choices`). -/
def finite_profile_majorant {ι : Type*} [Fintype ι] (D : ι → ℕ → ℝ) : ℕ → ℝ :=
  fun j ↦ 1 + ∑ p, |D p j|

/-- The same finite majorant is nonnegative, including the empty-center case
(`new:sec:order-of-choices`). -/
theorem finite_profile_majorant_nonneg {ι : Type*} [Fintype ι]
    (D : ι → ℕ → ℝ) (j : ℕ) : 0 ≤ finite_profile_majorant D j :=
  add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- Every original center is dominated without any sampling-family count
(`new:sec:order-of-choices`). -/
theorem le_finite_profile_majorant {ι : Type*} [Fintype ι]
    (D : ι → ℕ → ℝ) (p : ι) (j : ℕ) : D p j ≤ finite_profile_majorant D j := by
  classical
  exact (le_abs_self _).trans ((Finset.single_le_sum (fun q _ ↦ abs_nonneg (D q j))
    (Finset.mem_univ p)).trans (le_add_of_nonneg_left zero_le_one))

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat

/-- Enlarge only the three symbol-budget fields. Both the retained positive and
negative signed operator gains, including the literal adjoint, are copied
unchanged (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem endpoint_profile_mono {i : Fin (d+1)} {KQ : Set E}
    {Q : E → Coeff} {B : E → Mat} {χout χsource : E → ℂ}
    {c : E → E → CMat} {R M : ℝ} {D D' Dgain G : ℕ → ℝ}
    (hM : 0 ≤ M) (hD : ∀ j, D j ≤ D' j)
    (h : EndpointPdoEstimates i KQ Q B χout χsource c R M D Dgain G) :
    EndpointPdoEstimates i KQ Q B χout χsource c R M D' Dgain G := by
  have low : 0 ≤ 1+M+M := add_nonneg (add_nonneg zero_le_one hM) hM
  refine ⟨⟨h.1.smooth,h.1.support,fun ξ is hi z ↦
    (h.1.derivative ξ is hi z).trans (mul_le_mul_of_nonneg_right (hD _) low)⟩,
    (fun ξ is hi z ↦ (h.2.1 ξ is hi z).trans (mul_le_mul_of_nonneg_right (hD _) low)),
    (fun m ξ is hi z ↦ (h.2.2.1 m ξ is hi z).trans
      (mul_le_mul_of_nonneg_right (hD m) ?_)),h.2.2.2⟩
  exact add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)

/-- Preserve the actual normal box and normal constant, and majorize only the
all-order algebraic derivative profile (`complement-symbol`). -/
theorem algebraic_profile_mono {KQ : Set E} {Q : E → Coeff} {B : E → Mat}
    {χout χsource : E → ℂ} {c : E → E → CMat} {R N : ℝ} {C D : ℕ → ℝ}
    (hC : ∀ j, C j ≤ D j)
    (h : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R N ∧
      ∀ j ξ is, is.length ≤ j → ∀ z,
        (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
            C j * (1+cNorm KQ (j+1) Q+cNorm KQ (j+1) B)) :
    GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R N ∧
      ∀ j ξ is, is.length ≤ j → ∀ z,
        (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
            D j * (1+cNorm KQ (j+1) Q+cNorm KQ (j+1) B) := by
  refine ⟨h.1,fun j ξ is hi z ↦ (h.2 j ξ is hi z).trans
    (mul_le_mul_of_nonneg_right (hC j) ?_)⟩
  exact add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)

/-- The doubled native threshold is still admitted by the one original
algebraic constructor (`complement-symbol`). -/
theorem twice_admitted_threshold {a L : ℝ} (ha : 1 ≤ a) (hL : a ≤ L) : a ≤ 2*L := by
  linarith

/-- Order zero is precisely the native algebraic inverse b; order one is the
FULL physical symbol derivative pb, including B (`energy-complete-residual`). -/
theorem selected_algebraic_symbol_mem {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Coeff} {K : Set E} (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) (L : ℝ) (Q : E → Coeff) (B : E → Mat) (o : Fin 2) :
    let c := f.chart p
    let b := directAlgebraicSymbol
      (conicBminus c.radialSection c.index Q (fieldRoot (coordinateSplit c.index) Q c.root) c.row c.col)
      (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask)
      (fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ))
    let pb := physicalSymbolApply
      (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b
    selectedAlgebraicSymbol f p L Q B o ∈ ({b,pb} : Set (E → E → CMat)) := by
  classical
  dsimp only
  unfold selectedAlgebraicSymbol
  split_ifs <;> simp

end JanetCartan.PhysicalPrimary.OriginalPdoProfiles

set_option maxHeartbeats 600000 in
retain_original_pdo_static_profiles

set_option maxHeartbeats 600000 in
apply_original_current_pdo_profiles
