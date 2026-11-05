module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.NegativeBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.AdjointRegularization
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity

/-!
# The canonical physical PDOs in the complete residual

The same `CompleteResidual.maskedPhysicalPDO` is identified with the existing
vector two-position PDO after the explicit physical covector conversion
`η = 2 * π * ξ`. Both physical masks, Euclidean Lebesgue measure, vector Hilbert
norm and Frobenius symbol norm are retained. The helper `IntegerBounds` transfers
natural-order and gain-one estimates, forward and literal adjoint, with fixed
reserves `2 * (n + 1)` and `2 * (n + 1) + 1` and a single high symbol quantity.
`NegativeBounds` proves the corresponding negative integer estimates by
Euclidean weighted Fourier duality, including `H^(-k-1) → H^(-k)`.

`directPDOSymbols_regularizations` supplies the four actual PDO representatives
and strong limits consumed by
`CompleteResidual.completeResidual_operators_of_graph_regularizations` in
`app:ch_regular_base:eq:energy-complete-residual`. It retains any prescribed
common bounded smooth frequency sequence tending to one.

Remaining primitive sector inputs are precisely joint smoothness, a fixed
paired-position support box, and the low/high physical coordinate derivative
budgets for the literal symbols with BOTH masks. Order-minus-one terms require
the weighted budgets in `IntegerBounds`. Their producer is the sector amplitude
construction: the algebraic symbol `bminus1 * alpha`, the principal `alpha`,
the diagonal `A_t * W1 * beta`, and the full derivative `P_x(bminus1 * alpha)`.
`AmplitudeBounds.exists_rootMinorData_cNorm_bounds`,
`AmplitudeBounds.exists_twoTimeRowTransport_cNorm_bounds` and
`AmplitudeBounds.exists_pencilPhysicalAmplitudes_cNorm_bounds` supply upstream
local grades; the `jc-regular-sector` construction still owes their supported
symbol conversion and common coefficient budgets. No bound for those concrete
coefficient families is asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.PdoRealization
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds.FrequencyCutoff
open Pseudodifferential AmplitudeBound CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

/-- The exact cycle symbol of the masked physical PDO in
`app:ch_regular_base:eq:energy-complete-residual`, with the source mask on the
right and the output mask on the left. Consumer: the same residual's bounds. -/
def maskedPhysicalPDOCycleSymbol (χout χsource : E → ℂ) (c : E → E → Mat) :
    E → P → Mat :=
  physicalPDOCycleSymbol (fun x z η ↦ (χout x * χsource z) • c x η)

/-- Pointwise identification retains the original multiplier order and performs
only the frequency conversion `η = 2πξ` (`energy-complete-residual`). -/
@[simp] theorem maskedPhysicalPDOCycleSymbol_pairedPosition
    (χout χsource : E → ℂ) (c : E → E → Mat) (ξ x z : E) :
    maskedPhysicalPDOCycleSymbol χout χsource c ξ (pairedPosition x z) =
      (χout x * χsource z) • c x ((2 * Real.pi) • ξ) :=
  physicalPDOCycleSymbol_pairedPosition _ ξ x z

/-- The actual canonical PDO used by the complete residual equals the existing
matrix Sobolev operator. There is no graph realization or equality premise;
the proof uses the literal compact-test integrals and density.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem maskedPhysicalPDO_eq_vectorTwoPositionL2Operator
    (χout χsource : E → ℂ) (c : E → E → Mat) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M) :
    maskedPhysicalPDO χout χsource c =
      vectorTwoPositionL2Operator (Nat.succ_pos d) R
        (maskedPhysicalPDOCycleSymbol χout χsource c) hb.smooth hb.support M hb.entry_bound :=
  canonicalGraph_eq_vectorTwoPositionL2Operator (Nat.succ_pos d) R _
    hb.smooth hb.support M hb.entry_bound

/-- A finite family retains ONE prescribed smooth frequency sequence. The
actual canonical cut operators realize the literal test kernels and converge
strongly, forward and literal adjoint. Consumer: the four PDO inputs of
`completeResidual_operators_of_graph_regularizations` in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem maskedPhysicalPDO_regularizations
    (χout χsource : E → ℂ) (c : Fin 4 → E → E → Mat) (R : ℝ) (M : Fin 4 → ℝ)
    (hb : ∀ k, GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource (c k)) R (M k))
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) {C : ℝ} (hC : 1 ≤ C)
    (hθbound : ∀ j η, ‖θ j η‖ ≤ C)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1)) :
    ∃ Preg : Fin 4 → ℕ → H →L[ℂ] H,
      (∀ k j u, Preg k j (graphTestToLp u) =ᵐ[volume] graphTestOutput
        (fun x η ↦ inner ℝ x η)
        (frequencyCutFullAmplitude (θ j) (fun x z η ↦ (χout x * χsource z) • c k x η)) u) ∧
      (∀ k u, Tendsto (fun j ↦ Preg k j u) atTop
        (𝓝 (maskedPhysicalPDO χout χsource (c k) u))) ∧
      (∀ k u, Tendsto (fun j ↦ (Preg k j).adjoint u) atTop
        (𝓝 ((maskedPhysicalPDO χout χsource (c k)).adjoint u))) := by
  refine ⟨fun k j ↦ fullGraphOperator (fun x η ↦ inner ℝ x η)
    (frequencyCutFullAmplitude (θ j) (fun x z η ↦ (χout x * χsource z) • c k x η)), ?_, ?_, ?_⟩
  · intro k j u
    exact canonicalGraph_frequencyCut_realizes (Nat.succ_pos d) _ (hb k)
      (θ j) (hθ j) (zero_le_one.trans hC) (hθbound j) u
  · intro k u
    exact tendsto_canonicalGraph_frequencyCut (Nat.succ_pos d) _ (hb k)
      θ hθ hC hθbound hθlim u
  · intro k u
    exact tendsto_canonicalGraph_frequencyCut_adjoint (Nat.succ_pos d) _ (hb k)
      θ hθ hC hθbound hθlim u

/-- The cutoff-preservation output of `exists_fullGraphFamily_of_wholeImage_phase`
is enough to share its EXACT sequence with all four PDOs. Smooth physical
cutoffs construct the operators and their strong limits; preservation identifies
the finite test kernels with the graph producer's sequence. This avoids assuming
convergence for a different cutoff sequence (`energy-complete-residual`). -/
theorem maskedPhysicalPDO_regularizations_of_cutoff_preservation
    (χout χsource : E → ℂ) (c : Fin 4 → E → E → Mat) (R : ℝ) (M : Fin 4 → ℝ)
    (hb : ∀ k, GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource (c k)) R (M k))
    (θ : ℕ → E → ℂ)
    (hpres : ∀ k j, frequencyCutFullAmplitude (θ j)
      (fun x z η ↦ (χout x * χsource z) • c k x η) =
      frequencyCutFullAmplitude (complexPhysicalCutoff j)
        (fun x z η ↦ (χout x * χsource z) • c k x η)) :
    ∃ Preg : Fin 4 → ℕ → H →L[ℂ] H,
      (∀ k j u, Preg k j (graphTestToLp u) =ᵐ[volume] graphTestOutput
        (fun x η ↦ inner ℝ x η)
        (frequencyCutFullAmplitude (θ j) (fun x z η ↦ (χout x * χsource z) • c k x η)) u) ∧
      (∀ k u, Tendsto (fun j ↦ Preg k j u) atTop
        (𝓝 (maskedPhysicalPDO χout χsource (c k) u))) ∧
      (∀ k u, Tendsto (fun j ↦ (Preg k j).adjoint u) atTop
        (𝓝 ((maskedPhysicalPDO χout χsource (c k)).adjoint u))) := by
  obtain ⟨Preg, htest, hlim, hadj⟩ := maskedPhysicalPDO_regularizations χout χsource c R M hb
    complexPhysicalCutoff complexPhysicalCutoff_contDiff le_rfl
    complexPhysicalCutoff_norm_le complexPhysicalCutoff_tendsto
  exact ⟨Preg, fun k j u ↦ (hpres k j).symm ▸ htest k j u, hlim, hadj⟩

/-- Specialization to the FOUR literal symbols of the physical direct solver
and complete residual, including the diagonal correction and the derivative of
the whole algebraic symbol. This is the PDO producer consumed by
`completeResidual_operators_of_graph_regularizations`; the sector owner supplies
the displayed primitive budgets on these SAME symbols.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem directPDOSymbols_regularizations
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W₁ : EvolutionIntegral.TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ) (β χout χsource : E → ℂ)
    (R : ℝ) (M : Fin 4 → ℝ)
    (hb : ∀ k, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol χout χsource (directPDOSymbols A B W₁ bminus σ β k)) R (M k))
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) {C : ℝ} (hC : 1 ≤ C)
    (hθbound : ∀ j η, ‖θ j η‖ ≤ C)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1)) :
    let c := directPDOSymbols A B W₁ bminus σ β
    ∃ Preg : Fin 4 → ℕ → H →L[ℂ] H,
      (∀ k j u, Preg k j (graphTestToLp u) =ᵐ[volume] graphTestOutput
        (fun x η ↦ inner ℝ x η)
        (frequencyCutFullAmplitude (θ j) (fun x z η ↦ (χout x * χsource z) • c k x η)) u) ∧
      (∀ k u, Tendsto (fun j ↦ Preg k j u) atTop
        (𝓝 (maskedPhysicalPDO χout χsource (c k) u))) ∧
      (∀ k u, Tendsto (fun j ↦ (Preg k j).adjoint u) atTop
        (𝓝 ((maskedPhysicalPDO χout χsource (c k)).adjoint u))) :=
  maskedPhysicalPDO_regularizations χout χsource _ R M hb θ hθ hC hθbound hθlim

/-- Choose one concrete smooth compact frequency sequence for all four direct
PDOs and construct every literal representative and strong limit. The chosen
sequence is `complexPhysicalCutoff`; when the retarded graph producer uses its
collared version, `maskedPhysicalPDO_regularizations_of_cutoff_preservation`
retains that exact common sequence instead.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_directPDOSymbols_regularizations
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W₁ : EvolutionIntegral.TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ) (β χout χsource : E → ℂ)
    (R : ℝ) (M : Fin 4 → ℝ)
    (hb : ∀ k, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol χout χsource (directPDOSymbols A B W₁ bminus σ β k)) R (M k)) :
    let c := directPDOSymbols A B W₁ bminus σ β
    ∃ θ : ℕ → E → ℂ, (∀ j, ContDiff ℝ ∞ (θ j)) ∧
      (∀ j, HasCompactSupport (θ j)) ∧
      ∃ Preg : Fin 4 → ℕ → H →L[ℂ] H,
        (∀ k j u, Preg k j (graphTestToLp u) =ᵐ[volume] graphTestOutput
          (fun x η ↦ inner ℝ x η)
          (frequencyCutFullAmplitude (θ j) (fun x z η ↦ (χout x * χsource z) • c k x η)) u) ∧
        (∀ k u, Tendsto (fun j ↦ Preg k j u) atTop
          (𝓝 (maskedPhysicalPDO χout χsource (c k) u))) ∧
        (∀ k u, Tendsto (fun j ↦ (Preg k j).adjoint u) atTop
          (𝓝 ((maskedPhysicalPDO χout χsource (c k)).adjoint u))) :=
  ⟨complexPhysicalCutoff, complexPhysicalCutoff_contDiff,
    complexPhysicalCutoff_hasCompactSupport,
    directPDOSymbols_regularizations A B W₁ bminus σ β χout χsource R M hb
      complexPhysicalCutoff complexPhysicalCutoff_contDiff le_rfl
      complexPhysicalCutoff_norm_le complexPhysicalCutoff_tendsto⟩

end JanetCartan.RegularSector.Characteristic.PdoRealization
