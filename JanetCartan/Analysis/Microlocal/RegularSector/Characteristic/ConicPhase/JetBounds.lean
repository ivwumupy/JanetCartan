module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Normalized

/-!
# Normalized phase budgets from the same local characteristic phase

The fixed radial continuation has joint jets bounded linearly by the original
local phase jets, with zero derivative loss and constants independent of the
phase and of every positive radial scale. Reassociation into the actual
`SymbolBudgets` coordinates and the elapsed substitution are both contractions.
The only additive cost is the fixed time pairing in the elapsed phase.

The parent conic construction supplies the compact chart inclusions below.
For `F = twoTimePhase C`, local smoothness is the published output of
`exists_buffered_physical_pencil_kernel`. No normalized-phase budget is an input.
Source: `app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`, and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open EvolutionIntegral FourierIntegral FullAmplitudePrimitiveBudget.Local

variable {d : ℕ}

private theorem budgetChart_subset (ℓ : Euclidean d →L[ℝ] ℝ)
    {J : Set (SymbolBudgets.TwoTimePoint d)} {L U : Set (TwoTimePoint (Euclidean d))}
    (hLU : L ⊆ U) (hpos : ∀ p ∈ J, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) J L) :
    J ⊆ budgetCoordinates ⁻¹' domain ℓ U :=
  fun p hp ↦ ⟨hpos p hp, hLU (hmap hp)⟩

/-- Uniform normalized elapsed seminorms from original local phase jets.
The lower time remains `s=t-r`. The constant is fixed by the compact charts,
`ℓ`, and the derivative order, with no derivative shift or radial dependence
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem cNorm_normalizedElapsedPhase_curriedExtend_le (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (Point (d + 1))} {J : Set (SymbolBudgets.TwoTimePoint d)}
    {L U : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hL : IsCompact L)
    (hU : IsOpen U) (hLU : L ⊆ U)
    (hpos : ∀ p ∈ J, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) J L)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {R : ℝ} (hR : 0 < R) {Δ r : ℝ} (hr : r ∈ Icc 0 Δ)
    (helapsed : MapsTo (SymbolBudgets.elapsedPoint r) K J) (n : ℕ) :
    cNorm K n (fun p : Point (d + 1) ↦ WholeImageGeometry.normalizedPhase R
      (elapsedPhase (curriedExtend ℓ F) r) p.1.1 p.2) ≤
        SymbolBudgets.phaseTimeConstant K n Δ +
          jetBoundConstant ℓ (budgetCoordinates '' J) n * cNorm L n F := by
  have hs : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase
      (SymbolBudgets.normalizedTwoTimePhase R (curriedExtend ℓ F)))
      (budgetCoordinates ⁻¹' domain ℓ U) := by
    rw [normalizedTwoTimePhase_curriedExtend ℓ F hR]
    exact contDiffOn_jointPhase_curriedExtend ℓ hU hF
  exact (SymbolBudgets.cNorm_normalizedElapsedPhase_le hK hJ
    ((isOpen_domain ℓ hU).preimage budgetCoordinates.continuous)
    (budgetChart_subset ℓ hLU hpos hmap) _ hR.ne' hs hr helapsed n).trans
      (add_le_add le_rfl
        (cNorm_normalizedTwoTimePhase_curriedExtend_le ℓ hJ hL hU hLU hpos hmap hF hR n))

/-- The position/covector jets required by the whole-image phase reserve
come from the same local phase jets. This instantiates the elapsed-phase
transfer at every positive radius (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem norm_iteratedFDeriv_normalizedElapsedPhase_curriedExtend_le
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (Point (d + 1))} {J : Set (SymbolBudgets.TwoTimePoint d)}
    {L U : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hL : IsCompact L)
    (hU : IsOpen U) (hLU : L ⊆ U)
    (hpos : ∀ p ∈ J, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) J L)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {R : ℝ} (hR : 0 < R) {Δ r : ℝ} (hr : r ∈ Icc 0 Δ)
    (helapsed : MapsTo (SymbolBudgets.elapsedPoint r) K J)
    {n k : ℕ} (hk : k ≤ n) {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : SymbolBudgets.phasePairInclusion p ∈ K) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (WholeImageGeometry.normalizedPhase R
      (elapsedPhase (curriedExtend ℓ F) r))) p‖ ≤
        SymbolBudgets.phaseTimeConstant K n Δ +
          jetBoundConstant ℓ (budgetCoordinates '' J) n * cNorm L n F := by
  have hs : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase
      (SymbolBudgets.normalizedTwoTimePhase R (curriedExtend ℓ F)))
      (budgetCoordinates ⁻¹' domain ℓ U) := by
    rw [normalizedTwoTimePhase_curriedExtend ℓ F hR]
    exact contDiffOn_jointPhase_curriedExtend ℓ hU hF
  exact (SymbolBudgets.norm_iteratedFDeriv_normalizedElapsedPhase_le hK hJ
    ((isOpen_domain ℓ hU).preimage budgetCoordinates.continuous)
    (budgetChart_subset ℓ hLU hpos hmap) _ hR.ne' hs hr helapsed n k hk p hp).trans
      (add_le_add le_rfl
        (cNorm_normalizedTwoTimePhase_curriedExtend_le ℓ hJ hL hU hLU hpos hmap hF hR n))

/-- The literal dyadic whole-image reserve, derived from local jets of the
fixed conic extension. The shell inclusion is geometric; no shell jet bound
or normalized smoothness assumption is required. Consumer:
`exists_fullGraphFamily_of_wholeImage_phase` in the retarded kernel proof. -/
theorem wholeImagePhaseReserve_curriedExtend (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (Point (d + 1))} {J : Set (SymbolBudgets.TwoTimePoint d)}
    {L U : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hL : IsCompact L)
    (hU : IsOpen U) (hLU : L ⊆ U)
    (hpos : ∀ p ∈ J, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) J L)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {X D : Set (Euclidean (d + 1))} (a b : ℝ)
    (hchart : ∀ j : ℕ, ∀ p ∈ X ×ˢ WholeImageGeometry.normalizedSourceBand D ((2 : ℝ)^j) a b,
      SymbolBudgets.phasePairInclusion p ∈ K)
    {Δ r : ℝ} (hr : r ∈ Icc 0 Δ)
    (helapsed : MapsTo (SymbolBudgets.elapsedPoint r) K J) :
    ∀ j : ℕ, ∀ p ∈ X ×ˢ WholeImageGeometry.normalizedSourceBand D ((2 : ℝ)^j) a b,
      ∀ k ≤ WholeImageGeometry.wholeImagePhaseReserve (d + 1),
      ‖iteratedFDeriv ℝ k (Function.uncurry (WholeImageGeometry.normalizedPhase ((2 : ℝ)^j)
        (elapsedPhase (curriedExtend ℓ F) r))) p‖ ≤
          SymbolBudgets.phaseTimeConstant K (WholeImageGeometry.wholeImagePhaseReserve (d + 1)) Δ +
            jetBoundConstant ℓ (budgetCoordinates '' J)
              (WholeImageGeometry.wholeImagePhaseReserve (d + 1)) *
                cNorm L (WholeImageGeometry.wholeImagePhaseReserve (d + 1)) F := by
  intro j p hp k hk
  exact norm_iteratedFDeriv_normalizedElapsedPhase_curriedExtend_le
    ℓ hK hJ hL hU hLU hpos hmap hF (pow_pos (by norm_num) j) hr helapsed hk (hchart j p hp)

/-- The actual inverse-chart phase supplies its normalized elapsed budget
from its published local smoothness. Here `hC` is the output of
`exists_buffered_physical_pencil_kernel`, and the parent supplies the displayed
compact inclusions for that same chart. Source:
`app:ch_regular_base:lem:characteristic-kernel` and the fixed-time representation. -/
theorem cNorm_normalizedElapsedPhase_phase_le (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {K : Set (Point (d + 1))} {J : Set (SymbolBudgets.TwoTimePoint d)}
    {L : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hL : IsCompact L) (hLC : L ⊆ C.target)
    (hpos : ∀ p ∈ J, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) J L)
    {R : ℝ} (hR : 0 < R) {Δ r : ℝ} (hr : r ∈ Icc 0 Δ)
    (helapsed : MapsTo (SymbolBudgets.elapsedPoint r) K J) (n : ℕ) :
    cNorm K n (fun p : Point (d + 1) ↦ WholeImageGeometry.normalizedPhase R
      (elapsedPhase (curriedExtend ℓ (twoTimePhase C)) r) p.1.1 p.2) ≤
        SymbolBudgets.phaseTimeConstant K n Δ +
          jetBoundConstant ℓ (budgetCoordinates '' J) n * cNorm L n (twoTimePhase C) :=
  cNorm_normalizedElapsedPhase_curriedExtend_le
    ℓ hK hJ hL C.open_target hLC hpos hmap hC hR hr helapsed n

end JanetCartan.RegularSector.Characteristic.ConicPhase
