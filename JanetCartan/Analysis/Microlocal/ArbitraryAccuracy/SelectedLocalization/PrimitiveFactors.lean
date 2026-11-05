module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Regularizations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Profiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.CompleteFactor
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.UniformEvolution
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open FourierIntegral FourierIntegral.LowBounds
variable {d q : ℕ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-! The selected-chart specialization below is the operator identity used by
`CompleteFactor`: it keeps the endpoint output mask, the original chart input
mask, and the source-before-Fourier ordering fixed. -/

/-- The SAME retained signed retarded operator is the common endpoint-masked
operator in both literal orientations.  This is the selected-chart form of
`retained_common_localization_eq_endpoint`, for the fixed response and its
literal adjoint (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_common_masked_retarded_operator
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (B : E → MetricTensor (d + 1))
    (Δ a : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q) (β : E → ℂ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (canonical : H →L[ℂ] H)
    (hcanonical : ∀ u : graphTestSpace (d + 1) q,
      canonical (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (retardedPhysicalIntegral Ψ W (endpointOutputMask f p output)
          (chartInputMask f p) β (chartPhysicalMasks_properties f p).2.1 a u y))
    (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (o : ℕ) (A : ℝ) (As : ℕ → ℝ) (Op : H →L[ℂ] H)
    (hOp : RetainedSignedRetardedBounds (closedBall x RQ) Q B Δ a Ψ W
      χout χsource β hs o A As Op)
    (hlocalout : ∀ y, (output y : ℂ) * χout
      ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ))
    (hlocalin : ∀ y, χsource ((physicalCoordinates (f.chart p).index).symm y) *
      (f.inputMask y : ℂ) = (f.inputMask y : ℂ))
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) :
    let e := physicalCoordinates (f.chart p).index
    let Mo := sourceCutMultiplier (r := q) (output ∘ e)
      (ho.comp e.continuous) (fun y ↦ hob (e y))
    let Mi := sourceCutMultiplier (r := q) (f.inputMask ∘ e)
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ hib (e y))
    Mo.comp (Op.comp Mi) = canonical ∧
      Mi.comp (Op.adjoint.comp Mo) = canonical.adjoint := by
  simpa using retained_common_localization_eq_endpoint f p Q B Δ a Ψ W β output ho hob
    canonical hcanonical χout χsource hs o A As Op hOp hlocalout hlocalin hib

end JanetCartan.ArbitraryAccuracy.SelectedLocalization

end

/-!
# Common-order adapter for the selected elapsed grades

`exists_selected_elapsed_amplitude_inputs` proves the literal residual at its
natural order `-1`.  `CompleteFactor` consumes the common order-zero profile
for the summed source, endpoint, and differentiated algebraic branches.  The
adapter below only enlarges that order, leaving the selected carrier, masks,
profile constants, and zero offsets unchanged.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open JanetCartan.FourierIntegral JanetCartan.FiniteChain.Graph.KernelEstimates
open RegularSector RegularSector.Characteristic
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic.RootFamily
open ProtectedMasks ProtectedMasks.ConicInterior
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo

/-- The selected elapsed residual's order `-1` grades imply the common
order-zero grades required by `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
This is the fixed-operator, fixed-loss domination used before the varying
target and finite history (`app:ch_regular:eq:chain-tail`). -/
theorem selected_hasAmplitudeGrades_order_zero
    {d q : ℕ}
    {D : AmplitudeProfiles} {ρ L : ℝ}
    {b : FullAmplitude (d + 1) q}
    {mi mo : LocalizerSymbol (d + 1)}
    {χA χo : Euclidean (d + 1) → ℝ} {u y : Euclidean (d + 1)}
    {Kg : Set (JointVariables (Euclidean (d + 1)))}
    (hρ : 1 ≤ ρ) (hL : 0 ≤ L)
    (h : HasAmplitudeGrades D ρ (ρ ^ (-1 : ℝ)) L b mi mo χA χo u y Kg) :
    HasAmplitudeGrades D ρ (ρ ^ (0 : ℝ)) L b mi mo χA χo u y Kg := by
  refine { h with symbol_bound := ?_ }
  exact fun k v hv ↦ (h.symbol_bound k v hv).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hρ (by norm_num : (-1 : ℝ) ≤ 0))
        (D.symbol_nonneg k))
      (pow_nonneg hL _))

/-! The selected even-mask conclusion is projected without choosing a second
mask family.  This is the exact parity input consumed by `CompleteFactor`.
-/

/-- Extract the physical-covector parity from the SAME selected even nested
mask witnesses (`app:ch_regular:lem:finite-chain`).  All support, propagation,
phase-gap, and canonical-coordinate fields remain attached to that witness in
the producer proposition; this projection only exposes the fields needed by
the real/adjoint CompleteFactor branch. -/
theorem selected_even_nested_mask_parity
    {d : ℕ} {M : ℝ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)}
    {RQ : ℝ} {A₀ : Fin (d + 1) → MetricTensor (d + 1)}
    {K : Set (Euclidean (d + 1))}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (χ₂ : Euclidean (d + 1) → ℝ) (Ksource : Set (Euclidean (d + 1)))
    (V : Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (Γ : Set (Euclidean (d + 1)))
    (output : Euclidean (d + 1) → ℝ) (N : ℕ)
    (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (j : f.centers) → Fin (n j) → ℝ)
    (hcRad : ∀ j k, 0 < cRad j k)
    (Urad : (j : f.centers) → Fin (n j) → Set (RootState (Euclidean d)))
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Cphase : f.centers → OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
      (TwoTimePoint (Euclidean d)))
    (hEven : SelectedEvenProofMasks.SelectedSectorEvenNestedMaskConclusion f eT eI
      χ₂ Ksource V Γ output N aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase) :
    ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
      ∀ k y ξ, m k (y, -ξ) = m k (y, ξ) := by
  dsimp only [SelectedEvenProofMasks.SelectedSectorEvenNestedMaskConclusion] at hEven
  rcases hEven with ⟨Gext, m, heven, hrest⟩
  exact ⟨m, heven⟩

/-- Select the first two members of the SAME even nested family for the
CompleteFactor real/adjoint branch.  No independent localizer choices are
introduced; `hieven` and `hoeven` are projections of one producer witness. -/
theorem selected_even_nested_masks_completeFactor_parity
    {d : ℕ} {M : ℝ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)}
    {RQ : ℝ} {A₀ : Fin (d + 1) → MetricTensor (d + 1)}
    {K : Set (Euclidean (d + 1))}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (χ₂ : Euclidean (d + 1) → ℝ) (Ksource : Set (Euclidean (d + 1)))
    (V : Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (Γ : Set (Euclidean (d + 1))) (output : Euclidean (d + 1) → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (j : f.centers) → Fin (n j) → ℝ)
    (hcRad : ∀ j k, 0 < cRad j k)
    (Urad : (j : f.centers) → Fin (n j) → Set (RootState (Euclidean d)))
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Cphase : f.centers → OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
      (TwoTimePoint (Euclidean d)))
    (hEven : SelectedEvenProofMasks.SelectedSectorEvenNestedMaskConclusion f eT eI
      χ₂ Ksource V Γ output N aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase) :
    ∃ (mi mo : LocalizerSymbol (d + 1)),
      (∀ y ξ, mi (y, -ξ) = mi (y, ξ)) ∧
      (∀ y ξ, mo (y, -ξ) = mo (y, ξ)) := by
  obtain ⟨m, heven⟩ := selected_even_nested_mask_parity f eT eI χ₂ Ksource V Γ output N
    aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase hEven
  let i₀ : Fin (N + 1) := ⟨0, by omega⟩
  let i₁ : Fin (N + 1) := ⟨1, by omega⟩
  refine ⟨m i₀, m i₁, ?_, ?_⟩
  · intro y ξ
    exact heven i₀ y ξ
  · intro y ξ
    exact heven i₁ y ξ

/-! The next projection retains the actual buffered geometry of the same
even family.  The complete residual needs a compact plateau set for the
output localizer and a diagonal support carrier; both are obtained from the
published shoulders and the first nesting step, rather than selected anew. -/

/-- Project the SAME selected even nested family to the buffered localizer
data consumed by `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).  The
output plateau is the thickened support of the first mask, the support carrier
is the original protected region, and the physical annular support and both
parity identities are retained. -/
theorem selected_even_nested_masks_completeFactor_localizer_data
    {d : ℕ} {M : ℝ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)}
    {RQ : ℝ} {A₀ : Fin (d + 1) → MetricTensor (d + 1)}
    {K : Set (Euclidean (d + 1))}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (χ₂ : Euclidean (d + 1) → ℝ) (Ksource : Set (Euclidean (d + 1)))
    (V : Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (Γ : Set (Euclidean (d + 1)))
    (output : Euclidean (d + 1) → ℝ) (N : ℕ)
    (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (j : f.centers) → Fin (n j) → ℝ)
    (hcRad : ∀ j k, 0 < cRad j k)
    (Urad : (j : f.centers) → Fin (n j) → Set (RootState (Euclidean d)))
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Cphase : f.centers → OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
      (TwoTimePoint (Euclidean d)))
    (hN : 1 ≤ N) (hθ : 0 ≤ θ)
    (hEven : SelectedEvenProofMasks.SelectedSectorEvenNestedMaskConclusion f eT eI
      χ₂ Ksource V Γ output N aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase) :
    ∃ (mi mo : LocalizerSymbol (d + 1))
      (Ko Oo : Set (Euclidean (d + 1) × Euclidean (d + 1))),
      IsBufferedLocalizer mo Ko Oo ∧ IsCompact Ko ∧
      tsupport mi ⊆ Ko ∧ tsupport mi ⊆ interior {p | mo p = 1} ∧
      (∀ y ξ, mi (y, -ξ) = mi (y, ξ)) ∧
      (∀ y ξ, mo (y, -ξ) = mo (y, ξ)) ∧
      (∀ p, mi p ∈ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a b) := by
  dsimp only [SelectedEvenProofMasks.SelectedSectorEvenNestedMaskConclusion] at hEven
  rcases hEven with ⟨Gext, m, heven, hGext, hm, hfirst, hshoulder, hreachable,
    hbound, hjet, hnest, hcanon, hcanonsupp, hcanonjet, hunit, hrecut, hgap⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  let i₀ : Fin (N + 1) := ⟨0, by omega⟩
  let i₁ : Fin (N + 1) := ⟨1, by omega⟩
  let k₀ : Fin N := ⟨0, hNpos⟩
  let Ko : Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
    cthickening θ (tsupport (m i₀))
  let Oo : Set (Euclidean (d + 1) × Euclidean (d + 1)) := physicalProtectedRegion Γ
  have hsupportKo : tsupport (m i₀) ⊆ Ko := self_subset_cthickening _
  have hdiag : tsupport (m i₀) ⊆ interior {p | m i₁ p = 1} := by
    intro p hp
    have hnest0 := hnest k₀ p (self_subset_cthickening _ hp) p (Or.inl rfl)
    exact hnest0 (mem_closedBall_self hθ)
  have hbuf := hm i₁
  have hobuf : IsBufferedLocalizer (m i₁) Ko Oo := by
    refine ⟨hbuf.smooth, hbuf.range, hbuf.compactSupport, hbuf.support_subset, ?_⟩
    intro p hp
    have hnest0 := hnest k₀ p hp p (Or.inl rfl)
    exact hnest0 (mem_closedBall_self hθ)
  have hKo : IsCompact Ko := (hm i₀).compactSupport.cthickening
  refine ⟨m i₀, m i₁, Ko, Oo, hobuf, hKo, hsupportKo, hdiag,
    heven i₀, heven i₁, (hm i₀).range, ?_⟩
  intro p hp
  exact (hbound i₀ (self_subset_cthickening _ hp)).1.2

/-! The CompleteFactor interface asks for the input annulus and range on
individual frequency slices.  The selected even producer exposes those facts
on the full physical symbol; the following projection keeps the same symbol
and merely transports the support through the fixed slice embedding. -/

/-- Convert the SAME selected localizer's global support and range fields to
the sliced `hiAnn` and `hiBound` premises of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
No new localizer or frequency carrier is introduced (`app:ch_regular:lem:finite-chain`). -/
theorem selected_completeFactor_sliced_localizer_inputs
    {d : ℕ} {a b : ℝ} {mi : LocalizerSymbol (d + 1)}
    (hann : ∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a b)
    (hrange : ∀ p, mi p ∈ Icc (0 : ℝ) 1) :
    (∀ y, tsupport (fun η ↦ mi (y, η)) ⊆ frequencyAnnulus a b) ∧
      (∀ y η, ‖mi (y, η)‖ ≤ 1) := by
  have hslice (y : Euclidean (d + 1)) :
      tsupport (fun η ↦ mi (y, η)) ⊆
        {η | (y, η) ∈ tsupport mi} := by
    change closure (Function.support (fun η ↦ mi (y, η))) ⊆ _
    apply closure_minimal
    · intro η hη
      exact subset_tsupport mi hη
    · exact (isClosed_tsupport mi).preimage (continuous_const.prodMk continuous_id)
  constructor
  · intro y η hη
    exact hann (y, η) (hslice y hη)
  · intro y η
    rw [Real.norm_of_nonneg (hrange (y, η)).1]
    exact (hrange (y, η)).2

end JanetCartan.ArbitraryAccuracy.SelectedLocalization

end

/-!
# Primitive inputs on the retained selected chart witnesses

For `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`, the
common-mask regularizations identify the retained retarded operators with
their original conic elapsed integrals, in both literal orientations. The
profile deductions give finite-family normalized phase-gradient and conic
amplitude bounds from the original coefficient profile and the retained
construction's estimates.

The complete chart leakage estimate still requires joint elapsed-amplitude
grades, the three PDO grades and realizations, and application of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
These primitive results alone do not establish that leakage estimate or the
arbitrary-accuracy response theorem.
-/
