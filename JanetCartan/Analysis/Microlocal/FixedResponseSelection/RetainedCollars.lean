module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates

/-!
# Algebraic collars on the retained response chart

Apply the compact-root and normalized-collar producers to the chart already
chosen with its stationary source radius. No second local chart is selected.
Consumer: finite selection with the original algebraic collar and protection
certificates (`app:ch_regular_base:eq:complement-inverse`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicChart
open ActualCarriers RootFamily ResidualCoordinates AlgebraicSymbols EvolutionIntegral
open AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- Enrich an already constructed chart with the full original algebraic
collar and complement budgets. The root buffer and source containment are
the proved outputs of `exists_localChart_with_stationary_source_radius`.
This preserves its masks, stationary radius and protection certificates
(`app:ch_regular_base:eq:complement-inverse`, `energy-complete-residual`). -/
theorem exists_algebraic_collar_on_retained_localChart
    {Ω : Set E} (hΩ : IsOpen Ω) {x : E} {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    {A₀ : Coeff} {ξ : E} {M : ℝ} (c : LocalChart Ω x RQ A₀ ξ M)
    (hc : RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
      c.minorGap c.transportGap)
    (hsource : MapsTo (rootPhysicalPosition (coordinateSplit c.index))
      (tsupport c.sourceMask) (closedBall x RQ)) :
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
      a < c.coefficientRadius ∧ b < min c.coefficientRadius c.rootRadius ∧
      let KA := closedBall A₀ a
      let Kη := closedBall (coordinateSplit c.index ξ).2 b
      let x' := (physicalCoordinates c.index).symm x
      IsCompact KA ∧ IsCompact Kη ∧
      KA ⊆ ball A₀ c.coefficientRadius ∧
      Kη ⊆ ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) ∧
      (∀ p ∈ ball A₀ c.coefficientRadius ×ˢ
        ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius),
        ContDiffAt ℝ ∞ c.root p) ∧
      (∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ c.root p) ∧
    ∃ bound > (0 : ℝ),
      (∀ p ∈ KA ×ˢ Kη,
        ‖coefficientRootPencil (coordinateSplit c.index) c.root p‖ ≤ bound ∧
        ‖pencil p.1 ((coordinateSplit c.index).symm (1, 0))‖ ≤ bound ∧
        (coefficientRootPencil (coordinateSplit c.index) c.root p).det = 0 ∧
        c.minorGap ≤ |(coefficientRootPencil (coordinateSplit c.index) c.root p).adjugate c.row c.col| ∧
        c.transportGap ≤ |minorTransportCoefficient
          (coefficientRootPencil (coordinateSplit c.index) c.root p)
          (pencil p.1 ((coordinateSplit c.index).symm (1, 0))) c.row c.col|) ∧
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass c.row c.col bound c.minorGap c.transportGap,
        ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det|) ∧
      (minorCoefficientClass c.row c.col bound c.minorGap c.transportGap ×ˢ
        closedBall (0 : ℝ) ε ⊆ minorComplementDomain c.row c.col) ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ c.coefficientRadius ∧
    ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ c.angularNeighborhood ∧
      (∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V) ∧
    ∃ Λ > (0 : ℝ),
      (∀ ζ ∈ V,
        let ζ' := (physicalCoordinates c.index).symm ζ
        0 < c.radialSection (spatialPart ζ') ∧
        spatialPart (normalizeCovector c.radialSection ζ') ∈ Kη ∧
        ‖normalizeCovector c.radialSection ζ'‖ ≤ Λ ∧
        ∀ A ∈ closedBall A₀ a',
          |normalizeCovector c.radialSection ζ' 0 -
            c.root (A, spatialPart (normalizeCovector c.radialSection ζ'))| ≤ ε) ∧
      ∀ Q : E → Coeff, MapsTo Q Ω (closedBall A₀ a') →
        (∀ β : E → ℂ, tsupport β ⊆ V →
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹' Ω) ε (β ∘ physicalCoordinates c.index) ∧
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹'
              (rootPhysicalPosition (coordinateSplit c.index) '' tsupport c.sourceMask))
            ε (β ∘ physicalCoordinates c.index) ∧
          (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
            (normalizeCovector c.radialSection '' tsupport (β ∘ physicalCoordinates c.index)) ⊆
            complementDomain c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col (fieldDomain (coordinateSplit c.index) Ω c.radialSection
                (coordinateSplit c.index ξ).2 c.coefficientRadius)) ∧
        (ContDiffOn ℝ ∞ Q Ω → ∀ ζ ∈ V,
          let ζ' := normalizeCovector c.radialSection ((physicalCoordinates c.index).symm ζ)
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') y) ∧
          ∀ m, cNorm (closedBall x' RQ) m
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q)) := by
  obtain ⟨a, ha, b, hb, hac, hbc, hKA, hKη, hKAopen, hKηopen,
    hHopen, bound, hbound, hprimitive⟩ := exists_compact_root_buffers c hc
  have hH p (hp : p ∈ closedBall A₀ a ×ˢ closedBall (coordinateSplit c.index ξ).2 b) :
      ContDiffAt ℝ ∞ c.root p := hHopen p ⟨hKAopen hp.1, hKηopen hp.2⟩
  let x' := (physicalCoordinates c.index).symm x
  have hphysical : MapsTo (physicalCoordinates c.index) (closedBall x' RQ) (closedBall x RQ) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    have hx : physicalCoordinates c.index x' = x :=
      (physicalCoordinates c.index).apply_symm_apply x
    have he : ‖physicalCoordinates c.index y - x‖ = ‖y - x'‖ := by
      calc
        _ = ‖physicalCoordinates c.index (y - x')‖ := by rw [map_sub, hx]
        _ = _ := norm_physicalCoordinates _ _
    rwa [he]
  obtain ⟨ε, hε, δ, hδ, C, hC, hgap, hdomain, hinverse⟩ :=
    exists_bminus_fieldRoot_cNorm_bounds c.index c.row c.col x' hRQ x RQ hphysical
      hKA hKη c.root hH bound c.minorGap_pos c.transportGap_pos hprimitive
  obtain ⟨a', ha', ha'a, ha'c, V, hV, hξV, hVc, hVcone, Λ, hΛ, hcollar⟩ :=
    exists_normalized_spectral_collar c hc ha hb hε
  refine ⟨a, ha, b, hb, hac, hbc,
    hKA, hKη, hKAopen, hKηopen, hHopen, hH, bound, hbound, hprimitive,
    ε, hε, δ, hδ, C, hC, hgap, hdomain, a', ha', ha'a, ha'c,
    V, hV, hξV, hVc, hVcone, Λ, hΛ, hcollar, ?_⟩
  intro Q hQrange
  refine ⟨?_, ?_⟩
  · intro β hβ
    have hs := normalizedSpectralSupport_of_collar c
      (fun ζ hζ ↦ (hcollar ζ hζ).2.2.2) Q hQrange β hβ
    refine ⟨hs, ?_, ?_⟩
    · intro y hy ζ hζ
      obtain ⟨w, hw, he⟩ := hy
      exact hs y (hKΩ (he ▸ hsource hw)) ζ hζ
    · have hv ζ (hζ : ζ ∈ tsupport (β ∘ physicalCoordinates c.index)) :
          physicalCoordinates c.index ζ ∈ V :=
        hβ (tsupport_comp_subset_preimage β (physicalCoordinates c.index).continuous hζ)
      have hη ζ (hζ : ζ ∈ tsupport (β ∘ physicalCoordinates c.index)) :
          spatialPart (normalizeCovector c.radialSection ζ) ∈
            closedBall (coordinateSplit c.index ξ).2 b := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using (hcollar _ (hv ζ hζ)).2.1
      have hpos ζ (hζ : ζ ∈ tsupport (β ∘ physicalCoordinates c.index)) :
          0 < c.radialSection (spatialPart ζ) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using (hcollar _ (hv ζ hζ)).1
      exact normalized_support_subset_complementDomain c.radialSection c.index c.row c.col
        c.root hdomain hprimitive Q
        (fun y hy ↦ closedBall_subset_closedBall ha'a (hQrange hy))
        (β ∘ physicalCoordinates c.index) hη
        (fun y hy ζ hζ ↦ normalized_rootState_mem_fieldDomain c
          (hbc.trans_le (min_le_left _ _)) hy (hpos ζ hζ) (hη ζ hζ)) hs
  intro hQ ζ hζ ζ'
  apply hinverse Ω hΩ hKΩ Q hQ
    (fun y hy ↦ closedBall_subset_closedBall ha'a (hQrange (hKΩ hy))) ζ'
    (hcollar ζ hζ).2.1
  intro y hy
  exact (hcollar ζ hζ).2.2.2 _ (hQrange (hKΩ (hphysical hy)))

end JanetCartan.RegularSector.Characteristic.AlgebraicChart
