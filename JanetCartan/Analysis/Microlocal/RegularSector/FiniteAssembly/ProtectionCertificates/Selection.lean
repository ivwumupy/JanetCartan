module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily

/-!
# Retained protection certificates for the finite direct construction

The same local root, masks and evolution are retained through this deduction.
Consumer: `exists_finite_direct_operator_bounds_with_protection_certificates`,
then `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat

/-- Construct a finite family from the enriched local algebraic charts.
Its common coefficient radius lies in every selected spectral collar's
coefficient ball. The complete physical, angular and low-frequency partition
belongs to this SAME family; every inverse interval and tame bound is retained
from its actual local producer. Source: `app:ch_regular_base:thm:sector`,
`app:ch_regular_base:eq:complement-inverse` and `energy-complete-residual`. -/
theorem exists_actualMaskFamily_with_algebraic_collar_with_protection_certificates
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ f : ActualMaskFamily Ω x RQ A₀ K M, ∀ p : f.centers,
      let c := f.chart p
      let ξ := p.val.val
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 ∧
      RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
        (closedBall x RQ) ∧
    ∃ evolutionTime speedGap rootSize rootCost,
      LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost ∧
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
      f.coefficientRadius ≤ a' ∧
    ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ c.angularNeighborhood ∧
      tsupport (f.angularMask p) ⊆ V ∧
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
  classical
  let Z := {ξ : E | ξ ∈ K ∧ determinant A₀ ξ = 0}
  have hc (p : Z) := exists_localChart_algebraic_collar_with_protection_certificates hΩ x hRQ hKΩ A₀ p.val
    (fun hz ↦ hKzero (hz ▸ p.property.1)) p.property.2
    (hregular p.val p.property.1 p.property.2) hM
  choose charts hcb hcm hroot hsource evolutionTime speedGap rootSize rootCost hprotection a ha b hb hac hbc hKA hKη hKAopen hKηopen
    hHopen hH bound hbound hprimitive ε hε δ hδ C hC hgap hdomain
    a' ha' ha'a ha'c V hV hcenter hVc hVcone Λ hΛ hcollar hbudgets using hc
  obtain ⟨s, χ, ε₀, hε₀, δ₀, hδ₀, hχ, hrange, hcompact, hsupp, hsum, hstable⟩ :=
    exists_finite_pencil_masks A₀ hK V hV (by
      intro ξ hξ hp
      exact ⟨⟨ξ, hξ, hp⟩, hcenter ⟨ξ, hξ, hp⟩⟩)
  let chart : ∀ p : s, LocalChart Ω x RQ A₀ p.val.val M := fun p ↦ charts p.val
  obtain ⟨ε₁, hε₁, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : s ↦ (0 : ℝ)) (y := fun p ↦ a' p.val) (fun p ↦ ha' p.val)
  let U : Set E := ball x RQ ∩ ⋂ p : s, (chart p).physicalNeighborhood
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_iInter_of_finite fun p ↦ (chart p).isOpen_physicalNeighborhood)
  have hxU : x ∈ U := ⟨mem_ball_self hRQ,
    mem_iInter.mpr fun p ↦ (chart p).center_mem_physicalNeighborhood⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hball : closedBall x (4 * (r / 8)) ⊆ U :=
    (closedBall_subset_ball (by linarith : 4 * (r / 8) < r)).trans hrU
  have hsupp' (p : s) : tsupport (χ p) ⊆ (chart p).angularNeighborhood :=
    (hsupp p).trans (hVc p.val)
  obtain ⟨angular, L, hL, hang, hangp, _⟩ := exists_common_physical_radial_masks
    (fun p : s ↦ p.val.val) chart χ hsupp'
  obtain ⟨input, output, hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, _⟩ :=
    exists_common_physical_masks x (show 0 < r / 8 by positivity)
  have hsmall' (p : s) : min ε₀ ε₁ ≤ a' p.val :=
    (min_le_right _ _).trans (by simpa using (hsmall p).le)
  refine ⟨⟨s, chart, χ, angular, min ε₀ ε₁, δ₀, r / 8, L, input, output,
    lt_min hε₀ hε₁, hδ₀, by positivity, hL,
    (fun p ↦ (hsmall' p).trans (ha'c p.val)),
    (fun y hy ↦ hKΩ (ball_subset_closedBall (hball hy).1)),
    (fun y hy ↦ ball_subset_closedBall (hball hy).1),
    (fun p y hy ↦ mem_iInter.mp (hball hy).2 p),
    hχ, hrange, hcompact, hsupp', hsum, hang, hangp,
    hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, ?_⟩, ?_⟩
  · intro Q X hQ
    exact hstable Q X fun y hy ↦ (hQ y hy).trans (min_le_left _ _)
  · intro p
    exact ⟨hcb p.val, hcm p.val, hroot p.val, hsource p.val,
      evolutionTime p.val, speedGap p.val, rootSize p.val, rootCost p.val, hprotection p.val,
      a p.val, ha p.val, b p.val, hb p.val, hac p.val, hbc p.val,
      hKA p.val, hKη p.val, hKAopen p.val, hKηopen p.val,
      hHopen p.val, hH p.val, bound p.val, hbound p.val, hprimitive p.val,
      ε p.val, hε p.val, δ p.val, hδ p.val, C p.val, hC p.val,
      hgap p.val, hdomain p.val, a' p.val, ha' p.val, ha'a p.val, ha'c p.val,
      hsmall' p, V p.val, hV p.val, hcenter p.val, hVc p.val, hsupp p,
      hVcone p.val, Λ p.val, hΛ p.val, hcollar p.val, hbudgets p.val⟩

end JanetCartan.RegularSector.FiniteAlgebraic
