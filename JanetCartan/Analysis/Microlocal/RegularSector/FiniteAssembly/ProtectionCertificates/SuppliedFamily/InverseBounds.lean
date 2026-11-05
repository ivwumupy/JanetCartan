module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.Selection

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SpectralSupport
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.NormalizedRoot
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.ConicInverse
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalConstruction

/-!
# Conic inverse on a supplied protected finite family

The original algebraic-collar selector supplies the hypotheses for a fixed
`ActualMaskFamily`. The same local root, masks and evolution are retained.
Consumer: `exists_finite_physical_algebraic_pdos_of_selected_collar`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat

/-- Retain a supplied finite family through the actual conic inverse construction.
`hf` is exactly the original selector's collar conclusion, also retained as the
first projection of `exists_actualMaskFamily_with_stationary_source_radii`.
No new family, reference, masks or radial threshold is selected. Constants
precede the varying coefficients and radial enlargement. Consumer: the
supplied-family continuation of
`exists_finite_protected_direct_operator_bounds_and_equations`.
Sources: `app:ch_regular_base:thm:sector`, `complement-symbol`,
`sector-theorem-residual`, `measured-adjoint`, `energy-complete-residual`. -/
theorem exists_finite_physical_evolution_and_algebraic_inverse_of_selected_collar
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (_hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} {M : ℝ} (hM : 0 ≤ M)
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hf : ∀ p : f.centers,
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
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q))) :
    ∃ (evolutionTime speedGap rootSize : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ),
      (∀ p, LocalProtectionCertificate (f.chart p) (evolutionTime p) (speedGap p)
        (rootSize p) (rootCost p)) ∧
      (∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) ∧
      (∀ p : f.centers, SelectedChartPhysicalEvolution (f.chart p) (f.angularMask p)
        ((physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask)
        ((physicalCoordinates (f.chart p).index) ⁻¹' Ω)) ∧
      ∀ p : f.centers,
        let c := f.chart p
        let x' := (physicalCoordinates c.index).symm x
        RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
          c.minorGap c.transportGap ∧
        MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
          (closedBall x RQ) ∧
        ∃ ε > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
        ∀ L ≥ f.radialThreshold, ∀ Q : E → Coeff,
          ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
          let h := fieldRoot (coordinateSplit c.index) Q c.root
          let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ)
          let U := physicalCoordinates c.index ⁻¹' Ω
          NormalizedSpectralSupport c.radialSection h U ε β ∧
          ContDiffOn ℝ ∞ h (normalizedRootDomain c) ∧
          (∀ w ∈ normalizedRootDomain c, (rootPencil (coordinateSplit c.index) Q h w).det = 0) ∧
          (U ×ˢ (normalizeCovector c.radialSection '' tsupport β) ⊆
            complementDomain c.index Q h c.row c.col
              (normalizedRootDomain c)) ∧
          (∀ ρ : Euclidean d → ℝ, ContDiff ℝ ∞ ρ →
            tsupport ρ ⊆ {η | 0 < c.radialSection η} →
            ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol
              (conicBminus c.radialSection c.index Q h c.row c.col)
              (conicSourceSymbol c.radialSection ρ c.sourceMask) β))) ∧
          ∀ ζ ∈ tsupport β,
            (∀ y ∈ U, (∑ a, (ζ a : ℂ) • (coefficient c.index Q y a).map Complex.ofReal) *
              conicBminus c.radialSection c.index Q h c.row c.col y ζ =
                1 - projector c.index Q h c.row c.col y
                  ((c.radialSection (spatialPart ζ))⁻¹ • spatialPart ζ)) ∧
            (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
              (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) y) ∧
            ∀ m, (1 + ‖ζ‖) * cNorm (closedBall x' RQ) m
              (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) ≤
                C m * (1 + cNorm (closedBall x RQ) m Q) := by
  classical
  have hcert (p : f.centers) := (hf p).2.2.2.2
  choose evolutionTime speedGap rootSize rootCost hprotection hcollar using hcert
  have hradii (p : f.centers) := And.intro (hf p).1 (hf p).2.1
  refine ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hradii, ?_, ?_⟩
  · intro p
    exact exists_selected_chart_physical_operators (f.chart p) (hradii p).1 (hradii p).2 hM
      (f.angularMask p) (f.angularMask_smooth p) (f.angularMask_support p)
      (f.inputMask_compact.image (physicalCoordinates (f.chart p).index).symm.continuous)
      (hΩ.preimage (physicalCoordinates (f.chart p).index).continuous)
      (selected_input_carrier_subset_domain f p)
  intro p
  let c := f.chart p
  let x' := (physicalCoordinates c.index).symm x
  obtain ⟨hroot, hsource⟩ := And.intro (hf p).2.2.1 (hf p).2.2.2.1
  obtain ⟨a, ha, b, hb, hac, hbc, hKA, hKη, hKAopen, hKηopen,
    hHopen, hH, bound, hbound, hprimitive, ε, hε, δ, hδ, D, hD, hgap, hdomain,
    a', ha', ha'a, ha'c, hfa', V, hV, hcenter, hVc, hsupp, hVcone,
    Λ, hΛ, hcollar, hbudgets⟩ := hcollar p
  let W := 1 + (1 / Λ)⁻¹ + max 0 Λ
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨hroot, hsource, ε, hε, fun m ↦ W * D m, fun m ↦ mul_pos hW (hD m), ?_⟩
  intro L hL Q hQ hQrange h β U
  have hLone : 1 ≤ L := f.radialThreshold_ge_one.trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hQsmall : MapsTo Q Ω (closedBall A₀ a') :=
    fun y hy ↦ closedBall_subset_closedBall hfa' (hQrange hy)
  let βphys := fun ζ ↦ (dilatedConicMask (f.angularMask p) L ζ : ℂ)
  have hsphys : tsupport βphys ⊆ V :=
    (tsupport_comp_subset Complex.ofReal_zero (dilatedConicMask (f.angularMask p) L)).trans
      (dilatedConicMask_tsupport_subset_collar (f.angularMask p) hsupp hVcone hLpos)
  have hdata := hbudgets Q hQsmall
  have hsupport := hdata.1 βphys hsphys
  have hrootData := fieldRoot_smooth_and_characteristic_on_normalizedRootDomain c hΩ hroot Q hQ
    (f.mapsTo_local_coefficient_ball p hQrange)
  have hdom : U ×ˢ (normalizeCovector c.radialSection '' tsupport β) ⊆
      complementDomain c.index Q h c.row c.col (normalizedRootDomain c) := by
    rintro ⟨y, η⟩ ⟨hy, ζ, hζ, rfl⟩
    have hζV := physical_multiplier_mem_collar c.index (f.angularMask p) hsupp hVcone hLpos hζ
    have hη : spatialPart (normalizeCovector c.radialSection ζ) ∈
        closedBall (coordinateSplit c.index p.val.val).2 b := by
      simpa only [c, ContinuousLinearEquiv.symm_apply_apply] using (hcollar _ hζV.1).2.1
    refine ⟨⟨hy, (closedBall_subset_ball hbc) hη⟩,
      (hsupport.2.2 ⟨hy, ζ, hζ, rfl⟩).2⟩
  refine ⟨hsupport.1, hrootData.1, hrootData.2, hdom, ?_, ?_⟩
  · intro ρ hρ hsρ
    apply contDiff_conicAlgebraicSymbol c.radialSection c.index hQ
      (isOpen_normalizedRootDomain c hΩ) hrootData.1 (fun _ hw ↦ hw.1)
      c.row c.col hdom ρ hρ hsρ c.sourceMask c.sourceMask_smooth
    · intro w hw
      change physicalCoordinates c.index
        (KernelIdentification.timeSpacePoint w.1 w.2.1) ∈ Ω
      rw [physicalCoordinates_timeSpacePoint]
      exact hKΩ (hsource hw)
    · exact Complex.ofRealCLM.contDiff.comp
        ((contDiff_dilatedConicMask (f.angularMask_smooth p) L).comp
          (physicalCoordinates c.index).contDiff)
    · intro ζ hζ
      exact mem_image_of_mem _ hζ
  intro ζ hζ
  have hζV := physical_multiplier_mem_collar c.index (f.angularMask p) hsupp hVcone hLpos hζ
  have hsection : 0 < c.radialSection (spatialPart ζ) := by
    simpa only [c, ContinuousLinearEquiv.symm_apply_apply] using (hcollar _ hζV.1).1
  have hnorm : ‖normalizeCovector c.radialSection ζ‖ ≤ Λ := by
    simpa only [c, ContinuousLinearEquiv.symm_apply_apply] using (hcollar _ hζV.1).2.2.1
  have hradial := section_lower_bound_of_normalized_norm c.radialSection hΛ hsection
    hnorm (hLone.trans hζV.2)
  have hinverse := hdata.2 hQ (physicalCoordinates c.index ζ) hζV.1
  simp only [c, ContinuousLinearEquiv.symm_apply_apply] at hinverse
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact conicBminus_identity c.radialSection c.index Q h c.row c.col hrootData.2
      (hdom ⟨hy, ζ, hζ, rfl⟩)
  · intro y hy
    exact (contDiffAt_const (c := (c.radialSection (spatialPart ζ))⁻¹)).smul
      (hinverse.1 y hy)
  intro m
  have he := cNorm_smul_of_contDiffAt (c.radialSection (spatialPart ζ))⁻¹
    (fun y hy ↦ (hinverse.1 y hy).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  change cNorm (closedBall x' RQ) m
      (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) =
    ‖(c.radialSection (spatialPart ζ))⁻¹‖ * cNorm (closedBall x' RQ) m
      (fun y ↦ bminus c.index Q h c.row c.col y (normalizeCovector c.radialSection ζ)) at he
  rw [he, ← mul_assoc]
  have hw : (1 + ‖ζ‖) * ‖(c.radialSection (spatialPart ζ))⁻¹‖ ≤ W :=
    (conic_inverse_weight_le c.radialSection (one_div_pos.mpr hΛ) hradial hnorm).trans
      (by dsimp [W]; linarith [le_max_right 0 Λ])
  calc
    _ ≤ W * cNorm (closedBall x' RQ) m
        (fun y ↦ bminus c.index Q h c.row c.col y (normalizeCovector c.radialSection ζ)) :=
      mul_le_mul_of_nonneg_right hw (cNorm_nonneg _ _ _)
    _ ≤ W * (D m * (1 + cNorm (closedBall x RQ) m Q)) :=
      mul_le_mul_of_nonneg_left (hinverse.2 m) hW.le
    _ = _ := by ring

end JanetCartan.RegularSector.FiniteAlgebraic
