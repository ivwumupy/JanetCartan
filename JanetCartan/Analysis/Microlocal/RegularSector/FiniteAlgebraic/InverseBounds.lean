module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SpectralSupport
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.NormalizedRoot
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.ConicInverse
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalConstruction

/-!
# Actual finite retarded family with its same-root algebraic inverse

Select the covering only after the local algebraic interval is fixed. The
literal physical multiplier then satisfies that interval's spectral condition
for every coefficient field in the common neighborhood. Its inverse bounds
come from the retained producer, not a second existential interval. The same
normalized root proves the literal complement equation and global smoothness
of the original supported source-inverse product.
Consumer: the algebraic solver and physical derivative terms of
`app:ch_regular_base:eq:energy-complete-residual`.
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

/-- Construct the actual physical evolutions and the algebraic inverse on
ONE selected finite family. The entire physical multiplier, at any enlarged
common radial threshold, stays in the SAME inverse interval. Its normalized
support lies in the actual complement domain, and the literal conic inverse
has the full-frequency order-minus-one bound with no derivative loss.
The same normalized root gives global smoothness of the supported algebraic
symbol and the literal complement equation throughout the multiplier support.
All constants precede the varying coefficients and radial enlargement.
Source: `app:ch_regular_base:thm:sector`, `complement-symbol` and
`energy-complete-residual`. This is not yet the complete sector solver. -/
theorem exists_finite_physical_evolution_and_algebraic_inverse
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Coeff) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ f : ActualMaskFamily Ω x RQ A₀ K M,
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
  obtain ⟨f, hf⟩ := exists_actualMaskFamily_with_algebraic_collar
    hΩ x hRQ hKΩ A₀ hK hKzero hregular hM
  have hradii (p : f.centers) := And.intro (hf p).1 (hf p).2.1
  refine ⟨f, hradii, ?_, ?_⟩
  · intro p
    exact exists_selected_chart_physical_operators (f.chart p) (hradii p).1 (hradii p).2 hM
      (f.angularMask p) (f.angularMask_smooth p) (f.angularMask_support p)
      (f.inputMask_compact.image (physicalCoordinates (f.chart p).index).symm.continuous)
      (hΩ.preimage (physicalCoordinates (f.chart p).index).continuous)
      (selected_input_carrier_subset_domain f p)
  intro p
  let c := f.chart p
  let x' := (physicalCoordinates c.index).symm x
  obtain ⟨_, _, hroot, hsource, a, ha, b, hb, hac, hbc, hKA, hKη, hKAopen, hKηopen,
    hHopen, hH, bound, hbound, hprimitive, ε, hε, δ, hδ, D, hD, hgap, hdomain,
    a', ha', ha'a, ha'c, hfa', V, hV, hcenter, hVc, hsupp, hVcone,
    Λ, hΛ, hcollar, hbudgets⟩ := hf p
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
