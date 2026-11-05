module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Buffers
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.PhysicalMasks

/-!
# The actual finite chart family and fixed common masks

`exists_actualMaskFamily` constructs every field from a frozen coefficient
pencil, a compact physical coefficient neighborhood and regularity of the
protected frozen zeros. No open characteristic cover, matching masks, or
successful sector family is assumed. The same local root, section, phase
and W₀/W₁/PW₁ producer are retained in each selected `LocalChart`.

The common coefficient, physical and radial radii and all masks precede the
varying fields, orders, histories and accuracy. Explicit coordinate pullbacks
preserve the original physical partition, including its low-frequency term.
The shell-cover and source/time plateau methods apply to these SAME objects.

Consumer: the actual finite physical solver of
`app:ch_regular_base:thm:sector` and `prop:complete-residual` in `paper.tex`,
and `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
The parent still constructs and sums the operators and instantiates all
analytic estimates; this module constructs their finite geometric inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open ActualCarriers Characteristic Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral FourierIntegral.PrimitiveProfiles
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "P" => (E × E) × E

/-- Concrete fixed data for the finite physical solver. All fields are proved
by `exists_actualMaskFamily`; this record is not a premise of that constructor.
Source: `app:ch_regular_base:thm:sector` and `prop:complete-residual`. -/
structure ActualMaskFamily (Ω : Set E) (x : E) (RQ : ℝ)
    (A₀ : Fin (d + 1) → Mat) (K : Set E) (M : ℝ) where
  centers : Finset {ξ : E | ξ ∈ K ∧ determinant A₀ ξ = 0}
  chart : ∀ p : centers, LocalChart Ω x RQ A₀ p.val.val M
  angularMask : centers → E → ℝ
  spatialMask : centers → Euclidean d → ℝ
  coefficientRadius : ℝ
  determinantGap : ℝ
  physicalRadius : ℝ
  radialThreshold : ℝ
  inputMask : E → ℝ
  outputMask : E → ℝ
  coefficientRadius_pos : 0 < coefficientRadius
  determinantGap_pos : 0 < determinantGap
  physicalRadius_pos : 0 < physicalRadius
  radialThreshold_ge_one : 1 ≤ radialThreshold
  coefficientRadius_le : ∀ p, coefficientRadius ≤ (chart p).coefficientRadius
  physicalBall_subset : closedBall x (4 * physicalRadius) ⊆ Ω
  physicalBall_coefficientDomain : closedBall x (4 * physicalRadius) ⊆ closedBall x RQ
  physicalBall_in_chart : ∀ p, closedBall x (4 * physicalRadius) ⊆ (chart p).physicalNeighborhood
  angularMask_smooth : ∀ p, ContDiff ℝ ∞ (angularMask p)
  angularMask_range : ∀ p ζ, angularMask p ζ ∈ Icc (0 : ℝ) 1
  angularMask_compact : ∀ p, HasCompactSupport (angularMask p)
  angularMask_support : ∀ p, tsupport (angularMask p) ⊆ (chart p).angularNeighborhood
  angularMask_sum_le_one : ∀ ζ, ∑ p, angularMask p ζ ≤ 1
  spatialMask_properties : ∀ p, ContDiff ℝ ∞ (spatialMask p) ∧
    (∀ η, spatialMask p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (spatialMask p) ∧
    tsupport (spatialMask p) ⊆ (chart p).spatialCone
  spatialMask_plateau : ∀ p, ∀ ζ ∈ tsupport (dilatedConicMask (angularMask p) radialThreshold ∘
    physicalCoordinates (chart p).index), conicMask (spatialMask p) =ᶠ[𝓝 (spatialPart ζ)] (fun _ ↦ 1)
  inputMask_smooth : ContDiff ℝ ∞ inputMask
  outputMask_smooth : ContDiff ℝ ∞ outputMask
  inputMask_range : ∀ y, inputMask y ∈ Icc (0 : ℝ) 1
  outputMask_range : ∀ y, outputMask y ∈ Icc (0 : ℝ) 1
  inputMask_compact : HasCompactSupport inputMask
  outputMask_compact : HasCompactSupport outputMask
  inputMask_support : tsupport inputMask ⊆ ball x (3 * physicalRadius)
  outputMask_support : tsupport outputMask ⊆ ball x (2 * physicalRadius)
  outputMask_plateau : closedBall x physicalRadius ⊆ interior {y | outputMask y = 1}
  inputMask_plateau : closedBall x (2 * physicalRadius) ⊆ interior {y | inputMask y = 1}
  stable_pencil_masks : ∀ (Q : E → Fin (d + 1) → Mat) (X : Set E),
    (∀ y ∈ X, ‖Q y - A₀‖ ≤ coefficientRadius) →
    (∀ y ∈ X, ∀ ζ ∈ K ∩ tsupport (fun η ↦ 1 - ∑ p, angularMask p η),
      determinantGap ≤ |determinant (Q y) ζ|) ∧
    (∀ y ∈ X, ∀ ζ ∈ K, determinant (Q y) ζ = 0 →
      ζ ∈ interior {η | ∑ p, angularMask p η = 1})

/-- Construct the finite family, the common coefficient and physical balls,
the common enlarged radial threshold, and all original physical/angular/
spatial masks. The analytic local witnesses are those of the existing uniform
producer. Every extra premise of the finite-mask and nesting constructors is
discharged here from regularity and the actual local plateaux.
Source: `app:ch_regular_base:thm:sector`, `prop:complete-residual`. -/
theorem exists_actualMaskFamily
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) : Nonempty (ActualMaskFamily Ω x RQ A₀ K M) := by
  classical
  obtain ⟨s, chart, χ, ε, hε, δ, hδ, R, hR, hεchart, hΩball, hcoefficientBall, hball,
    hχ, hrange, hcompact, hsupp, hsum, hstable⟩ :=
    exists_finite_actual_chart_masks hΩ x hRQ hKΩ A₀ hK hKzero hregular hM
  obtain ⟨a, L, hL, ha, hap, _⟩ := exists_common_physical_radial_masks
    (fun p : s ↦ p.val.val) chart χ hsupp
  obtain ⟨input, output, hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, _⟩ :=
    exists_common_physical_masks x hR
  exact ⟨⟨s, chart, χ, a, ε, δ, R, L, input, output, hε, hδ, hR, hL,
    hεchart, hΩball, hcoefficientBall, hball, hχ, hrange, hcompact, hsupp, hsum, ha, hap,
    hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, hstable⟩⟩

namespace ActualMaskFamily
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M)

/-- Exact physical partition with the same common enlarged low-frequency
complement. Coordinates have not been identified across charts
(`prop:complete-residual`). -/
theorem complete_partition (ζ : E) :
    (∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ζ) +
      dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) f.radialThreshold ζ +
      FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 (f.radialThreshold⁻¹ • ζ) = 1 :=
  dilatedConicMask_complete_partition f.angularMask f.radialThreshold ζ

/-- Both original physical masks stay in each selected chart, on their full
closed supports (`energy-complete-residual`). -/
theorem physical_supports_in_chart (p : f.centers) :
    tsupport f.inputMask ∪ tsupport f.outputMask ⊆ (f.chart p).physicalNeighborhood :=
  physical_mask_supports_in_chart (f.chart p) f.physicalRadius_pos
    (f.physicalBall_in_chart p) f.inputMask_support f.outputMask_support

/-- The time plateau and lower-time buffer hold on BOTH original physical
supports with the retained local time mask (`retarded-kernel`). -/
theorem physical_time_plateau_and_lower_buffer (p : f.centers) {y : E}
    (hy : y ∈ tsupport f.inputMask ∪ tsupport f.outputMask) :
    (f.chart p).timeMask =ᶠ[𝓝 (coordinateSplit (f.chart p).index y).1] (fun _ ↦ 1) ∧
    (coordinateSplit (f.chart p).index x).1 - (f.chart p).maskRadius <
      (coordinateSplit (f.chart p).index y).1 := by
  have h := f.physical_supports_in_chart p hy
  exact ⟨(f.chart p).timeMask_plateau_of_mem h, (f.chart p).physical_lower_buffer h⟩

/-- The original source mask equals one on the normalized diagonal over the
common physical ball and the complete pulled-back right support. This is the
literal source factor used by the supported endpoint (`energy-complete-residual`). -/
theorem sourceMask_diagonal_eq_one (p : f.centers) {y ζ : E}
    (hy : physicalCoordinates (f.chart p).index y ∈ closedBall x (4 * f.physicalRadius))
    (hζ : ζ ∈ tsupport (dilatedConicMask (f.angularMask p) f.radialThreshold ∘
      physicalCoordinates (f.chart p).index)) :
    (f.chart p).sourceMask (rootState y
      (((f.chart p).radialSection (spatialPart ζ))⁻¹ • spatialPart ζ)) = 1 := by
  have hs := tsupport_comp_subset_preimage
    (dilatedConicMask (f.angularMask p) f.radialThreshold)
    (physicalCoordinates (f.chart p).index).continuous hζ
  have hcone := (f.chart p).angularNeighborhood_of_mem_rightSupport
    (f.angularMask_support p) f.radialThreshold_ge_one hs
  have hp := (f.chart p).sourceMask_diagonal_plateau (f.physicalBall_in_chart p hy) hcone
  simpa only [split_physicalCoordinates, rootState, mem_ofPred_eq] using interior_subset hp

/-- The complete scalar source symbol is EXACTLY one on the measurement
neighborhood and the closed physical right support; both the original source
mask and the nested spatial collar have been instantiated (`energy-complete-residual`). -/
theorem conicSourceSymbol_eq_one (p : f.centers) {y ζ : E}
    (hy : physicalCoordinates (f.chart p).index y ∈ closedBall x (4 * f.physicalRadius))
    (hζ : ζ ∈ tsupport (dilatedConicMask (f.angularMask p) f.radialThreshold ∘
      physicalCoordinates (f.chart p).index)) :
    conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
      (f.chart p).sourceMask y (spatialPart ζ) = 1 := by
  have ha := (f.spatialMask_plateau p ζ hζ).eq_of_nhds
  have hs := f.sourceMask_diagonal_eq_one p hy hζ
  simp only [conicSourceSymbol, sourceSymbol, hs, ha, Complex.ofReal_one, mul_one]

/-- The selected spatial amplitude mask satisfies the positive-section
hypothesis of the retained uniform local amplitude producer
(`characteristic-kernel`). -/
theorem spatialMask_positive_section (p : f.centers) {η : Euclidean d}
    (hη : η ∈ tsupport (f.spatialMask p)) : 0 < (f.chart p).radialSection η :=
  ((f.spatialMask_properties p).2.2.2 hη).1

/-- The original input mask is one as a germ on the full closed output
support (`energy-complete-residual`). -/
theorem inputMask_plateau_on_outputSupport :
    tsupport f.outputMask ⊆ interior {y | f.inputMask y = 1} :=
  f.outputMask_support.trans (ball_subset_closedBall.trans f.inputMask_plateau)

/-- The common coefficient ball maps into EVERY retained local producer's
ball, for the same varying field (`thm:sector`). -/
theorem mapsTo_local_coefficient_ball (p : f.centers)
    {Q : E → Fin (d + 1) → Mat} (hQ : MapsTo Q Ω (closedBall A₀ f.coefficientRadius)) :
    MapsTo Q Ω (closedBall A₀ (f.chart p).coefficientRadius) :=
  fun _y hy ↦ closedBall_subset_closedBall (f.coefficientRadius_le p) (hQ hy)

/-- The actual physical mask supports and the complete right multiplier
stay in the SAME buffered conic phase chart (`retarded-kernel`). -/
theorem right_support_in_conic_buffer (p : f.centers) {y z ζ : E}
    (hy : y ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hz : z ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hζ : ζ ∈ tsupport (dilatedConicMask (f.angularMask p) f.radialThreshold)) :
    let c := f.chart p
    let e := coordinateSplit c.index
    ((e y).1, ((e z).1, ((e y).2, (e ζ).2))) ∈ ConicPhase.domain c.radialSection
      (ball ((e x).1, ((e x).1, ((e x).2, (e p.val.val).2))) (c.bufferRadius / 2)) := by
  exact (f.chart p).pair_mem_conic_buffer (f.physical_supports_in_chart p hy)
    (f.physical_supports_in_chart p hz)
    ((f.chart p).angularNeighborhood_of_mem_rightSupport
      (f.angularMask_support p) f.radialThreshold_ge_one hζ)

/-- The actual normalized right support lies in the retained root ball,
where the SAME root producer proves determinant, minor and transport gaps
(`characteristic-kernel`). -/
theorem right_support_in_root_buffer (p : f.centers) {y ζ : E}
    (hy : y ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hζ : ζ ∈ tsupport (dilatedConicMask (f.angularMask p) f.radialThreshold)) :
    let c := f.chart p
    let e := coordinateSplit c.index
    ((e y).1, ((e y).2, (c.radialSection (e ζ).2)⁻¹ • (e ζ).2)) ∈
      closedBall ((e x).1, ((e x).2, (e p.val.val).2)) c.rootRadius := by
  exact (f.chart p).diagonal_mem_root_buffer (f.physical_supports_in_chart p hy)
    ((f.chart p).angularNeighborhood_of_mem_rightSupport
      (f.angularMask_support p) f.radialThreshold_ge_one hζ)

/-- Construct the actual finite shell covers on the original source/output
supports. The common enlarged radial threshold is already fixed; both
normalization inequalities retain constant ONE (`retarded-kernel`). -/
theorem exists_shell_cover (p : f.centers) :
    let X := tsupport f.outputMask ×ˢ tsupport f.inputMask
    ∃ (s : Finset (normalizedMaskCarrier X (f.angularMask p)))
      (ρ : normalizedMaskCarrier X (f.angularMask p) → ℝ),
      (∀ q, 0 < ρ q) ∧
      (∀ q ∈ s, closedBall (q : P) (ρ q) ⊆ (f.chart p).shellDomain) ∧
      (∀ q ∈ s, ∀ m, BoundedNormalizedSeminorm (closedBall (q : P) (ρ q)) m
        (fun z : P ↦ (dilatedConicMask (f.angularMask p) f.radialThreshold z.2 : ℂ))) ∧
      ∀ q ∈ X ×ˢ tsupport (fun ζ ↦
        (dilatedConicMask (f.angularMask p) f.radialThreshold ζ : ℂ)),
        ∃ v ∈ s, ∃ R : ℝ, 1 ≤ R ∧ ∃ w ∈ closedBall (v : P) (ρ v),
          q = (w.1, R • w.2) ∧ 1 + ‖q.2‖ ≤ R ∧ R ≤ 1 * (1 + ‖q.2‖) := by
  dsimp only
  obtain ⟨s, ρ, hρ, hball, hbound, hcover⟩ := (f.chart p).exists_dilated_shell_cover
    (f.outputMask_compact.prod f.inputMask_compact)
    (fun q hq ↦ ⟨f.physical_supports_in_chart p (Or.inr hq.1),
      f.physical_supports_in_chart p (Or.inl hq.2)⟩)
    (f.angularMask_smooth p) (f.angularMask_support p)
  exact ⟨s, ρ, hρ, hball, hbound f.radialThreshold f.radialThreshold_ge_one,
    hcover f.radialThreshold f.radialThreshold_ge_one⟩

end ActualMaskFamily
end JanetCartan.RegularSector.FiniteMasks.ActualFamily
