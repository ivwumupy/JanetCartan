module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Source
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalConstruction

/-!
# Physical geometry of the endpoint on the selected finite family

The literal doubled physical multiplier has a uniform temporal cone and value
bound on the SAME selected chart. The common physical ball supplies the
coefficient-domain inclusion and both diagonal time coordinates required by
`EndpointPdoBounds.exists_supported_endpoint_pdo_budgets`.
The radial-band inclusion is a separate obligation of the retained evolution
constructor; no shell coverage is inferred from positivity of its radii.
Sources: `app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EndpointPdoBounds FiniteMasks FiniteMasks.ActualFamily
open FiniteAlgebraic FiniteEvolution
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The right multiplier at the retained common threshold. The coordinate
permutation remains INSIDE the physical radial cutoff
(`energy-complete-residual`, direct PDO index two). -/
def selectedEndpointMultiplier (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) (L : ℝ) (ζ : E) : ℂ :=
  dilatedConicMask (f.angularMask p) (2 * L) (physicalCoordinates (f.chart p).index ζ)

/-- Smoothness and the value bound of the exact selected multiplier, before
varying coefficients or Sobolev order (`fixed-time-representation`). -/
theorem selectedEndpointMultiplier_bounds (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) (L : ℝ) :
    ContDiff ℝ ∞ (selectedEndpointMultiplier f p L) ∧
      ∀ ζ, ‖selectedEndpointMultiplier f p L ζ‖ ≤ 1 := by
  have h := complex_dilatedConicMask_pdo_bounds (f.angularMask p)
    (f.angularMask_smooth p) (f.angularMask_range p) (2 * L)
  exact ⟨h.1.comp (physicalCoordinates (f.chart p).index).contDiff,
    fun ζ ↦ h.2 (physicalCoordinates (f.chart p).index ζ)⟩

/-- One temporal cone works for every positive enlarged threshold on the
selected chart. It is proved from the actual angular carrier, not assumed
as an endpoint-symbol estimate (`fixed-time-representation`). -/
theorem exists_selectedEndpointMultiplier_temporal_cone
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) :
    ∃ C ≥ (0 : ℝ), ∀ L > (0 : ℝ), ∀ ζ ∈ tsupport (selectedEndpointMultiplier f p L),
      |ζ 0| ≤ C * ‖spatialPart ζ‖ := by
  let c := f.chart p
  let e := coordinateSplit c.index
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
  obtain ⟨aperture, hAp, hcarrier⟩ := exists_chart_temporal_aperture c hρb hsrcρ
    (f.angularMask p) (f.angularMask_support p)
  refine ⟨(aperture / 2) * ‖c.radialSection‖, by positivity, ?_⟩
  intro L hL ζ hζ
  have hcanonical := PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
    (f.angularMask p) c.index hL hζ
  have hreal := tsupport_comp_subset Complex.ofReal_zero
    (dilatedConicMask (f.angularMask p ∘ physicalCoordinates c.index) L) hcanonical
  have hcone := dilatedConicMask_tsupport_subset_fullAngularCone c.radialSection z
    (retainedRadius c.targetRadius c.bufferRadius / 4) (aperture / 2)
    (f.angularMask p ∘ physicalCoordinates c.index) hcarrier hL hreal
  have hsection : c.radialSection (spatialPart ζ) ≤
      ‖c.radialSection‖ * ‖spatialPart ζ‖ :=
    (le_abs_self _).trans (c.radialSection.le_opNorm (spatialPart ζ))
  calc
    |ζ 0| ≤ aperture / 2 * c.radialSection (spatialPart ζ) := hcone.2.le
    _ ≤ aperture / 2 * (‖c.radialSection‖ * ‖spatialPart ζ‖) :=
      mul_le_mul_of_nonneg_left hsection (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- The endpoint's common chart ball maps into the ORIGINAL coefficient
ball. This discharges `hphysical` in both endpoint budget producers
(`energy-complete-residual`). -/
theorem selectedEndpoint_physical_ball_mapsTo
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    MapsTo (physicalCoordinates (f.chart p).index)
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) (2 * f.physicalRadius))
      (closedBall x RQ) := by
  intro y hy
  apply f.physicalBall_coefficientDomain
  have he : dist (physicalCoordinates (f.chart p).index y) x =
      dist y ((physicalCoordinates (f.chart p).index).symm x) := by
    conv_lhs => arg 2; rw [← (physicalCoordinates (f.chart p).index).apply_symm_apply x]
    rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
  change dist (physicalCoordinates (f.chart p).index y) x ≤ 4 * f.physicalRadius
  rw [he]
  exact hy.trans (by linarith [f.physicalRadius_pos])

/-- The original common output mask lies in the smaller endpoint ball;
the coefficient radius need not fit inside the amplitude's time buffer
(`energy-complete-residual`). -/
theorem chartOutputMask_support_endpointBall
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    tsupport (chartOutputMask f p) ⊆
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (2 * f.physicalRadius) := by
  intro y hy
  have ht := tsupport_comp_subset_preimage
    (fun y ↦ (f.outputMask y : ℂ)) (physicalCoordinates (f.chart p).index).continuous hy
  have hs := tsupport_comp_subset Complex.ofReal_zero f.outputMask ht
  have hb := (mem_ball.mp (f.outputMask_support hs)).le
  change dist y ((physicalCoordinates (f.chart p).index).symm x) ≤ 2 * f.physicalRadius
  have he : dist (physicalCoordinates (f.chart p).index y) x =
      dist y ((physicalCoordinates (f.chart p).index).symm x) := by
    conv_lhs => arg 2; rw [← (physicalCoordinates (f.chart p).index).apply_symm_apply x]
    rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
  rwa [he] at hb

/-- Every point of the endpoint ball fits both diagonal time slots and the
spatial position buffer at `ε = bufferRadius/2`. The normalized frequency
band must still be supplied for the SAME retained `ra,rb`
(`energy-complete-residual`). -/
theorem selectedEndpoint_diagonal_position_buffer
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    ∀ y ∈ closedBall ((physicalCoordinates (f.chart p).index).symm x)
      (2 * f.physicalRadius),
      y 0 ∈ closedBall (coordinateSplit (f.chart p).index x).1
        (2 * ((f.chart p).bufferRadius / 2)) ∧
      spatialPart y ∈ closedBall (coordinateSplit (f.chart p).index x).2
        (2 * ((f.chart p).bufferRadius / 2)) := by
  intro y hy
  let c := f.chart p
  have he : dist (physicalCoordinates c.index y) x =
      dist y ((physicalCoordinates c.index).symm x) := by
    conv_lhs => arg 2; rw [← (physicalCoordinates c.index).apply_symm_apply x]
    rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
  have hb : physicalCoordinates c.index y ∈ closedBall x (4 * f.physicalRadius) := by
    change dist (physicalCoordinates c.index y) x ≤ 4 * f.physicalRadius
    rw [he]
    exact hy.trans (by linarith [f.physicalRadius_pos])
  have hchart := f.physicalBall_in_chart p hb
  change dist (coordinateSplit c.index (physicalCoordinates c.index y))
    (coordinateSplit c.index x) < c.neighborhoodRadius at hchart
  rw [split_physicalCoordinates, Prod.dist_eq, max_lt_iff] at hchart
  have hsmall : c.neighborhoodRadius ≤ c.bufferRadius / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hr : c.neighborhoodRadius ≤ 2 * (c.bufferRadius / 2) := by
    linarith [c.bufferRadius_pos]
  exact ⟨hchart.1.le.trans hr, hchart.2.le.trans hr⟩

end JanetCartan.RegularSector.FinitePdo
