module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.RootDomain

/-!
# Full annular support and original primary domains

These are the fixed geometric inputs to `DiagonalBuffers`,
`HistoryJointPhaseJets` and `HistoryAnnularHessian`. No coefficient comparison,
moving critical point or operator interval is assumed here.
Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution
open EvolutionIntegral.KernelIdentification CompatibleResponse
open RegularSector.Characteristic.AmplitudeBounds
open AnnularComplement RegularSector.FiniteMasks

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "W" => CarrierVariables (d + 1)

/-- The ORIGINAL chart witnesses imply the fixed radius comparison needed
by the larger primary source domain. The inverse preserves output time, so
the boundary point with output time `z.1 + b` must invert into the source
ball of radius `a`. All premises are literal projections of
`exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution`;
no additional analytic bound is assumed
(`app:ch_response:eq:response-exact-phase`). -/
theorem retainedRadius_lt_rootRadius_of_original_chart
    (z : Z) {a b L : ℝ} (hb : 0 ≤ b) (haL : a < L) (ρ : ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hsource : C.source = ball (z.1, z) a)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (htime : ∀ q ∈ C.target, (C.symm q).1 = q.1) :
    UniformEvolution.retainedRadius b ρ < L := by
  let q : TwoTimePoint (Euclidean d) := (z.1 + b, z)
  have hdist : dist (z.1 + b) z.1 = b := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hb]
  have hq : q ∈ C.target := by
    apply hbuffer
    simpa only [q, mem_closedBall, Prod.dist_eq, dist_self, hdist, max_le_iff] using
      And.intro le_rfl hb
  have hs := C.map_target hq
  rw [hsource, mem_ball, Prod.dist_eq, max_lt_iff] at hs
  have hba : b < a := by
    have hh := hs.1
    rw [htime q hq] at hh
    simpa only [q, hdist] using hh
  dsimp [UniformEvolution.retainedRadius]
  linarith [min_le_left b ρ]

/-- The retained producer's root-ball physical projection gives the full
enlarged primary source domain, including its boundary. The sole extra radius
comparison is geometric and involves only the fixed retained radii. In the
original application compose `hroot` with the inclusion of the producer's
`closedBall x₀ RQ` in the original primary ball
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_primary_physical_buffer (i : Fin (d + 1)) (z : Z)
    {ε L : ℝ} (hεL : ε ≤ L) {X : Set E}
    (hroot : MapsTo (rootPhysicalPosition (coordinateSplit i)) (closedBall z L) X) :
    MapsTo (primaryCoordinateChange i).symm (closure (elapsedPhysicalBox z ε)) X := by
  let K : Set E := {x | dist (x 0) z.1 ≤ ε ∧ dist (spatialPart x) z.2.1 ≤ ε}
  have hK : IsClosed K :=
    (isClosed_le ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.dist
      continuous_const) continuous_const).inter
      (isClosed_le (spatialPartCLM.continuous.dist continuous_const) continuous_const)
  have hsub : closure (elapsedPhysicalBox z ε) ⊆ K :=
    closure_minimal (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩) hK
  intro x hx
  have hh := hsub hx
  have hw : (x 0, (spatialPart x, z.2.2)) ∈ closedBall z L := by
    simp only [mem_closedBall, Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨hh.1.trans hεL, hh.2.trans hεL, (dist_nonneg.trans hh.1).trans hεL⟩
  exact hroot hw

/-- A fixed physical margin exists at every original output point, before
coefficients or masks. This permits the retained producer's physical radii
to be chosen inside the ORIGINAL primary domain; it does not shrink an
already constructed operator (`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_primary_physical_radius (i : Fin (d + 1))
    {X : Set E} (hX : IsOpen X) {x₀ : E} (hx₀ : x₀ ∈ X) (η₀ : Euclidean d) :
    let z : Z := ((coordinateSplit i x₀).1, ((coordinateSplit i x₀).2, η₀))
    ∃ ε > (0 : ℝ), MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z (4 * ε))) X := by
  intro z
  have hz : rootPhysicalPosition (coordinateSplit i) z ∈ X := by
    change (coordinateSplit i).symm (coordinateSplit i x₀) ∈ X
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx₀
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp
    ((hX.preimage (rootPhysicalPosition (coordinateSplit i)).continuous).mem_nhds hz)
  refine ⟨a / 8, by positivity, retained_primary_physical_buffer i z le_rfl ?_⟩
  exact (closedBall_subset_ball (by linarith : 4 * (a / 8) < a)).trans hball

/-- The full normalized annular amplitude belongs to the explicit closed
frequency carrier used by `AnnularDomain`. This exposes the actual carrier
from `AnnularCarriers` without reselecting masks or discarding either radial
shoulder. Its angular hypothesis is precisely the existing inner sphere
support condition (`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedAnnularAmplitude_mem_full_frequency_carrier
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {ε aperture a b : ℝ} (hε : 0 < ε) (hAp : 0 < aperture)
    (ha : 0 < a) (hb : 0 < b) (mask : E → ℝ)
    (hm : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ η₀ (ε / 2) (aperture / 2))
    {threshold : ℝ} (ht : 0 < threshold) {r : ℕ} (A : TwoTimeAmplitude d r)
    (χout χsource : E → ℂ) (t : ℝ) {lam : ℝ} (hlam : 0 < lam) (order : ℤ)
    {v : (E × Euclidean 3) × W}
    (hv : v ∈ tsupport (Function.uncurry (AnnularSobolev.normalizedAnnularElapsedAmplitude
      A χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
      (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t lam order))) :
    v.2.snd ∈ retainedAnnularFrequencyCarrier ℓ η₀ ε aperture
      ((a / 4 / (1 + aperture / 2 + ‖η₀‖ + ε / 2)) / 2) (2 * b) := by
  let den := 1 + aperture / 2 + ‖η₀‖ + ε / 2
  have hd : 0 < den := by dsimp [den]; positivity
  have hs := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource
    (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
    (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t hlam.ne' order hv
  have hcone := dilatedConicMask_tsupport_subset_fullAngularCone ℓ η₀
    (ε / 2) (aperture / 2) mask hm ht hs.2.2.1
  have hr := tsupport_annularSelector_subset a b ha hb
    (tsupport_comp_subset Complex.ofReal_zero _ hs.2.2.2)
  have hband := normalizedSourceBand_mem_radialSectionBand ℓ (half_pos hε).le
    (half_pos hAp).le (show 0 < a / 4 by positivity) hlam
    (ξ := v.2.snd) (b := 3 * b) ⟨hcone, by linarith [hr.1], by linarith [hr.2]⟩
  have hrad : a / 4 / den ≤ ℓ (spatialPart v.2.snd) := by
    obtain ⟨⟨s, η⟩, ⟨hlo, _, he⟩, hη⟩ := hband
    rw [← hη, map_smul, smul_eq_mul, he, mul_one]
    exact hlo.1
  refine ⟨by simpa only [mem_closedBall, dist_zero_right] using hr.2,
    subset_closure ⟨?_, ?_⟩⟩
  · simpa only [inv_smul_smul₀ hlam.ne'] using
      smul_mem_fullAngularCone (inv_pos.mpr hlam) hcone
  · change (a / 4 / den) / 2 < _
    linarith [show 0 < a / 4 / den by positivity]

/-- The SAME physical masks of `AnnularMasks`, full radial selector and
dilated multiplier have their entire source/frequency support in the enlarged
integration domain. This holds for every elapsed time, so no comparison with
the original operator interval is asserted
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedAnnularAmplitude_mem_buffered_integrationDomain
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z)
    {ε aperture a b : ℝ} (hε : 0 < ε) (hAp : 0 < aperture)
    (ha : 0 < a) (hb : 0 < b) (mask : E → ℝ)
    (hm : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (ε / 4) (aperture / 2))
    {O : Set E}
    (hFO : retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture
      ((a / 4 / (1 + aperture / 2 + ‖z.2.2‖ + (ε / 2) / 2)) / 2) (2 * b) ⊆ O)
    {threshold : ℝ} (ht : 0 < threshold) {r : ℕ} (A : TwoTimeAmplitude d r)
    (χout χsource : E → ℂ)
    (hsource : tsupport χsource ⊆ elapsedPhysicalBox z (ε / 2))
    (t : ℝ) {lam : ℝ} (hlam : 0 < lam) (order : ℤ)
    {v : (E × Euclidean 3) × W}
    (hv : v ∈ tsupport (Function.uncurry (AnnularSobolev.normalizedAnnularElapsedAmplitude
      A χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
      (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t lam order))) :
    v.2 ∈ retainedOpenIntegrationDomain z ε O := by
  have hs := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource
    (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
    (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t hlam.ne' order hv
  exact retained_annular_integration_subset z hε hFO
    ⟨subset_closure (hsource hs.2.1),
      normalizedAnnularAmplitude_mem_full_frequency_carrier ℓ z.2.2 (half_pos hε) hAp ha hb
        mask (by simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hm)
        ht A χout χsource t hlam order hv⟩

end JanetCartan.ResponseTransfer.RetainedFactors
