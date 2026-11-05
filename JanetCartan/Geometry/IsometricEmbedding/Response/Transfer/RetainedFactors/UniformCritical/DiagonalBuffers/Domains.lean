module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Carriers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.RetardedGeometry

/-!
# Common chart and primary domains for the enlarged annular carrier

Both literal graph orientations normalize into the original chart on a
buffered signed elapsed interval. The same compact carrier supplies source,
output and segment inclusions for `HistoryJointPhaseJets` and
`HistoryAnnularHessian` (`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- The closure of the enlarged full annular buffer remains in the angular
cone required by the doubled retained closed carrier. Its positive frequency
gap applies on every segment (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_annular_buffer_frequency_geometry
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε aperture g R : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    {θ : E}
    (hθ : θ ∈ closure (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)) :
    spatialPart θ ∈ angularCone ℓ z.2.2 (2 * ε) ∧
      g / (1 + ‖ℓ‖) ≤ ‖spatialPart θ‖ ∧ ‖θ‖ ≤ R := by
  have hF : θ ∈ retainedAnnularFrequencyCarrier ℓ z.2.2 ε (2 * aperture) g R := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      closure_retainedOpenAnnularFrequencyCarrier_subset ℓ z.2.2 (ε / 2) aperture g R hθ
  have hh := retainedAnnularFrequencyCarrier_geometry ℓ z.2.2 hε
    (show 0 < 2 * aperture by positivity) hg hF
  exact ⟨⟨hh.1.1.1, ball_subset_ball (by linarith : ε ≤ 2 * ε) hh.1.1.2⟩, hh.2⟩

/-- The exact compact carrier used by both history estimates normalizes
into the original chart in both orientations. This discharges their `hpos`
and `hmap` premises from the full enlarged annulus, with no raw-frequency
ball premise (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_annular_buffer_closedCarrier_normalizes
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε aperture g R b : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g) (hb : 4 * ε ≤ b)
    {C : OpenPartialHomeomorph TC TC} (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    {Par : Set (Euclidean 3)} (adj : Bool) {v : RetainedCarrierPoint d}
    (hv : v ∈ retainedClosedCarrier z (2 * ε) Par
      (closure (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))) :
    0 < ℓ (spatialPart v.2.snd) ∧
      ConicPhase.normalize ℓ (carrierGraphPoint adj v) ∈ closedBall (z.1, z) b ∧
      carrierGraphPoint adj v ∈ domain ℓ C.target := by
  obtain ⟨hp, hn⟩ := retainedClosedCarrier_normalizes ℓ z
    (show 0 < 2 * ε by positivity)
    (fun _ hθ ↦ (retained_annular_buffer_frequency_geometry ℓ z hε hAp hg hθ).1) adj hv
  have hnb : ConicPhase.normalize ℓ (carrierGraphPoint adj v) ∈ closedBall (z.1, z) b :=
    closedBall_subset_closedBall (by linarith : 2 * (2 * ε) ≤ b) hn
  exact ⟨hp, hnb, by simpa only [carrierGraphPoint] using hp, hbuffer hnb⟩

/-- Normalize both LITERAL graph points, including negative elapsed times,
on the enlarged source domain and the FULL annular frequency closure. The
radius `4 * ε` is allowed by the original producer when
`ε = retainedRadius b ρ`, by `four_mul_retainedRadius_le`.
No pointwise chart or phase is reselected
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_annular_buffer_normalizes
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε aperture g R b : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g) (hb : 4 * ε ≤ b)
    {C : OpenPartialHomeomorph TC TC} (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (adj : Bool) {t : ℝ} (ht : |t| ≤ 2 * ε)
    {q : E × Euclidean 3} {w : W}
    (hq : q.1 ∈ closure (elapsedPhysicalBox z ε))
    (hw : w ∈ closure (retainedOpenIntegrationDomain z ε
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))) :
    0 < ℓ (spatialPart w.snd) ∧
      ConicPhase.normalize ℓ (carrierGraphPoint adj ((t, q), w)) ∈
        closedBall (z.1, z) (4 * ε) ∧
      carrierGraphPoint adj ((t, q), w) ∈ domain ℓ C.target := by
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R
  have hclosed : IsClosed (WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
      (closure (elapsedPhysicalBox z ε) ×ˢ closure O)) :=
    (isClosed_closure.prod isClosed_closure).preimage
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).continuous
  have hparts : w.fst ∈ closure (elapsedPhysicalBox z ε) ∧ w.snd ∈ closure O := by
    change w ∈ WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
      (closure (elapsedPhysicalBox z ε) ×ˢ closure O)
    apply closure_minimal ?_ hclosed hw
    exact fun _ hv ↦ ⟨subset_closure hv.1, subset_closure hv.2⟩
  have hθ := (retained_annular_buffer_frequency_geometry ℓ z hε hAp hg hparts.2).1
  let x := if adj then w.fst else q.1
  have hx : x ∈ elapsedPhysicalBox z (2 * ε) := by
    apply UniformEvolution.closure_elapsedPhysicalBox_half_subset (by positivity : 0 < 2 * ε)
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      (show x ∈ closure (elapsedPhysicalBox z ε) by
        cases adj
        · exact hq
        · exact hparts.1)
  have hs : dist (x 0 - t) z.1 ≤ 4 * ε := by
    calc
      _ ≤ dist (x 0 - t) (x 0) + dist (x 0) z.1 := dist_triangle _ _ _
      _ = |t| + dist (x 0) z.1 := by rw [Real.dist_eq]; congr 1; ring_nf; exact abs_neg t
      _ ≤ 4 * ε := by have hx' := hx.1; change dist (x 0) z.1 < 2 * ε at hx'; linarith
  have hn : ConicPhase.normalize ℓ (carrierGraphPoint adj ((t, q), w)) ∈
      closedBall (z.1, z) (4 * ε) := by
    change (x 0, (x 0 - t, (spatialPart x, (ℓ (spatialPart w.snd))⁻¹ • spatialPart w.snd))) ∈ _
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨hx.1.le.trans (by linarith), hs, hx.2.le.trans (by linarith),
      hθ.2.le.trans (by linarith)⟩
  exact ⟨hθ.1, hn, hθ.1, hbuffer (closedBall_subset_closedBall hb hn)⟩

/-- Every integration segment, and every intermediate nonnegative elapsed
time, lies in the SAME compact carrier. This supplies the exact segment
premise of the history Hessian estimate; its integration points may be
different (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_buffered_domain_segments (z : Z) (ε : ℝ)
    {O : Set E} (hO : IsOpen O) (hOc : Convex ℝ O) (hOK : IsCompact (closure O))
    {Par : Set (Euclidean 3)} {t : ℝ} (ht : t ∈ Icc 0 (2 * ε))
    {q : E × Euclidean 3} (hq : q ∈ closure (elapsedPhysicalBox z ε) ×ˢ Par)
    {v w : W} (hv : v ∈ closure (retainedOpenIntegrationDomain z ε O))
    (hw : w ∈ closure (retainedOpenIntegrationDomain z ε O)) :
    ∀ u ∈ uIcc (0 : ℝ) t, ∀ a ∈ Icc (0 : ℝ) 1,
      ((u, q), v + a • (w - v)) ∈ retainedClosedCarrier z (2 * ε) Par (closure O) ∧
        v + a • (w - v) ∈ closure (retainedOpenIntegrationDomain z ε O) := by
  have hsegments := retainedClosedCarrier_segments z (2 * ε) hOc.closure ht
    (retainedOpenIntegrationDomain_mem_closedCarrier z ε hO hOc hOK ht hq hv)
    (retainedOpenIntegrationDomain_mem_closedCarrier z ε hO hOc hOK ht hq hw)
  exact fun u hu a ha ↦ ⟨hsegments u hu a ha,
    (retainedOpenIntegrationDomain_geometry z ε hO hOc hOK).2.1.closure.add_smul_sub_mem hv hw ha⟩

end JanetCartan.ResponseTransfer.RetainedFactors

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ResponseTransfer.RetainedFactors
open RegularSector.Characteristic

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)

/-- The exact compact primary domain used by the joint phase and annular
Hessian estimates contains BOTH physical projections of the enlarged closed
carrier, and is inside the original primary family's physical/parameter
domain. The physical premise is supplied by
`retained_primary_physical_buffer`, and the parameter premise by the actual
`RootDomain` comparison (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_annular_buffer_primary_domains
    (i : Fin (d + 1)) (z : RootState (Euclidean d)) (ε : ℝ)
    {c₀ : Euclidean 3} {s : ℝ} (hs : 0 < s)
    (hparam : closedBall c₀ (4 * s) ⊆ parameterInterior (2 * P.radius))
    (hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z ε)) (ball 0 T.physicalRadius))
    {F : Set E} (hF : IsCompact F) :
    let Par := closedBall c₀ (2 * s)
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ Par
    let K := retainedClosedCarrier z (2 * ε) Par F
    IsCompact KP ∧ IsCompact K ∧
      (∀ q ∈ KP, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
        q.2 ∈ parameterInterior (2 * P.radius)) ∧
      (∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ KP) ∧
      (∀ v ∈ K, v.1.2 ∈ KP) := by
  intro Par KP K
  have hX : IsCompact (closure (elapsedPhysicalBox z ε)) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      isCompact_closure_retained_physicalBox z (2 * ε)
  refine ⟨hX.prod (isCompact_closedBall _ _),
    isCompact_retainedClosedCarrier z (2 * ε) (isCompact_closedBall _ _) hF,
    fun _ hq ↦ ⟨hphysical hq.1,
      hparam (closedBall_subset_closedBall (by linarith : 2 * s ≤ 4 * s) hq.2)⟩, ?_, ?_⟩
  · intro v hv
    have hv' : v.2.fst ∈ closure (elapsedPhysicalBox z ((2 * ε) / 2)) := hv.2.1
    exact ⟨by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hv',
      hv.1.2.2⟩
  · intro v hv
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hv.1.2

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
