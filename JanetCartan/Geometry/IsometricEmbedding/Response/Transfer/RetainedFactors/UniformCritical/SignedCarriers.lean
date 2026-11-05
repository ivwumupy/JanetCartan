module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers

/-!
# Signed compact carriers for the uniform retained stationary branches

The contraction construction needs a neighborhood of elapsed time zero on
both sides. This enlarges the time factor of the existing compact annular
carrier while keeping its entire source and frequency factors. The original
chart buffer still contains both normalized graph orientations.
Consumer: the history instantiation of `exists_uniform_retained_conic_stationary_branches`,
for `app:ch_response:eq:direct-envelope-profile`.
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

/-- The full integration closure with a signed elapsed buffer. The same
carrier contains the contraction balls and the original supported annulus
(`app:ch_response:eq:direct-envelope-profile`). -/
def retainedSignedCarrier (z : Z) (ε : ℝ) (Par : Set (Euclidean 3)) (O : Set E) :
    Set (RetainedCarrierPoint d) :=
  (Icc (-2 * ε) (2 * ε) ×ˢ (closure (elapsedPhysicalBox z ε) ×ˢ Par)) ×ˢ
    closure (retainedOpenIntegrationDomain z ε O)

/-- Compactness and both primary projections of the signed full annular
carrier (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedSignedCarrier_geometry (z : Z) (ε : ℝ)
    {Par : Set (Euclidean 3)} (hPar : IsCompact Par)
    {O : Set E} (hO : IsOpen O) (hOc : Convex ℝ O) (hOK : IsCompact (closure O)) :
    IsCompact (retainedSignedCarrier z ε Par O) ∧
      ∀ v ∈ retainedSignedCarrier z ε Par O,
        (v.2.fst, v.1.2.2) ∈ closure (elapsedPhysicalBox z ε) ×ˢ Par ∧
        v.1.2 ∈ closure (elapsedPhysicalBox z ε) ×ˢ Par := by
  have hX : IsCompact (closure (elapsedPhysicalBox z ε)) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      isCompact_closure_retained_physicalBox z (2 * ε)
  have hD := retainedOpenIntegrationDomain_geometry z ε hO hOc hOK
  exact ⟨(isCompact_Icc.prod (hX.prod hPar)).prod hD.2.2.1,
    fun _ hv ↦ ⟨⟨(hD.2.2.2 _ hv.2).1, hv.1.2.2⟩, hv.1.2⟩⟩

/-- Every segment from a retained critical point to any supported integration
variable lies in this same compact carrier, together with its whole elapsed
segment in either time direction. The critical-map theorem supplies the first
endpoint's inclusion and the annular support theorem supplies the second
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedSignedCarrier_segments (z : Z) (ε : ℝ)
    {O : Set E} (hOc : Convex ℝ O) {Par : Set (Euclidean 3)}
    {t : ℝ} (ht : |t| ≤ 2 * ε) {q : E × Euclidean 3}
    (hq : q ∈ closure (elapsedPhysicalBox z ε) ×ˢ Par)
    {v w : W} (hv : v ∈ closure (retainedOpenIntegrationDomain z ε O))
    (hw : w ∈ closure (retainedOpenIntegrationDomain z ε O)) :
    ∀ u ∈ uIcc (0 : ℝ) t, ∀ a ∈ Icc (0 : ℝ) 1,
      ((u, q), v + a • (w - v)) ∈ retainedSignedCarrier z ε Par O ∧
        v + a • (w - v) ∈ closure (retainedOpenIntegrationDomain z ε O) := by
  have hD : Convex ℝ (retainedOpenIntegrationDomain z ε O) :=
    ((convex_elapsedPhysicalBox z ε).prod hOc).linear_preimage
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toLinearMap
  intro u hu a ha
  have huabs : |u| ≤ 2 * ε := by
    have h := abs_sub_left_of_mem_uIcc hu
    simp only [sub_zero] at h
    exact h.trans ht
  have hseg := hD.closure.add_smul_sub_mem hv hw ha
  exact ⟨⟨⟨⟨by linarith [(abs_le.mp huabs).1], (abs_le.mp huabs).2⟩, hq⟩, hseg⟩, hseg⟩

/-- Both normalized graph orientations stay in the original fixed chart
buffer, even at negative elapsed times. This statement precedes the varying
chart and supplies the geometry of the history jet bound
(`app:ch_response:eq:response-exact-phase`). -/
theorem retainedSignedCarrier_normalizes
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε aperture g R : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hOc : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hOK : IsCompact (closure
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)))
    {Par : Set (Euclidean 3)} (adj : Bool) {v : RetainedCarrierPoint d}
    (hv : v ∈ retainedSignedCarrier z ε Par
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)) :
    0 < ℓ (spatialPart v.2.snd) ∧
      ConicPhase.normalize ℓ (carrierGraphPoint adj v) ∈ closedBall (z.1, z) (4 * ε) := by
  have hparts := (retainedOpenIntegrationDomain_geometry z ε hO hOc hOK).2.2.2 _ hv.2
  have hθ := (retained_annular_buffer_frequency_geometry ℓ z hε hAp hg hparts.2).1
  let x := if adj then v.2.fst else v.1.2.1
  have hx : x ∈ elapsedPhysicalBox z (2 * ε) := by
    apply UniformEvolution.closure_elapsedPhysicalBox_half_subset (by positivity : 0 < 2 * ε)
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      (show x ∈ closure (elapsedPhysicalBox z ε) by
        cases adj
        · exact hv.1.2.1
        · exact hparts.1)
  have ht : |v.1.1| ≤ 2 * ε := abs_le.mpr ⟨by linarith [hv.1.1.1], hv.1.1.2⟩
  have hs : dist (x 0 - v.1.1) z.1 ≤ 4 * ε := by
    calc
      _ ≤ dist (x 0 - v.1.1) (x 0) + dist (x 0) z.1 := dist_triangle _ _ _
      _ = |v.1.1| + dist (x 0) z.1 := by
        rw [Real.dist_eq]; congr 1; ring_nf; exact abs_neg v.1.1
      _ ≤ 4 * ε := by
        have hx' := hx.1
        change dist (x 0) z.1 < 2 * ε at hx'
        linarith
  refine ⟨hθ.1, ?_⟩
  change (x 0, (x 0 - v.1.1, (spatialPart x, (ℓ (spatialPart v.2.snd))⁻¹ •
    spatialPart v.2.snd))) ∈ _
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff]
  exact ⟨hx.1.le.trans (by linarith), hs, hx.2.le.trans (by linarith),
    hθ.2.le.trans (by linarith)⟩

/-- A common open smooth neighborhood of the signed carrier for BOTH
literal phases. Only the original conic and primary domains are used;
no smooth extension or independent phase is selected
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_retained_joint_phase_smooth_neighborhood
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph TC TC)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (φ : E → Euclidean 3 → ℝ) {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {K : Set (RetainedCarrierPoint d)}
    (hgraph : ∀ adj : Bool, MapsTo (carrierGraphPoint adj) K (domain ℓ C.target))
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ Ω)
    (hout : ∀ v ∈ K, v.1.2 ∈ Ω) :
    ∃ V : Set (RetainedCarrierPoint d), IsOpen V ∧ K ⊆ V ∧
      ∀ adj : Bool, ContDiffOn ℝ ∞ (jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ) V := by
  let src : RetainedCarrierPoint d → E × Euclidean 3 := fun v ↦ (v.2.fst, v.1.2.2)
  let out : RetainedCarrierPoint d → E × Euclidean 3 := fun v ↦ v.1.2
  let V := (carrierGraphPoint false ⁻¹' domain ℓ C.target) ∩
    (carrierGraphPoint true ⁻¹' domain ℓ C.target) ∩ (src ⁻¹' Ω) ∩ (out ⁻¹' Ω)
  have hs : Continuous src :=
    ((WithLp.continuous_fst 2 E E).comp continuous_snd).prodMk continuous_fst.snd.snd
  have ho : Continuous out := continuous_fst.snd
  have hd := isOpen_domain ℓ C.open_target
  refine ⟨V, (((hd.preimage (contDiff_carrierGraphPoint false).continuous).inter
    (hd.preimage (contDiff_carrierGraphPoint true).continuous)).inter
      (hΩ.preimage hs)).inter (hΩ.preimage ho),
    fun _ hv ↦ ⟨⟨⟨hgraph false hv, hgraph true hv⟩, hsrc _ hv⟩, hout _ hv⟩, ?_⟩
  intro adj v hv
  have hg : carrierGraphPoint adj v ∈ domain ℓ C.target := by
    cases adj
    · exact hv.1.1.1
    · exact hv.1.1.2
  exact (contDiffAt_jointRetainedCarrierPhase adj ℓ C hC φ hg
    (hφ.contDiffAt (hΩ.mem_nhds hv.1.2))
    (hφ.contDiffAt (hΩ.mem_nhds hv.2))).contDiffWithinAt

end JanetCartan.ResponseTransfer.RetainedFactors
