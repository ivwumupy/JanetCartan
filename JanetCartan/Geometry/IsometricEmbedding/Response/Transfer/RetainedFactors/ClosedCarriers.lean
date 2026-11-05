module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Geometry

/-!
# Common closed carriers inside the retained conic chart

Construct a convex compact source/covector box with a positive radial gap on
the original angular section, then keep the whole elapsed interval and both
physical positions in one closed carrier. This supplies the domain and segment
premises of `HistoryElapsedHessian` and the smooth-representative application.
Critical-map containment, primary-domain containment and inclusion of the
original full time support must still be proved for the actual response.
Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.RetainedFactors
open DirectEvolution RegularSector.Characteristic ConicPhase EvolutionIntegral
open UniformEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => TwoTimePoint (Euclidean d)

/-- The compact carrier retains the full elapsed slab, both physical positions,
primary parameters and normalized covectors. Its integration-variable fiber is
a convex product when the frequency set is convex
(`app:ch_response:eq:direct-envelope-profile`). -/
def retainedClosedCarrier (z : Z) (ε : ℝ) (P : Set (Euclidean 3)) (D : Set E) :
    Set (RetainedCarrierPoint d) :=
  (Icc 0 ε ×ˢ (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ P)) ×ˢ
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
      (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ D))

/-- The original retained physical box has compact closure, with its norm
bound inherited from the producer (`app:ch_response:eq:direct-envelope-profile`). -/
theorem isCompact_closure_retained_physicalBox (z : Z) (ε : ℝ) :
    IsCompact (closure (elapsedPhysicalBox z (ε / 2))) := by
  have hb : Bornology.IsBounded (elapsedPhysicalBox z (ε / 2)) :=
    isBounded_iff_forall_norm_le.mpr
      ⟨|z.1| + ‖z.2.1‖ + 2 * (ε / 2), fun _ hx ↦ norm_le_on_elapsedPhysicalBox hx⟩
  exact isCompact_of_isClosed_isBounded isClosed_closure hb.closure

/-- Compactness includes the closed source/covector fiber and both endpoints
of elapsed time (`app:ch_response:eq:direct-envelope-profile`). -/
theorem isCompact_retainedClosedCarrier (z : Z) (ε : ℝ)
    {P : Set (Euclidean 3)} {D : Set E} (hP : IsCompact P) (hD : IsCompact D) :
    IsCompact (retainedClosedCarrier z ε P D) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  have hX := isCompact_closure_retained_physicalBox z ε
  have he : e ⁻¹' (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ D) =
      e.symm '' (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ D) := by
    ext w
    constructor
    · intro hw
      exact ⟨e w, hw, e.symm_apply_apply w⟩
    · rintro ⟨v, hv, rfl⟩
      simpa only [mem_preimage, e.apply_symm_apply] using hv
  change IsCompact ((Icc 0 ε ×ˢ (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ P)) ×ˢ
    (e ⁻¹' (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ D)))
  rw [he]
  exact (isCompact_Icc.prod (hX.prod hP)).prod ((hX.prod hD).image e.symm.continuous)

/-- The actual normalized section admits a compact convex frequency ball
with a strict nonzero spatial-frequency gap. Both the raw and normalized
covectors stay in the ORIGINAL local ball; no phase or inverse is reselected.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_retained_frequency_ball
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε : ℝ} (hε : 0 < ε)
    (hℓ : ℓ z.2.2 = 1) (θ : E) (hθ : spatialPart θ = z.2.2) :
    ∃ δ > (0 : ℝ), ∃ gap > (0 : ℝ), ∀ η ∈ closedBall θ δ,
      spatialPart η ∈ ball z.2.2 ε ∧
      spatialPart η ∈ angularCone ℓ z.2.2 ε ∧ gap ≤ ‖spatialPart η‖ := by
  have hz : z.2.2 ≠ 0 := by
    intro he
    rw [he, map_zero] at hℓ
    exact zero_ne_one hℓ
  have hn : 0 < ‖z.2.2‖ := norm_pos_iff.mpr hz
  let O := (spatialPart ⁻¹' (ball z.2.2 ε ∩ angularCone ℓ z.2.2 ε)) ∩
    {η : E | ‖z.2.2‖ / 2 < ‖spatialPart η‖}
  have hO : IsOpen O :=
    (((isOpen_ball.inter (isOpen_angularCone ℓ z.2.2 ε)).preimage spatialPartCLM.continuous).inter
      (isOpen_lt continuous_const spatialPartCLM.continuous.norm))
  have hθO : θ ∈ O := by
    change (spatialPart θ ∈ ball z.2.2 ε ∧ spatialPart θ ∈ angularCone ℓ z.2.2 ε) ∧
      ‖z.2.2‖ / 2 < ‖spatialPart θ‖
    rw [hθ]
    refine ⟨⟨mem_ball_self hε, ?_⟩, by linarith⟩
    change 0 < ℓ z.2.2 ∧ (ℓ z.2.2)⁻¹ • z.2.2 ∈ ball z.2.2 ε
    simpa only [hℓ, inv_one, one_smul] using And.intro zero_lt_one (mem_ball_self hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hθO)
  refine ⟨δ / 2, by positivity, ‖z.2.2‖ / 2, by positivity, ?_⟩
  intro η hη
  have hh := hball (closedBall_subset_ball (by linarith : δ / 2 < δ) hη)
  exact ⟨hh.1.1, hh.1.2, hh.2.le⟩

/-- Every original source/covector segment and its entire time segment remain
in the common carrier. The two integration endpoints may be distinct, as in
the actual averaged Hessian. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem retainedClosedCarrier_segments
    (z : Z) (ε : ℝ) {P : Set (Euclidean 3)} {D : Set E} (hD : Convex ℝ D)
    {t : ℝ} (ht : t ∈ Icc 0 ε) {q : E × Euclidean 3} {a w : W}
    (ha : ((t, q), a) ∈ retainedClosedCarrier z ε P D)
    (hw : ((t, q), w) ∈ retainedClosedCarrier z ε P D) :
    ∀ u ∈ uIcc (0 : ℝ) t, ∀ s ∈ Icc (0 : ℝ) 1,
      ((u, q), a + s • (w - a)) ∈ retainedClosedCarrier z ε P D := by
  intro u hu s hs
  have hu' : u ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hu
  refine ⟨⟨⟨hu'.1, hu'.2.trans ht.2⟩, ha.1.2⟩, ?_, ?_⟩
  · change (WithLp.fstL 2 ℝ E E) (a + s • (w - a)) ∈ _
    simp only [map_add, map_smul, map_sub]
    exact (convex_elapsedPhysicalBox z (ε / 2)).closure.add_smul_sub_mem ha.2.1 hw.2.1 hs
  · change (WithLp.sndL 2 ℝ E E) (a + s • (w - a)) ∈ _
    simp only [map_add, map_smul, map_sub]
    exact hD.add_smul_sub_mem ha.2.2 hw.2.2 hs

/-- Both literal graph points normalize into the SAME original closed chart
buffer on every point of the constructed carrier. This proves the common
normalization domain rather than identifying independent chart existentials.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem retainedClosedCarrier_normalizes
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε : ℝ} (hε : 0 < ε)
    {P : Set (Euclidean 3)} {D : Set E}
    (hD : ∀ θ ∈ D, spatialPart θ ∈ angularCone ℓ z.2.2 ε)
    (adj : Bool) {v : RetainedCarrierPoint d} (hv : v ∈ retainedClosedCarrier z ε P D) :
    0 < ℓ (spatialPart v.2.snd) ∧
      ConicPhase.normalize ℓ (carrierGraphPoint adj v) ∈ closedBall (z.1, z) (2 * ε) := by
  have hη := hD _ hv.2.2
  have ho := UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hv.1.2.1
  have hs := UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hv.2.1
  refine ⟨hη.1, ?_⟩
  cases adj
  · exact elapsedPoint_mem_twoTime_buffer hε hv.1.1 ho hη.2
  · exact elapsedPoint_mem_twoTime_buffer hε hv.1.1 hs hη.2

/-- Raw and normalized covectors both lie in the SAME open overlap on the
entire retained carrier, in either orientation. This supplies the zero-time
block formula as well as the positive-time local conic germ, without a second
chart (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedClosedCarrier_overlap
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε : ℝ} (hε : 0 < ε)
    {P : Set (Euclidean 3)} {D : Set E}
    (hraw : ∀ θ ∈ D, spatialPart θ ∈ ball z.2.2 ε)
    (hD : ∀ θ ∈ D, spatialPart θ ∈ angularCone ℓ z.2.2 ε)
    (adj : Bool) {v : RetainedCarrierPoint d} (hv : v ∈ retainedClosedCarrier z ε P D) :
    carrierGraphPoint adj v ∈
      localPatch (bufferedBase z ε) (ball z.2.2 (2 * ε)) ∩
        domain ℓ (localPatch (bufferedBase z ε) (ball z.2.2 (2 * ε))) := by
  have hη := hD _ hv.2.2
  have hηraw := ball_subset_ball (show ε ≤ 2 * ε by linarith) (hraw _ hv.2.2)
  have ho := UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hv.1.2.1
  have hs := UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hv.2.1
  cases adj
  · exact ⟨⟨elapsed_mem_bufferedBase hε hv.1.1 ho, hηraw⟩,
      elapsed_mem_domain_bufferedBase ℓ hε hv.1.1 ho hη⟩
  · exact ⟨⟨elapsed_mem_bufferedBase hε hv.1.1 hs, hηraw⟩,
      elapsed_mem_domain_bufferedBase ℓ hε hv.1.1 hs hη⟩

/-- The SAME full normalized annular amplitude, with both physical masks and
the original multiplier still present, is supported in the constructed common
carrier whenever those fixed masks and selector use its three factors. No
amplitude is replaced and no derivative shoulder is omitted.
Source: `app:ch_response:eq:fixed-factor-transfer`. -/
theorem normalizedAnnularAmplitude_mem_retainedClosedCarrier
    (z : Z) (ε : ℝ) {P : Set (Euclidean 3)} {D : Set E}
    {r : ℕ} (A : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (ho : tsupport χout ⊆ closure (elapsedPhysicalBox z (ε / 2)))
    (hs : tsupport χsource ⊆ closure (elapsedPhysicalBox z (ε / 2)))
    (hπ : tsupport π ⊆ D) {t lam : ℝ} (ht : t ∈ Icc 0 ε) (hlam : lam ≠ 0)
    (order : ℤ) {q : E × Euclidean 3} {w : W} (hq : q.2 ∈ P)
    (hw : (q, w) ∈ tsupport (Function.uncurry
      (AnnularSobolev.normalizedAnnularElapsedAmplitude A χout χsource β π t lam order))) :
    ((t, q), w) ∈ retainedClosedCarrier z ε P D := by
  have hh := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource β π t hlam order hw
  exact ⟨⟨ht, ho hh.1, hq⟩, hs hh.2.1, hπ hh.2.2.2⟩

end JanetCartan.ResponseTransfer.RetainedFactors
