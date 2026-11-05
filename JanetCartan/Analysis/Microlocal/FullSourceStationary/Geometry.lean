module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.DiagonalBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.SignedCarriers

/-!
# Literal joint phases and signed carriers for full source parameters

Only the chart geometry forgets the source covector: the literal modulated
phase keeps it in both original source-phase terms. The full integration
closure and all its segments normalize into the same retained conic chart in
both orientations. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.FullSourceStationary
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open ResponseTransfer.DirectEvolution ResponseTransfer.DirectEvolution.CompactTransfer
open ResponseTransfer.RetainedFactors

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- Full external parameters and integration variables, including independent
source labels and covectors (`app:ch_response:eq:direct-envelope-profile`). -/
abbrev FullSourcePoint (d : ℕ) :=
  (ℝ × (Euclidean (d + 1) × (Euclidean 3 × Euclidean d))) × CarrierVariables (d + 1)

private def chartProjection (v : FullSourcePoint d) : RetainedCarrierPoint d :=
  ((v.1.1, (v.1.2.1, v.1.2.2.1)), v.2)

private theorem contDiff_chartProjection : ContDiff ℝ ∞ (chartProjection (d := d)) :=
  (contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk contDiff_fst.snd.snd.fst)).prodMk contDiff_snd

/-- The same literal graph point, with both original source parameters
retained in its domain (`app:ch_response:eq:fixed-factor-transfer`). -/
def fullSourceGraphPoint (adj : Bool) (v : FullSourcePoint d) : TC :=
  let x := if adj then v.2.fst else v.1.2.1
  (x 0, (x 0 - v.1.1, (spatialPart x, spatialPart v.2.snd)))

/-- The actual forward and literal-adjoint modulated phases for independent
full source parameters (`app:ch_response:eq:fixed-factor-transfer`). -/
def fullSourceJointPhase (adj : Bool) (Ψ : TwoTimePhase d)
    (φ : E → Param → ℝ) (v : FullSourcePoint d) : ℝ :=
  if adj then adjointCarrierPhase (elapsedPhase Ψ v.1.1) φ v.1.2 v.2
  else elapsedCarrierPhase Ψ v.1.1 φ v.1.2 v.2

/-- The signed compact carrier contains the entire integration closure and
the original full source parameter set (`app:ch_response:eq:direct-envelope-profile`). -/
def fullSourceSignedCarrier (z : RootState (Euclidean d))
    (ε : ℝ) (A : Set Param) (O : Set E) : Set (FullSourcePoint d) :=
  (Icc (-2 * ε) (2 * ε) ×ˢ (closure (elapsedPhysicalBox z ε) ×ˢ A)) ×ˢ
    closure (retainedOpenIntegrationDomain z ε O)

/-- Graph normalization is smooth in all full-source variables. The graph
does not couple the independent source covector to the carrier label
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_fullSourceGraphPoint (adj : Bool) :
    ContDiff ℝ ∞ (fullSourceGraphPoint (d := d) adj) :=
  (contDiff_carrierGraphPoint adj).comp contDiff_chartProjection

/-- Decompose only the parameter-independent chart contribution. Both source
terms still use the original FULL parameter, so this identity neither changes
the source phase nor restricts its covectors
(`app:ch_response:eq:response-exact-phase`). -/
theorem fullSourceJointPhase_eq_zero_source (adj : Bool) (Ψ : TwoTimePhase d)
    (φ : E → Param → ℝ) :
    fullSourceJointPhase adj Ψ φ = fun v ↦
      jointRetainedCarrierPhase adj Ψ (fun _ _ ↦ 0)
        ((v.1.1, (v.1.2.1, v.1.2.2.1)), v.2) +
        φ v.2.fst v.1.2.2 - φ v.1.2.1 v.1.2.2 := by
  funext v
  cases adj <;> simp [fullSourceJointPhase, jointRetainedCarrierPhase,
    elapsedCarrierPhase, carrierPhase, adjointCarrierPhase]

/-- Smoothness of the full-source phase in both literal orientations on the
original normalized chart domain (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiffAt_fullSourceJointPhase
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph TC TC)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (φ : E → Param → ℝ) {v : FullSourcePoint d}
    (hv : fullSourceGraphPoint adj v ∈ domain ℓ C.target)
    (hs : ContDiffAt ℝ ∞ (Function.uncurry φ) (v.2.fst, v.1.2.2))
    (ho : ContDiffAt ℝ ∞ (Function.uncurry φ) v.1.2) :
    ContDiffAt ℝ ∞ (fullSourceJointPhase adj (curriedPhase ℓ C) φ) v := by
  have hg := (contDiffAt_jointRetainedCarrierPhase adj ℓ C hC (fun _ _ ↦ 0)
    (v := chartProjection v) hv contDiffAt_const contDiffAt_const).comp v
      contDiff_chartProjection.contDiffAt
  have hsrc := hs.comp v (((WithLp.fstL 2 ℝ E E).contDiff.contDiffAt.comp v
    contDiffAt_snd).prodMk contDiffAt_fst.snd.snd)
  have hout := ho.comp v contDiffAt_fst.snd
  rw [fullSourceJointPhase_eq_zero_source]
  exact (hg.add hsrc).sub hout

/-- Compactness and both full primary projections of the signed carrier.
The free source covector is retained in each projection
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSourceSignedCarrier_geometry (z : RootState (Euclidean d)) (ε : ℝ)
    {A : Set Param} (hA : IsCompact A)
    {O : Set E} (hO : IsOpen O) (hOc : Convex ℝ O) (hOK : IsCompact (closure O)) :
    IsCompact (fullSourceSignedCarrier z ε A O) ∧
      ∀ v ∈ fullSourceSignedCarrier z ε A O,
        (v.2.fst, v.1.2.2) ∈ closure (elapsedPhysicalBox z ε) ×ˢ A ∧
        v.1.2 ∈ closure (elapsedPhysicalBox z ε) ×ˢ A := by
  have hX : IsCompact (closure (elapsedPhysicalBox z ε)) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      isCompact_closure_retained_physicalBox z (2 * ε)
  have hD := retainedOpenIntegrationDomain_geometry z ε hO hOc hOK
  exact ⟨(isCompact_Icc.prod (hX.prod hA)).prod hD.2.2.1,
    fun _ hv ↦ ⟨⟨(hD.2.2.2 _ hv.2).1, hv.1.2.2⟩, hv.1.2⟩⟩

/-- Full integration segments and both signs of the elapsed-time segment
stay in the SAME original carrier, preserving every source parameter
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSourceSignedCarrier_segments (z : RootState (Euclidean d)) (ε : ℝ)
    {O : Set E} (hOc : Convex ℝ O) {A : Set Param}
    {t : ℝ} (ht : |t| ≤ 2 * ε) {q : E × Param}
    (hq : q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A)
    {v w : W} (hv : v ∈ closure (retainedOpenIntegrationDomain z ε O))
    (hw : w ∈ closure (retainedOpenIntegrationDomain z ε O)) :
    ∀ u ∈ uIcc (0 : ℝ) t, ∀ a ∈ Icc (0 : ℝ) 1,
      ((u, q), v + a • (w - v)) ∈ fullSourceSignedCarrier z ε A O ∧
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

/-- Both literal graph orientations on the full signed carrier normalize
into the original fixed chart buffer. Forgetting a covector here is only a
projection of geometry, never a substitution in the source phase
(`app:ch_response:eq:response-exact-phase`). -/
theorem fullSourceSignedCarrier_normalizes
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d)) {ε aperture g R : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hOc : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hOK : IsCompact (closure
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)))
    {A : Set Param} (adj : Bool) {v : FullSourcePoint d}
    (hv : v ∈ fullSourceSignedCarrier z ε A
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)) :
    0 < ℓ (spatialPart v.2.snd) ∧
      normalize ℓ (fullSourceGraphPoint adj v) ∈ closedBall (z.1, z) (4 * ε) := by
  apply retainedSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK
    (Par := univ) (v := chartProjection v) adj
  exact ⟨⟨hv.1.1, hv.1.2.1, mem_univ _⟩, hv.2⟩

/-- One open neighborhood supports smoothness of BOTH literal full-source
phases, using only the same chart and original full primary domain
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_joint_phase_smooth_neighborhood
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph TC TC)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (φ : E → Param → ℝ) {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {K : Set (FullSourcePoint d)}
    (hgraph : ∀ adj : Bool, MapsTo (fullSourceGraphPoint adj) K (domain ℓ C.target))
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ Ω)
    (hout : ∀ v ∈ K, v.1.2 ∈ Ω) :
    ∃ V : Set (FullSourcePoint d), IsOpen V ∧ K ⊆ V ∧
      ∀ adj : Bool, ContDiffOn ℝ ∞ (fullSourceJointPhase adj (curriedPhase ℓ C) φ) V := by
  let src : FullSourcePoint d → E × Param := fun v ↦ (v.2.fst, v.1.2.2)
  let out : FullSourcePoint d → E × Param := fun v ↦ v.1.2
  let V := (fullSourceGraphPoint false ⁻¹' domain ℓ C.target) ∩
    (fullSourceGraphPoint true ⁻¹' domain ℓ C.target) ∩ (src ⁻¹' Ω) ∩ (out ⁻¹' Ω)
  have hs : Continuous src :=
    ((WithLp.continuous_fst 2 E E).comp continuous_snd).prodMk continuous_fst.snd.snd
  have ho : Continuous out := continuous_fst.snd
  have hd := isOpen_domain ℓ C.open_target
  refine ⟨V, (((hd.preimage (contDiff_fullSourceGraphPoint false).continuous).inter
    (hd.preimage (contDiff_fullSourceGraphPoint true).continuous)).inter
      (hΩ.preimage hs)).inter (hΩ.preimage ho),
    fun _ hv ↦ ⟨⟨⟨hgraph false hv, hgraph true hv⟩, hsrc _ hv⟩, hout _ hv⟩, ?_⟩
  intro adj v hv
  have hg : fullSourceGraphPoint adj v ∈ domain ℓ C.target := by
    cases adj
    · exact hv.1.1.1
    · exact hv.1.1.2
  exact (contDiffAt_fullSourceJointPhase adj ℓ C hC φ hg
    (hφ.contDiffAt (hΩ.mem_nhds hv.1.2))
    (hφ.contDiffAt (hΩ.mem_nhds hv.2))).contDiffWithinAt

end JanetCartan.FullSourceStationary
