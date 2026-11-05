module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.ConicGeometry

/-!
# Compatibility with the supplied positive-source geometry

Transport matching on an open original-variable buffer identifies the full
augmented map and its differential. Left-inverse identities, followed by
homogeneity, identify the refined conic inverse with the supplied source
inverse on the common normalized target and its whole radial cone.

Consumers: the retained positive-reference geometry construction and the
source weighted comparison. Sources: `app:ch_background:eq:bg-Psi`,
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CanonicalConic

/-- The actual source/retained transport identity gives equality of the FULL
augmented map, including its differential on the open segment buffer.
The matching producer is
`SourceMatching.current_transportPosition_source_dilation_on_patch`.
This transfers the supplied source central gap before the retained domains
are refined (`bg-Psi`). -/
theorem retained_augmentedTransport_eqOn_of_matching {n : ℕ}
    {Y Z : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1)}
    {S : Set (Euclidean n × ContinuumRow.CarrierParameter)} (hS : IsOpen S)
    (hmatch : EqOn Y Z S)
    {W : Set (InputVariables n)} (hW : IsOpen W)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W S) :
    EqOn (augmentedTransportGradient Y) (augmentedTransportGradient Z) W ∧
      EqOn (fderiv ℝ (augmentedTransportGradient Y))
        (fderiv ℝ (augmentedTransportGradient Z)) W := by
  have hgrad : EqOn (transportAveragedGradient Y) (transportAveragedGradient Z) W := by
    intro p hp
    apply intervalIntegral.integral_congr
    intro t ht
    apply Filter.EventuallyEq.gradient_eq
    have hmem := hseg t (by simpa using ht) hp
    have hcont : ContinuousAt (fun x : Euclidean n ↦ (x, p.2.1))
        (p.1.2 + t • (p.1.1 - p.1.2)) := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hcont.eventually (hS.mem_nhds hmem)] with x hx
    rw [hmatch hx]
  have heq : EqOn (augmentedTransportGradient Y) (augmentedTransportGradient Z) W := by
    intro p hp
    simp only [augmentedTransportGradient, hgrad hp]
  refine ⟨heq, ?_⟩
  intro p hp
  have hh : augmentedTransportGradient Y =ᶠ[𝓝 p] augmentedTransportGradient Z :=
    (hW.eventually_mem hp).mono (fun q hq ↦ heq hq)
  exact hh.fderiv_eq

/-- A nonzero input covector cannot have zero output under a regular full
augmented differential. This derives the frequency condition needed by the
retained mask construction from the supplied reference gap and literal
homogeneity, without a separate output-frequency premise (`bg-Psi`). -/
theorem retained_transport_nonzero_of_augmented_gap {n : ℕ}
    {Y : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1)}
    {p : InputVariables n} (hη : p.2.2 ≠ 0)
    (hf : DifferentiableAt ℝ (augmentedTransportGradient Y) p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hgap : ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) :
    transportAveragedGradient Y p ≠ 0 := by
  intro hz
  let v : InputVariables n := (0, (0, p.2.2))
  have hpath : HasDerivAt (fun t : ℝ ↦ scaleInput t p) v 1 := by
    simpa only [scaleInput, v, one_smul, id_eq] using
      (hasDerivAt_const (1 : ℝ) p.1).prodMk
        ((hasDerivAt_const (1 : ℝ) p.2.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const p.2.2))
  have hfp : HasFDerivAt (augmentedTransportGradient Y)
      (fderiv ℝ (augmentedTransportGradient Y) p) (scaleInput 1 p) := by
    simpa only [scaleInput, one_smul] using hf.hasFDerivAt
  have hcomp := hfp.comp_hasDerivAt 1 hpath
  have heq : augmentedTransportGradient Y ∘ (fun t : ℝ ↦ scaleInput t p) =
      fun _ : ℝ ↦ augmentedTransportGradient Y p := by
    funext t
    change augmentedTransportGradient Y (scaleInput t p) = augmentedTransportGradient Y p
    rw [augmentedTransportGradient_scaleInput]
    simp only [augmentedTransportGradient, hz, scaleFrequency, smul_zero]
  rw [heq] at hcomp
  have hv := hcomp.unique (hasDerivAt_const (1 : ℝ) (augmentedTransportGradient Y p))
  have hinj := (FullPhaseCharts.bijective_of_normalized_gap
    (ContinuousLinearEquiv.refl ℝ (InputVariables n)) (by simpa using hgap)).1
  have hv0 : v = 0 := hinj (by simp only [ContinuousLinearMap.comp_apply, hv, map_zero])
  exact hη (congrArg (fun p : InputVariables n ↦ p.2.2) hv0)

/-- The supplied original conic support contains a neighborhood of its
retained center. Refining inside this neighborhood preserves the source
left-inverse identity on the entire new compact input buffer. Consumer:
`exists_retained_source_conic_geometry` (`bg-Psi`, `bg-full-complex-amplitude`). -/
theorem retained_conicMaskSupport_center_mem_interior {n : ℕ}
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (((0, 0), (z₀ 0, FullPhaseCharts.ActualComparison.spectatorCenter z₀), ηb) : InputVariables n) ∈
      interior (conicMaskSupport z₀ ηb r a) := by
  let p₀ : InputVariables n :=
    ((0, 0), (z₀ 0, FullPhaseCharts.ActualComparison.spectatorCenter z₀), ηb)
  apply mem_interior_iff_mem_nhds.mpr
  have hx : ∀ᶠ p : InputVariables n in 𝓝 p₀, p.1.1 ∈ closedBall 0 (4 * a) :=
    continuousAt_fst.fst (closedBall_mem_nhds _ (by positivity))
  have hy : ∀ᶠ p : InputVariables n in 𝓝 p₀, p.1.2 ∈ closedBall 0 (4 * a) :=
    continuousAt_fst.snd (closedBall_mem_nhds _ (by positivity))
  have hs : ∀ᶠ p : InputVariables n in 𝓝 p₀, p.2.1.1 ∈ closedBall (z₀ 0) (a / 2) :=
    continuousAt_snd.fst.fst (closedBall_mem_nhds _ (half_pos ha))
  have hv : ∀ᶠ p : InputVariables n in 𝓝 p₀,
      p.2.1.2 ∈ closedBall (FullPhaseCharts.ActualComparison.spectatorCenter z₀) (a / 2) :=
    continuousAt_snd.fst.snd (closedBall_mem_nhds _ (half_pos ha))
  have hn : ∀ᶠ p : InputVariables n in 𝓝 p₀, p.2.2 ≠ 0 :=
    (isOpen_ne_fun continuous_snd.snd continuous_const).mem_nhds hηb
  have hc : ContinuousAt (fun p : InputVariables n ↦ NormedSpace.normalize p.2.2) p₀ :=
    (continuousAt_snd.snd.norm.inv₀ (norm_ne_zero_iff.mpr hηb)).smul continuousAt_snd.snd
  have hθ : ∀ᶠ p : InputVariables n in 𝓝 p₀,
      NormedSpace.normalize p.2.2 ∈ closedBall (NormedSpace.normalize ηb) (angularWidth ηb r / 2) :=
    hc (closedBall_mem_nhds _ (half_pos (angularWidth_spec hηb hr).1))
  filter_upwards [hx, hy, hs, hv, hn, hθ] with p hpx hpy hps hpv hpn hpθ
  exact ⟨⟨hpx, hpy⟩, ⟨hps, hpv⟩, hpn,
    ⟨mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hpn), hpθ⟩⟩

/-- Identify the constructed inverse with a supplied source inverse using
its actual left-inverse identity on the old input domain. The compact range
may be strictly smaller than that domain. Positive homogeneity extends the
identity to the entire cone over the fixed compact target, which contains
the normalized uncut support. No inverse continuity or range in the refined
compact is assumed for the old inverse (`bg-Psi`, `bg-full-complex-amplitude`). -/
theorem retained_conic_inverse_eq_of_source_left_inverse {n : ℕ}
    {Y : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1)}
    {u v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Q Ω : Set (Variables n × Euclidean 2)} {Ki H : Set (InputVariables n)}
    (hrange : MapsTo (inverseCoordinates u) Q Ki) (hKiH : Ki ⊆ H)
    (hQΩ : Q ⊆ Ω)
    (heq : ∀ q ∈ Ω, transportAveragedGradient Y (inverseCoordinates u q) = q.1.2.2)
    (hleft : EqOn (inverseCoordinates v ∘ augmentedTransportGradient Y) id H)
    (hu : ∀ t : ℝ, 0 < t → ∀ q, u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2))
    (hv : ∀ t : ℝ, 0 < t → ∀ q, v (scaleFrequency t q.1, q.2) = ((v q).1, t • (v q).2))
    {b : ℝ} (hb : 0 < b) :
    EqOn u v Q ∧ EqOn u v (normalizedConicTarget b Q) := by
  have hlocal : EqOn u v Q := by
    intro q hq
    have hh := hleft (hKiH (hrange hq))
    change inverseCoordinates v (augmentedTransportGradient Y (inverseCoordinates u q)) =
      inverseCoordinates u q at hh
    have hhq : augmentedTransportGradient Y (inverseCoordinates u q) = q :=
      augmentedTransportGradient_inverseCoordinates Y u heq (hQΩ hq)
    rw [hhq] at hh
    exact Prod.ext (congrArg (fun p : InputVariables n ↦ p.2.1.1) hh.symm)
      (congrArg (fun p : InputVariables n ↦ p.2.2) hh.symm)
  refine ⟨hlocal, ?_⟩
  intro q hq
  let t := b / ‖q.1.2.2‖
  have ht : 0 < t := div_pos hb (norm_pos_iff.mpr hq.1)
  have hh := hlocal hq.2
  change u (scaleFrequency t q.1, q.2) = v (scaleFrequency t q.1, q.2) at hh
  rw [hu t ht q, hv t ht q] at hh
  apply Prod.ext
  · have hh1 := congrArg (fun p : ℝ × Euclidean (n - 1) ↦ p.1) hh
    exact hh1
  · exact (smul_right_injective _ ht.ne')
      (congrArg (fun p : ℝ × Euclidean (n - 1) ↦ p.2) hh)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
