module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilRoot
public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.SectionEnergy

/-!
# Identifying the direct root with the original primary covectors

For `paper-v2.tex`, `app:ch_response:eq:response-exact-phase`, construct the root
of the literal current pencil and identify its branch with a continuous family
of original characteristic covectors through the same simple point. The scalar
implicit-function uniqueness theorem proves the identity on a neighborhood,
including all spectator parameters. Root agreement is a conclusion.

The selected-carrier specialization uses the original `T.currentChart Q`.
This local construction does not assert that one root domain covers the entire
compact primary patch or the complete two-time flowout. Those common-buffer
and coordinate-pairing obligations remain with the final compatible response.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.CompatibleResponse
open ActualCarriers RegularSector.Characteristic

variable {n : ℕ} {E A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace A]

/-- The root state of an original physical point and covector in the chosen
adapted coordinates. This is only a coordinate map; no canonical pairing is
claimed for an arbitrary linear equivalence
(`app:ch_response:eq:response-exact-phase`). -/
def adaptedPrimaryRootState (e : Euclidean n ≃L[ℝ] (ℝ × E))
    (x ξ : Euclidean n) : RootState E :=
  ((e x).1, ((e x).2, (e ξ).2))

/-- Construct the actual pencil root and prove that the SAME original
characteristic covectors lie on it near their common simple base point.
Continuity retains all spectator parameters; scalar-root uniqueness supplies
the phase/root matching. No matching equation is an input
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_pencilRoot_matching_covectors
    (e : Euclidean n ≃L[ℝ] (ℝ × E))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {x ξ : A → Euclidean n} {a₀ : A}
    (hx : ContinuousAt x a₀) (hξ : ContinuousAt ξ a₀)
    (hxΩ : x a₀ ∈ Ω) (hξ₀ : ξ a₀ ≠ 0)
    (hchar : ∀ᶠ a in 𝓝 a₀, determinant (Q (x a)) (ξ a) = 0)
    (hgap : fderiv ℝ (determinant (Q (x a₀))) (ξ a₀) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState E), ∃ h : RootState E → ℝ,
      IsOpen D ∧ adaptedPrimaryRootState e (x a₀) (ξ a₀) ∈ D ∧
      h (adaptedPrimaryRootState e (x a₀) (ξ a₀)) = (e (ξ a₀)).1 ∧
      ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
          (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) ∧
      (∀ w ∈ D, ∀ c : ℝ, 0 < c →
        (w.1, (w.2.1, c • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, c • w.2.2)) = c * h w) ∧
      ∀ᶠ a in 𝓝 a₀, adaptedPrimaryRootState e (x a) (ξ a) ∈ D ∧
        (e (ξ a)).1 = h (adaptedPrimaryRootState e (x a) (ξ a)) := by
  let v := fun a ↦ adaptedPrimaryRootState e (x a) (ξ a)
  let q := fun a ↦ (e (x a), (e (ξ a)).2)
  let τ := fun a ↦ (e (ξ a)).1
  have hv : ContinuousAt v a₀ :=
    (e.continuousAt.comp hx).fst.prodMk
      ((e.continuousAt.comp hx).snd.prodMk (e.continuousAt.comp hξ).snd)
  have hq : ContinuousAt q a₀ := (e.continuousAt.comp hx).prodMk (e.continuousAt.comp hξ).snd
  have hτ : ContinuousAt τ a₀ := (e.continuousAt.comp hξ).fst
  obtain ⟨D, h, hD, haD, hbase, hh, hroot, hscale⟩ :=
    exists_pencilRoot_domain e hΩ hQ (v a₀) (τ a₀)
      (by simpa [v, adaptedPrimaryRootState] using hxΩ)
      (by simpa [v, τ, adaptedPrimaryRootState] using hξ₀)
      (by simpa [v, τ, adaptedPrimaryRootState] using hchar.self_of_nhds)
      (by simpa [v, τ, adaptedPrimaryRootState] using hgap)
  refine ⟨D, h, hD, haD, hbase, hh, hroot, hscale, ?_⟩
  let f := adaptedNormalizedPencil Q e
  let w₀ := (q a₀, τ a₀)
  let S := adaptedPencilState e ⁻¹' normalizedSymbolDomain Ω
  have hS : IsOpen S := (isOpen_normalizedSymbolDomain hΩ).preimage
    (contDiff_adaptedPencilState e).continuous
  have hwS : w₀ ∈ S := by
    simpa [S, w₀, q, τ, adaptedPencilState, normalizedSymbolDomain] using And.intro hxΩ hξ₀
  have hf : ContDiffAt ℝ ∞ f w₀ :=
    ((contDiffOn_normalizedSymbol hΩ hQ).comp
      (contDiff_adaptedPencilState e).contDiffOn (fun _ hw ↦ hw)).contDiffAt (hS.mem_nhds hwS)
  have hf₀ : f w₀ = 0 := by
    simpa [f, w₀, q, τ, adaptedNormalizedPencil, adaptedPencilState, normalizedSymbol]
      using mul_eq_zero_of_left (hchar.self_of_nhds) (determinantNormalization (ξ a₀))
  have hd := CharacteristicRoot.hasDerivAt_scalar (hf.differentiableAt (by simp))
  have hd' := hasDerivAt_adaptedNormalizedPencil Q e (e (x a₀)) (e (ξ a₀)).2 (τ a₀)
    (by simpa [τ] using hξ₀) (by simpa [τ] using hchar.self_of_nhds)
  have hscalar : CharacteristicRoot.scalarDerivative f w₀ ≠ 0 := by
    rw [hd.unique hd']
    simpa [τ] using mul_ne_zero (determinantNormalization_pos hξ₀).ne' hgap
  have huniq := CharacteristicRoot.localRoot_eventually_unique hf hscalar hf₀
  have hfirst := (hq.prodMk hτ).tendsto.eventually huniq
  have hhv : ContinuousAt (fun a ↦ h (v a)) a₀ :=
    ((hh.contDiffAt (hD.mem_nhds haD)).continuousAt).comp hv
  have ht : Tendsto (fun a ↦ (q a, h (v a))) (𝓝 a₀) (𝓝 w₀) := by
    simpa only [hbase] using (hq.prodMk hhv).tendsto
  have hsecond := ht.eventually huniq
  filter_upwards [hfirst, hsecond, hchar, hv.preimage_mem_nhds (hD.mem_nhds haD)]
    with a ha hb hc haD
  refine ⟨haD, ?_⟩
  have hfa : f (q a, τ a) = 0 := by
    simp [f, q, τ, adaptedNormalizedPencil, adaptedPencilState, normalizedSymbol, hc]
  have hfb : f (q a, h (v a)) = 0 := by
    have hr := (hroot (v a) haD).2.2.1
    simpa [f, q, v, adaptedPrimaryRootState, adaptedNormalizedPencil,
      adaptedPencilState, normalizedSymbol] using
        mul_eq_zero_of_left hr (determinantNormalization (e.symm (h (v a), (e (ξ a)).2)))
  exact (ha.mp hfa).symm.trans (hb.mp hfb)

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse RegularSector.Characteristic

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The selected primary phase stays in the original physical symbol domain,
with nonzero gradient. This follows from the SAME inverse chart and its
Hamilton flow, before constructing the direct root
(`app:ch_response:eq:response-exact-phase`). -/
theorem primary_state_mem (Q : _) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball 0 T.physicalRadius) (hz : z ∈ parameterInterior (2 * P.radius)) :
    (x, T.carrierGradient Q x z) ∈ normalizedSymbolDomain U := by
  have ht := T.reference.target_contains x hx z hz
  have ha := (T.currentChart Q).source_admissible _ ((T.currentChart Q).maps_to_source _ ht)
  have hg : T.carrierGradient Q x z =
      (T.currentChart Q).chartMomentum (x, (0, T.reference.spatialPatch z)) :=
    (T.currentChart Q).gradient_phase_eq_chartMomentum ht
  rw [hg]
  change (x, (T.family.flow Q).momentum
    (chartLift (T.currentChart Q).coordinates (x, (0, T.reference.spatialPatch z)))) ∈ _
  have hpos : (T.family.flow Q).position
      (chartLift (T.currentChart Q).coordinates (x, (0, T.reference.spatialPatch z))) = x :=
    (T.currentChart Q).right_inverse (x, (0, T.reference.spatialPatch z)) ht
  have hs := (T.family.flow Q).state_mem _ ha.1 _ ha.2
  change ((T.family.flow Q).position
      (chartLift (T.currentChart Q).coordinates (x, (0, T.reference.spatialPatch z))),
    (T.family.flow Q).momentum
      (chartLift (T.currentChart Q).coordinates (x, (0, T.reference.spatialPatch z)))) ∈
        normalizedSymbolDomain U at hs
  simpa only [hpos] using hs

/-- Construct a homogeneous direct-pencil root matching the literal selected
primary covectors on an open neighborhood of a physical/parameter base point.
Primary smoothness, characteristicity, nonzero covectors and physical-domain
membership are discharged using `T.currentChart Q`. Only the primitive simple
root gap in the chosen adapted direction remains an input; no phase/root
matching is assumed. The root is chosen before the nearby parameters.

This closes the LOCAL common-root equation in
`app:ch_response:eq:response-exact-phase`. A finite common flowout and canonical
coordinate identification are still required for the whole primary patch. -/
theorem exists_primary_matching_pencilRoot {c C : ℝ} (hP : P.IsValid c C) (Q : _)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : Euclidean n ≃L[ℝ] (ℝ × E))
    {x₀ : Euclidean n} {z₀ : Euclidean 3}
    (hx₀ : x₀ ∈ ball 0 T.physicalRadius) (hz₀ : z₀ ∈ parameterInterior (2 * P.radius))
    (hgap : fderiv ℝ (determinant (Q.1 x₀)) (T.carrierGradient Q x₀ z₀)
      (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState E), ∃ h : RootState E → ℝ,
      IsOpen D ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ U ∧ w.2.2 ≠ 0 ∧
        determinant (Q.1 (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q.1 (e.symm (w.1, w.2.1))))
          (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) ∧
      (∀ w ∈ D, ∀ a : ℝ, 0 < a →
        (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
      ∃ V : Set (Euclidean n × Euclidean 3), IsOpen V ∧ (x₀, z₀) ∈ V ∧
        V ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
        ∀ q ∈ V, adaptedPrimaryRootState e q.1 (T.carrierGradient Q q.1 q.2) ∈ D ∧
          (e (T.carrierGradient Q q.1 q.2)).1 =
            h (adaptedPrimaryRootState e q.1 (T.carrierGradient Q q.1 q.2)) := by
  let B := ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)
  have hB : IsOpen B := isOpen_ball.prod (isOpen_parameterInterior _)
  have hb : (x₀, z₀) ∈ B := ⟨hx₀, hz₀⟩
  have hs := T.primary_state_mem Q hx₀ hz₀
  obtain ⟨D, h, hD, _, _, hh, hroot, hscale, he⟩ :=
    exists_pencilRoot_matching_covectors e hU Q.2.1
      (continuousAt_fst (p := (x₀, z₀)))
      (((T.carrierGradient_smooth hP Q).contDiffAt (hB.mem_nhds hb)).continuousAt)
      hs.1 hs.2
      (show ∀ᶠ q : Euclidean n × Euclidean 3 in 𝓝 (x₀, z₀),
        determinant (Q.1 q.1) (T.carrierGradient Q q.1 q.2) = 0 from
        eventually_of_mem (hB.mem_nhds hb) (fun q hq ↦ T.carrier_characteristic Q hq.1 hq.2))
      hgap
  obtain ⟨V, hVsub, hV, hbase⟩ := _root_.mem_nhds_iff.mp (he.and (hB.mem_nhds hb))
  exact ⟨D, h, hD, hh, hroot, hscale, V, hV, hbase,
    fun q hq ↦ (hVsub hq).2, fun q hq ↦ (hVsub hq).1⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
