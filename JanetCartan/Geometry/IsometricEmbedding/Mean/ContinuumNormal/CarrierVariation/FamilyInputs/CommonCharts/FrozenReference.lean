module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedReference

/-!
# Incidence normalization for the source family

The primitive seed datum here is its physical covector at the zero section,
expressed as the graph of the fixed dispersion. Its actual producer is
`CommonCharts.SeedCovector.exists_retained_seed_covector_buffer`: the Hamilton
eikonal and initial-momentum identities, local frozen-root uniqueness, and a
primitive frame threshold prove the identity for the retained flat seed.
It is distinct from matching the positive-scale family to `T.currentChart`.

From this datum and the original frozen incidence/transversality we derive the
central augmented differential using `FrozenIncidence.referenceEquiv` and
`CanonicalConic.fderiv_frozenAugmentedChart_center`. No differential gap or
inverse field is assumed. Consumer: `exists_local_common_transport_inverse`
for `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalConic

variable {n : ℕ} {P : Patch n} {U₀ : Set (Euclidean n)} {hU₀ : IsOpen U₀}
    (T : PatchQuantitativeFamily P U₀ hU₀)

/-- The literal zero-scale augmented map agrees with the named frozen map
when the seed's physical zero-section covector has the fixed dispersion graph.
The premise concerns only that primitive covector; no inverse is supplied
(`new:lem:scaling`, `app:ch_background:eq:bg-Psi`). -/
theorem sourceAugmentedTransport_zero_eq_frozen
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hVbuffer : V ⊆ ball (covectorCenter T) (2 * T.family.radius))
    (hseed : ∀ η ∈ V, gradient (fun x ↦ S (x, η)) 0 =
      (adaptedSliceCoordinates T).equiv.symm (dispersion T η, η))
    (p : InputVariables n) (hp : spatialCarrier T (p.2.1.2, p.2.1.1) ∈ V) :
    augmentedTransportGradient
      (sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1)) 0) p =
      frozenAugmentedChart T p := by
  let κ := fun η ↦ gradient (fun x ↦ S (x, η)) 0
  let η := spatialCarrier T (p.2.1.2, p.2.1.1)
  let C := (adaptedSliceCoordinates T).equiv
  have hκ : DifferentiableAt ℝ κ η :=
    (((contDiffOn_phase_positionGradient hU hV hS).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hη ↦ ⟨h0, hη⟩)).contDiffAt
        (hV.mem_nhds hp)).differentiableAt (by simp)
  have hdisp : DifferentiableAt ℝ (dispersion T) η :=
    ((dispersion_smooth T).contDiffAt (isOpen_ball.mem_nhds (hVbuffer hp))).differentiableAt
      (by simp)
  have he : κ =ᶠ[𝓝 η] (fun θ ↦ C.symm (dispersion T θ, θ)) := by
    filter_upwards [hV.mem_nhds hp] with θ hθ
    exact hseed θ hθ
  have hD := he.fderiv_eq.trans
    (C.symm.hasFDerivAt.comp η (hdisp.hasFDerivAt.prodMk (hasFDerivAt_id η))).fderiv
  have havg : transportAveragedGradient
      (sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1)) 0) p =
      C.symm (inner ℝ (gradient (dispersion T) η) p.2.2, p.2.2) := by
    rw [sourceTransportAveragedGradient_zero S _ p hκ]
    change fderiv ℝ κ η p.2.2 = _
    rw [hD]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, inner_gradient_left]
  change ((p.1.1, p.1.2, _), p.2.1.2) = ((p.1.1, p.1.2, _), p.2.1.2)
  rw [havg]
  rfl

/-- Frozen incidence and transversality supply the SAME full augmented
normalization for the explicit source family. The spectator off-diagonal
block is retained by `augmentedReferenceEquiv`. The only additional seed
hypothesis is the displayed physical zero-section covector identity, supplied
by `exists_retained_seed_covector_buffer` for the actual flat seed (`bg-Psi`). -/
theorem fderiv_sourceAugmentedTransport_zero_center
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hVbuffer : V ⊆ ball (covectorCenter T) (2 * T.family.radius))
    (hseed : ∀ η ∈ V, gradient (fun x ↦ S (x, η)) 0 =
      (adaptedSliceCoordinates T).equiv.symm (dispersion T η, η))
    (hzV : spatialCarrier T (spectatorCenter z₀, z₀ 0) ∈ V) :
    fderiv ℝ (augmentedTransportGradient
      (sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1)) 0))
        (augmentedInputCenter T (z₀ := z₀) (k := k)) =
      (augmentedReferenceEquiv T hP hz₀ hinc hd).toContinuousLinearMap := by
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  have hz : carrierParameters (spectatorCenter z₀, z₀ 0) ∈
      parameterInterior (2 * P.radius) := by
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hpatch : ContinuousAt (fun p : InputVariables n ↦
      spatialCarrier T (p.2.1.2, p.2.1.1)) p₀ :=
    ((spatialCarrier_smooth T hP).continuousOn.continuousAt
      (((isOpen_parameterInterior _).preimage carrierParameters.continuous).mem_nhds hz)).comp
        (f := fun p : InputVariables n ↦ (p.2.1.2, p.2.1.1))
        (g := spatialCarrier T) (continuousAt_snd.fst.snd.prodMk continuousAt_snd.fst.fst)
  have he : augmentedTransportGradient
      (sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1)) 0) =ᶠ[𝓝 p₀]
      frozenAugmentedChart T := by
    filter_upwards [hpatch (hV.mem_nhds hzV)] with p hp
    exact sourceAugmentedTransport_zero_eq_frozen T hU hV h0 hS hVbuffer hseed p hp
  exact he.fderiv_eq.trans (fderiv_frozenAugmentedChart_center T hP hz₀ hinc hd)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
