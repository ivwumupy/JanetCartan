module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedSeedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian

/-!
# Literal Jacobian matching on the retained source chart

The normalized transport and the actual positive-source transport agree on
the seed buffer. The segment integral and slice derivative therefore give the
same absolute Jacobian on the common input chart. Consumer: the literal
weighted source comparison (`app:ch_background:eq:bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol

/-- Matching on the original transport buffer identifies the genuine
absolute Jacobians, retaining every segment point and both positions.
`SourceMatching.current_transportPosition_source_dilation_on_patch` supplies
`hmatch`; `SeedAssembly` supplies segment containment. Source:
`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`. -/
theorem source_transportAbsoluteJacobian_eqOn_of_matching {n : ℕ}
    (c : TransportSliceCoordinates n)
    {Z Z₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {S : Set (Euclidean n × (ℝ × Euclidean 2))} (hS : IsOpen S)
    (hmatch : EqOn Z Z₀ S)
    {W : Set (InputVariables n)} (hW : IsOpen W)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W S) :
    EqOn (transportAbsoluteJacobian c Z) (transportAbsoluteJacobian c Z₀) W := by
  have hgrad : EqOn (transportAveragedGradient Z) (transportAveragedGradient Z₀) W := by
    intro p hp
    apply intervalIntegral.integral_congr
    intro t ht
    apply Filter.EventuallyEq.gradient_eq
    have hmem := hseg t (by simpa using ht) hp
    have hcont : ContinuousAt (fun x : Euclidean n ↦ (x, p.2.1))
        (p.1.2 + t • (p.1.1 - p.1.2)) := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hcont.eventually (hS.mem_nhds hmem)] with x hx
    rw [hmatch hx]
  intro p hp
  have hcont : ContinuousAt
      (fun z : Euclidean n ↦ (p.1, ((c.equiv z).1, p.2.1.2), (c.equiv z).2))
      (c.equiv.symm (p.2.1.1, p.2.2)) :=
    continuousAt_const.prodMk
      ((c.equiv.continuous.continuousAt.fst.prodMk continuousAt_const).prodMk
        c.equiv.continuous.continuousAt.snd)
  have hmem : (p.1, ((c.equiv (c.equiv.symm (p.2.1.1, p.2.2))).1, p.2.1.2),
      (c.equiv (c.equiv.symm (p.2.1.1, p.2.2))).2) ∈ W := by simpa using hp
  have he : transportSliceForward c Z p =ᶠ[𝓝 (c.equiv.symm (p.2.1.1, p.2.2))]
      transportSliceForward c Z₀ p := by
    filter_upwards [hcont.eventually (hW.mem_nhds hmem)] with z hz
    exact hgrad hz
  exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean n ↦ |L.det|) he.fderiv_eq

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
