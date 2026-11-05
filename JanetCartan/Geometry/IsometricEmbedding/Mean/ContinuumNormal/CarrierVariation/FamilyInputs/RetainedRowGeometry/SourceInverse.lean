module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.CommonTarget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceWeighted.TransportMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.SourceCompatibility

/-!
# Match the positive source on the retained input cone

The actual Hamilton source-matching theorem identifies the averaged gradient,
its full differential and the literal slice Jacobian on the whole original
input cone. The canonical inverse therefore inverts that same normalized
source on the fixed comparison target. No inverse-comparison estimate or
identity is assumed. The seed and current frames remain the actual projected
stresses of one positive seed and its contraction.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel
open ContinuumNormalReduction.TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Apply the actual retained Hamilton matching to every original segment.
The physical bound is obtained by imposing `T.physicalRadius` in the local
geometry cap; the carrier bound is retained by
`RetainedJointGeometry.exists_retained_joint_comparison_geometry` (whose
`3 * P.radius / 2` interior is contained in this doubled interior).
Both positions, the incidence root and the entire radial input cone remain
unchanged. Consumers: `actual_source_canonical_inverse` and the literal source
weighted density. Sources: `app:ch_background:eq:bg-Nsigma`,
`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`. -/
theorem actual_source_transport_on_input_cone
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hseedTrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hr : 0 < r) (haT : a ≤ T.physicalRadius) (har : a ≤ r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (2 * P.radius)) :
    EqOn (augmentedTransportGradient (transportPosition T Qσ))
      (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ))
      (symbolInputDomain zRoot ηb r a) ∧
    EqOn (fderiv ℝ (augmentedTransportGradient (transportPosition T Qσ)))
      (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)))
      (symbolInputDomain zRoot ηb r a) ∧
    EqOn (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Qσ))
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q₀ σ))
      (symbolInputDomain zRoot ηb r a) ∧
    EqOn (fun p ↦ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Qσ) p)⁻¹)
      (fun p ↦ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p)⁻¹) (symbolInputDomain zRoot ηb r a) := by
  let S := ball (0 : Euclidean n) T.physicalRadius ×ˢ
    (parameter ⁻¹' parameterInterior (2 * P.radius))
  have hS : IsOpen S := isOpen_ball.prod
    ((isOpen_parameterInterior _).preimage parameter.continuous)
  have hmatch := (SourceMatching.current_transportPosition_source_dilation_on_patch
    T Q₀ Qσ hF hrank hphysical hseed hseedTrans hσ hσ1 hscaled).1
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      MapsTo (transportSegmentInput n t) (symbolInputDomain zRoot ηb r a) S := by
    intro t ht p hp
    refine ⟨?_, ?_⟩
    · have hh := (convex_ball (0 : Euclidean n) a) hp.1.2.2 hp.1.2.1
        (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
      have heq : (1 - t) • p.1.2 + t • p.1.1 = p.1.2 + t • (p.1.1 - p.1.2) := by
        module
      apply ball_subset_ball haT
      change p.1.2 + t • (p.1.1 - p.1.2) ∈ ball 0 a
      exact heq ▸ hh
    · exact hcarrier ⟨ball_subset_closedBall (ball_subset_ball (by linarith) hp.1.1),
        ball_subset_closedBall (ball_subset_ball (by linarith) hp.2.1)⟩
  have haug := retained_augmentedTransport_eqOn_of_matching hS hmatch
    (symbolInputDomain_open zRoot ηb r a) hseg
  have hjac := source_transportAbsoluteJacobian_eqOn_of_matching (adaptedSliceCoordinates T)
    hS hmatch (symbolInputDomain_open zRoot ηb r a) hseg
  exact ⟨haug.1, haug.2, hjac, fun p hp ↦ congrArg Inv.inv (hjac hp)⟩


variable {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hseedTrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a β cJ : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (haT : a ≤ T.physicalRadius) (har : a ≤ r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (2 * P.radius))
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Qσ) (physicalParameterSet zRoot a)
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r)) V L β cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot a,
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Qσ p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hF hrank hphysical hseed hseedTrans hσ hσ1 hscaled hηb hr haT har hcarrier hInv htrans

/-- On the SAME fixed conic target, the retained canonical inverse is a
left and right inverse of the actual normalized source, with identical
absolute and reciprocal Jacobians after substitution. The source transport
identity is proved from the seed, the positive dilation and Hamilton matching.
The buffered inverse and doubled output ball are the original outputs of
`RetainedJointGeometry.exists_retained_joint_comparison_geometry`.

The final clause applies `inverse_eq_symbolInverse` to a normalized-source
inverse with its own right-inverse and input-range evidence; it assumes no
comparison between inverses. `CommonCharts` constructs normalized-source
inverses, but their range in this SAME input cone must still be retained by
the final common construction. This clause alone does not perform that
instantiation. Consumers: the source branch of `FamilyInputs` and
`SourceWeighted.exists_actual_source_weighted_comparison`. Sources:
`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`,
`app:ch_background:prop:bg-normalized`. -/
theorem actual_source_canonical_inverse
    {b τ : ℝ} (hb : 0 < b) {q₀ : Variables n × Euclidean 2}
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Qσ zRoot ηb r a) :
    let u := symbolInverse T Qσ zRoot ηb r a
    let Z := normalizedTransportPosition T Q₀ σ
    let Ω := conicTarget b q₀ τ
    (∀ q ∈ Ω, transportAveragedGradient Z (inverseCoordinates u q) = q.1.2.2) ∧
    (∀ p ∈ symbolInputDomain zRoot ηb r a,
      inverseCoordinates u (augmentedTransportGradient Z p) = p) ∧
    EqOn (fun q ↦ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Qσ) (inverseCoordinates u q))
      (fun q ↦ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        Z (inverseCoordinates u q)) Ω ∧
    EqOn (fun q ↦ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Qσ) (inverseCoordinates u q))⁻¹)
      (fun q ↦ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        Z (inverseCoordinates u q))⁻¹) Ω ∧
    (∀ v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      MapsTo (inverseCoordinates v) Ω (symbolInputDomain zRoot ηb r a) →
      (∀ q ∈ Ω, transportAveragedGradient Z (inverseCoordinates v q) = q.1.2.2) →
      EqOn v u Ω) := by
  dsimp only
  obtain ⟨haug, _, hjac, hinvJac⟩ := actual_source_transport_on_input_cone
    T Q₀ Qσ hF hrank hphysical hseed hseedTrans hσ hσ1 hscaled hr haT har hcarrier
  have hdom := conicTarget_subset_symbolDomain T Qσ hb houtput
  have hmap := (symbolInverse_maps T Qσ hηb hr hInv htrans).mono_left hdom
  have hgrad (p : InputVariables n) (hp : p ∈ symbolInputDomain zRoot ηb r a) :
      transportAveragedGradient (transportPosition T Qσ) p =
        transportAveragedGradient (normalizedTransportPosition T Q₀ σ) p :=
    congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.2) (haug hp)
  refine ⟨?_, ?_, (fun q hq ↦ hjac (hmap hq)), (fun q hq ↦ hinvJac (hmap hq)), ?_⟩
  · intro q hq
    rw [← hgrad _ (hmap hq)]
    exact transportAveragedGradient_symbolInverse T Qσ hηb hr hInv htrans (hdom hq)
  · intro p hp
    rw [← haug hp]
    exact symbolInverse_augmentedTransportGradient T Qσ hηb hr hInv htrans hp
  · intro v hv heq
    apply inverse_eq_symbolInverse T Qσ hηb hr hInv htrans hv
    intro q hq
    rw [hgrad _ (hv hq)]
    exact heq q hq

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
