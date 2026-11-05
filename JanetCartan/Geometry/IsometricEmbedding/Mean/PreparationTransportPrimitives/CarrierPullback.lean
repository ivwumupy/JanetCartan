module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.Characteristic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.CarrierGraph
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# Pulling the full principal matrix back to the retained carrier

Reuse the original fixed carrier graph and the actual scalar compatibility
of the retained full-flow constructor. This transfers the full matrix norm
to the SAME retained carrier chart with no derivative loss. The principal
one-high estimate itself is the independently owned `OneHigh` obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean.PreparationTransportPrimitives
open ContinuumRow ContinuumAdjoint.Canonical ContinuumRow.LeadingPrimitive
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open LeadingWave LeadingWave.FullModulation ActualCarriers.ConstructedCarrierJets

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}

/-- Scalar compatibility on the supplied full/carrier flows identifies the
entire principal matrix, including its complex conversion. The compatibility
is the actual scalar formula exported by the before-geometry full-modulation
constructor (`app:ch_waves:eq:joint-tame`,
`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem retainedTransportMatrix_eq_fullPrincipal_on_graph
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω Kc p₀ R M τ row col F)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ Vcomp,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T c.Q F row col Φ Y initial
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T c.Q F row col c.forward c.inverse initial w)
    {p : Euclidean n × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted)
      (p.1, CanonicalCarrier.parameter p.2) ∈ Vcomp) :
    retainedTransportMatrix c initial p =
      (principalMatrix (fullNormal T c.Q F row col Φ Y initial (carrierGraph T p))
        (phaseGradient T c.Q (carrierGraph T p).1 (carrierGraph T p).2.2)).map Complex.ofReal := by
  unfold retainedTransportMatrix
  rw [normalField_eq_fullNormal_on_graph T c.Q F row col Φ Y c.forward c.inverse
    initial hcompat hp]
  rw [carrierGraph, phaseGradient_on_carrier]

/-- Fixed carrier pullback constants precede all immersions, flows and
scalars. The primitive smoothness and scalar compatibility hypotheses are
exported by `exists_full_joint_leading_wave_before_geometry_with_carrier_data_and_working_balls`
on these SAME supplied witnesses. Both compacts and the original graph are
retained, and no principal-matrix norm estimate is an input. The result is
the carrier-side input of `preparationNestedTransport_cNorm_le`
(`app:ch_waves:eq:joint-tame`, `app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem exists_retainedTransportMatrix_carrier_pullback_bounds
    (T : PatchQuantitativeFamily P U hU) {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {S J : Set (Euclidean n × CarrierParameter)} (hS : IsOpen S) (hJ : IsCompact J)
    (hJS : J ⊆ S)
    (hparameter : S ⊆ univ ×ˢ (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)))
    {Jfull : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJfull : IsCompact Jfull)
    (hgraph : MapsTo (carrierGraph T) J Jfull) :
    ∃ A : ℕ → ℝ, (∀ s, 0 < A s) ∧
      ∀ (F : Euclidean n → Euclidean N)
        (Ω Kc : Set (Euclidean n × Euclidean 3))
        (p₀ : Euclidean (n - 1) × Euclidean 3) (R M τ : ℝ) (row col : Fin n)
        (c : Chart T Ω Kc p₀ R M τ row col F)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → Jfull ⊆ O →
      MapsTo (carrierGraph T) S O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2)) S Vcomp →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T c.Q F row col Φ Y initial w • nullvector T c.Q col w) O →
      (∀ q ∈ Vcomp,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T c.Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T c.Q F row col c.forward c.inverse initial w) →
      let f := fun w ↦ (principalMatrix (fullNormal T c.Q F row col Φ Y initial w)
        (phaseGradient T c.Q w.1 w.2.2)).map Complex.ofReal
      ContDiffOn ℝ ∞ (retainedTransportMatrix c initial) S ∧
      ∀ s, cNorm J s (retainedTransportMatrix c initial) ≤ A s * cNorm Jfull s f := by
  have hψ := (carrierGraph_smooth T hP).mono hparameter
  obtain ⟨A, hA, hbound⟩ := exists_cNorm_fixed_pullback_le
    (G := Matrix (Fin N) (Fin n) ℂ) hJ hJfull
    (fun p hp ↦ hψ.contDiffAt (hS.mem_nhds (hJS hp))) hgraph
  refine ⟨A, hA, ?_⟩
  intro F Ω Kc p₀ R M τ row col c Φ Y initial O Vcomp hO hx hphase hJO hgraphO
    hcomp hF hi hrank hnull hcompat
  let f := fun w ↦ (principalMatrix (fullNormal T c.Q F row col Φ Y initial w)
    (phaseGradient T c.Q w.1 w.2.2)).map Complex.ofReal
  have hν := fullNormal_smooth T c.Q F row col Φ Y initial hO hx hphase hF hi hrank hnull
  have hξ := (phaseGradient_joint_smooth T c.Q).mono hphase
  have hf : ContDiffOn ℝ ∞ f O := by
    let entries : (Fin N → Fin n → ℂ) →L[ℝ] Matrix (Fin N) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap LinearMap.id
    apply entries.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact Complex.ofRealLI.contDiff.comp_contDiffOn
      ((((EuclideanSpace.proj i).contDiff.comp_contDiffOn hν).mul
        ((EuclideanSpace.proj j).contDiff.comp_contDiffOn hξ)).neg)
  have he : EqOn (retainedTransportMatrix c initial) (f ∘ carrierGraph T) S := by
    intro p hp
    exact retainedTransportMatrix_eq_fullPrincipal_on_graph c Φ Y initial hcompat (hcomp hp)
  refine ⟨(hf.comp hψ hgraphO).congr he, ?_⟩
  intro s
  have heq : cNorm J s (retainedTransportMatrix c initial) = cNorm J s (f ∘ carrierGraph T) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ s
    intro p hp
    exact eventuallyEq_of_mem (hS.mem_nhds (hJS hp)) (fun q hq ↦ he hq)
  rw [heq]
  exact hbound f (fun w hw ↦ hf.contDiffAt (hO.mem_nhds (hJO hw))) s

end JanetCartan.CurrentMean.PreparationTransportPrimitives
