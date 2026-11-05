module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationConstruction.JointReconstruction

/-!
# Restricting the retained full modulation to the literal carrier

The consumer is the normal-field input of the continuum row. The graph below
uses the SAME reference, minor, full scalar and compatible carrier scalar from
`exists_full_joint_leading_wave_before_geometry`. Its compatibility conclusion,
proved by flow uniqueness, is used explicitly. Sources:
`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`, and
`app:ch_background:eq:bg-mixed-input`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.LeadingPrimitive
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open LeadingWave LeadingWave.FullModulation LeadingWave.JointReconstruction
open AmbientResponse GeometricProfile CanonicalCarrier

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The fixed full-modulation graph, including the original `(s,v)` relabeling
of `app:ch_background:defn:bg-carriers`. No flow or current frame enters it. -/
def carrierGraph (p : Euclidean n × CarrierParameter) :
    Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
  (p.1, (parameter p.2, T.reference.spatialPatch (parameter p.2)))

/-- The graph is smooth on the original doubled parameter interior
(`app:ch_waves:eq:joint-tame`). -/
theorem carrierGraph_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ (carrierGraph T)
      (univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius))) := by
  have hz : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ parameter p.2)
      (univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius))) :=
    parameter.contDiff.contDiffOn.comp contDiffOn_snd (fun _ _ ↦ mem_univ _)
  exact contDiffOn_fst.prodMk (hz.prodMk
    ((T.reference.spatialPatch_smooth hP).comp hz (fun _ hp ↦ hp.2)))

/-- The full principal normal whose joint estimate is produced by the local
leading theorem (`app:ch_waves:eq:joint-tame`). -/
def fullNormal (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Euclidean N :=
  principalNormal (canonicalNormalCompletion F w.1) (phaseGradient T Q w.1 w.2.2)
    (scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w)

private theorem principalNormal_smooth_on_open
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b ξ : Euclidean n × Z → Euclidean n}
    {O : Set (Euclidean n × Z)} (hU : IsOpen U) (hO : IsOpen O) (hx : MapsTo Prod.fst O U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hb : ContDiffOn ℝ ∞ b O) (hξ : ContDiffOn ℝ ∞ ξ O) :
    ContDiffOn ℝ ∞
      (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) O := by
  have hdF := hF.fderiv_of_isOpen hU (by simp : ∞ + 1 ≤ ∞)
  have hddF := hdF.fderiv_of_isOpen hU (by simp : ∞ + 1 ≤ ∞)
  have hJF : ContDiffOn ℝ ∞ (fun p : Euclidean n × Z ↦ secondJet F p.1) O :=
    (hdF.prodMk hddF).comp contDiffOn_fst hx
  have hdb := hb.fderiv_of_isOpen hO (by simp : ∞ + 1 ≤ ∞)
  have hj : ContDiffOn ℝ ∞ (jointJet F b ξ) O :=
    (hJF.prodMk (hb.prodMk (hdb.clm_comp contDiffOn_const))).prodMk hξ
  have he : EqOn (principalNormalValue ∘ jointJet F b ξ)
      (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) O := by
    intro p hp
    exact principalNormalValue_jointJet_eq b ξ
      ((hF.contDiffAt (hU.mem_nhds (hx hp))).of_le (by simp))
      (hi _ (hx hp)) (hrank _ (hx hp))
  apply ContDiffOn.congr _ (fun p hp ↦ (he hp).symm)
  intro p hp
  have hFp : ContDiffAt ℝ 2 F p.1 :=
    (hF.contDiffAt (hU.mem_nhds (hx hp))).of_le (by simp)
  have hri : Set.range (secondJetNormalMap (secondJet F p.1)) =
      ((LinearMap.range (fderiv ℝ F p.1).toLinearMap)ᗮ : Set (Euclidean N)) := by
    rw [secondJetNormalMap_eq_of_contDiffAt hFp (hi _ (hx hp))]
    exact hrank _ (hx hp)
  exact (contDiffAt_principalNormalValue (q := jointJet F b ξ p)
    (hi _ (hx hp)) hri).comp_contDiffWithinAt p (hj p hp)

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- Smoothness of the full normal follows from the leading theorem's null
amplitude, the SAME Hamilton phase, and immersion geometry. It is not a new
analytic premise (`app:ch_waves:eq:joint-tame`). -/
theorem fullNormal_smooth {O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hO : IsOpen O) (hx : MapsTo Prod.fst O U) (hphase : O ⊆ domain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hb : ContDiffOn ℝ ∞
      (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O) :
    ContDiffOn ℝ ∞ (fullNormal T Q F row col Φ Y initial) O :=
  principalNormal_smooth_on_open hU hO hx hF hi hrank hb
    ((phaseGradient_joint_smooth T Q).mono hphase)

/-- Restriction of the retained full normal is the literal carrier normal.
The hypothesis is the scalar compatibility conclusion of
`exists_full_joint_leading_wave_before_geometry`, with the SAME two flows and
minor. Positivity alone is never used to identify the scalars
(`app:ch_waves:thm:leading`, `app:ch_background:eq:bg-T`). -/
theorem normalField_eq_fullNormal_on_graph
    {V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y initial
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y initial w)
    {p : Euclidean n × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2) ∈ V) :
    normalField T Q F row col φ y initial p.1 p.2 =
      fullNormal T Q F row col Φ Y initial (carrierGraph T p) := by
  have h := hcompat _ hp
  dsimp only at h
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  simp only [fullNormal, carrierGraph, phaseGradient_on_carrier, h,
    normalField]
  rw [nullvector_on_carrier T Q col (p.1, parameter p.2)]

end JanetCartan.ContinuumRow.LeadingPrimitive
