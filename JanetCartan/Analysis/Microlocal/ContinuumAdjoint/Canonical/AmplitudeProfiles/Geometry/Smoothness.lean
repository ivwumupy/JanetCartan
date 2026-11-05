module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NormalField
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Detector
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.TransportComponents

/-!
# Smoothness of the literal geometric adjoint component

The normal is reconstructed with the actual nullvector, with no scalar or flow.
The only coefficient regularity used is the nullvector regularity retained by
`NullTransport.exists_projected_local_positive_amplitude`. Fixed chart containment
places the cutoff support inside that producer's coefficient ball.

Consumer: `hc` in `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Sources: `app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-adjoint`,
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open LeadingWave AmbientResponse GeometricProfile LeadingWave.JointReconstruction
open DerivativeKernels

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Smoothness of the scalar-free principal normal on its actual open chart.
The separate immersion and normal-rank hypotheses are primitive geometry;
the coefficient regularity is a retained null-transport output
(`app:ch_waves:eq:joint-tame`). -/
theorem geometricNormal_contDiffOn {c C : ℝ} (hP : P.IsValid c C)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) (col : Fin n)
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)))
    {z : Euclidean 3} {ρ : ℝ}
    (hcoef : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (closedBall ((0 : Euclidean n), z) ρ))
    (hnull : ∀ w ∈ closedBall ((0 : Euclidean n), z) ρ,
      ContDiffAt ℝ ∞ (carrierNullvector T Q col) w) :
    ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      geometricNormal T Q F col (p.2, p.1)) (X ×ˢ V) := by
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)
  let b := fun p ↦ carrierNullvector T Q col (ψ p)
  let ξ := fun p : Euclidean n × CarrierParameter ↦ T.carrierGradient Q p.1
    (CanonicalCarrier.parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_fst.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_snd)
  have hb : ContDiffOn ℝ ∞ b (X ×ˢ V) := by
    change ContDiffOn ℝ ∞ ((carrierNullvector T Q col) ∘ ψ) (X ×ˢ V)
    intro p hp
    exact ((hnull (ψ p) (hcoef hp)).comp p (hψ.contDiffAt)).contDiffWithinAt
  have hξ : ContDiffOn ℝ ∞ ξ (X ×ˢ V) :=
    (T.carrierGradient_smooth hP Q).comp (f := ψ) (s := X ×ˢ V) hψ.contDiffOn hc
  have hj := contDiffOn_jointJet hX hV (hF.mono hXU) hb hξ
  intro p hp
  have hFp : ContDiffAt ℝ 2 F p.1 :=
    (hF.contDiffAt (hU.mem_nhds (hXU hp.1))).of_le (by simp)
  have hri : Set.range (secondJetNormalMap (secondJet F p.1)) =
      ((LinearMap.range (fderiv ℝ F p.1).toLinearMap)ᗮ : Set (Euclidean N)) := by
    rw [secondJetNormalMap_eq_of_contDiffAt hFp (hi _ (hXU hp.1))]
    exact hrank _ (hXU hp.1)
  have hvalue := contDiffAt_principalNormalValue
    (q := jointJet F b ξ p) (hi _ (hXU hp.1)) hri
  have he := (jointJet_fields_eventuallyEq ξ hX hV (hF.mono hXU) hb
    (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx)) hp).1
  exact ((hvalue.comp p (hj.contDiffAt ((hX.prod hV).mem_nhds hp))).congr_of_eventuallyEq
    he.symm).contDiffWithinAt

/-- The literal component in physical/carrier order. Its detector remains
the original quadratic stress contraction (`app:ch_background:eq:bg-T`). -/
def physicalGeometryComponent (F : Euclidean n → Euclidean N) (col : Fin n)
    (z : Euclidean 3) {a : ℝ} (ha : 0 < a) (j : Fin n)
    (p : Euclidean n × CarrierParameter) : ℂ :=
  ((FixedCutoffs.physical ha 1) p.1 *
    ‖extendedGeometricNormal T Q F col z ha (p.2, p.1)‖ ^ 2 *
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (CanonicalCarrier.parameter p.2)) j : ℝ)

/-- The original detector contributes no additional support: the geometric
normal cutoff already localizes the entire component (`bg-T`). -/
theorem physicalGeometryComponent_tsupport_subset
    (F : Euclidean n → Euclidean N) (col : Fin n)
    (z : Euclidean 3) {a : ℝ} (ha : 0 < a) (j : Fin n) :
    tsupport (physicalGeometryComponent T Q F col z ha j) ⊆ tsupport (chartBump z ha) := by
  apply (isClosed_tsupport _).closure_subset_iff.mpr
  intro p hp
  by_contra hn
  have hz : chartBump z ha p = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hp (by simp [physicalGeometryComponent, extendedGeometricNormal, hz])

/-- The exact component required by the adjoint endpoint, with no dependence
on the scalar or flow hidden in its geometric factor (`bg-T`). -/
theorem carrierChartGeometryComponent_eq_physicalGeometryComponent
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) {a : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) (j : Fin n) :
    carrierChartGeometryComponent
        (CanonicalCarrier.data T Q F row col Φ Y initial ha hcell angular high)
        (FixedCutoffs.physical ha 1) (extendedGeometricNormal T Q F col z ha) j =
      fun p ↦ physicalGeometryComponent T Q F col z ha j (p.2, p.1) := by
  funext p
  simp only [carrierChartGeometryComponent, physicalGeometryComponent,
    CanonicalCarrier.reducedCovector_data]
  rfl

/-- Both compact geometric extensions are globally smooth. The support
condition is fixed geometry: `chartBump_tsupport_subset` reduces it to the
supported chart of radius `24a`, which the parent's fixed caps place inside
`X × V`. No global smoothness of an uncut coefficient is assumed (`bg-adjoint`). -/
theorem extendedGeometricNormal_and_component_contDiff {c C : ℝ} (hP : P.IsValid c C)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) (col : Fin n)
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)))
    (z : Euclidean 3) {ρ a : ℝ} (ha : 0 < a)
    (hcoef : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (closedBall ((0 : Euclidean n), z) ρ))
    (hsupp : tsupport (chartBump z ha) ⊆ X ×ˢ V)
    (hnull : ∀ w ∈ closedBall ((0 : Euclidean n), z) ρ,
      ContDiffAt ℝ ∞ (carrierNullvector T Q col) w) :
    ContDiff ℝ ∞ (extendedGeometricNormal T Q F col z ha) ∧
      ∀ j, ContDiff ℝ ∞ (physicalGeometryComponent T Q F col z ha j) := by
  have hg := geometricNormal_contDiffOn T Q hP hF hi hrank col hX hV hXU hc hcoef hnull
  have he : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      extendedGeometricNormal T Q F col z ha (p.2, p.1)) := by
    change ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      chartBump z ha p • geometricNormal T Q F col (p.2, p.1))
    exact Localization.contDiff_of_contDiffOn_support_neighborhood (hX.prod hV)
      ((chartBump z ha).contDiff.contDiffOn.smul hg)
      ((tsupport_smul_subset_left _ _).trans hsupp)
  have hswap : ContDiff ℝ ∞ (Prod.swap : CarrierParameter × Euclidean n →
      Euclidean n × CarrierParameter) := contDiff_snd.prodMk contDiff_fst
  have hν : ContDiff ℝ ∞ (extendedGeometricNormal T Q F col z ha) := by
    have hh := he.comp hswap
    simpa only [Function.comp_def, Prod.swap, Prod.mk.eta] using hh
  refine ⟨hν, fun j ↦ ?_⟩
  have hq := (CanonicalCarrier.quadratic_canonical_smooth T hP Q).mono
    (show X ×ˢ V ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) from
      fun p hp ↦ ⟨⟨hXU hp.1, (hc hp).1⟩, (hc hp).2⟩)
  have hqj := contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn hq) j
  apply Localization.contDiff_of_contDiffOn_support_neighborhood (hX.prod hV)
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((((FixedCutoffs.physical ha 1).contDiff.comp contDiff_fst).contDiffOn.mul
        (he.norm_sq ℝ).contDiffOn).mul hqj)
  · exact (physicalGeometryComponent_tsupport_subset T Q F col z ha j).trans hsupp

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
