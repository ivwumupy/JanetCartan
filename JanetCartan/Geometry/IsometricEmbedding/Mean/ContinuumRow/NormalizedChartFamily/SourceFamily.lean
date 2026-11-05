module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.CarrierConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.SourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.SeedAdmission
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.SeedPullback

/-!
# Source charts from the original supplied seed coefficients

A single cap admits the actual source frame to the retained Hamilton family
and the parent's conic thresholds. Exact seed pullbacks construct every chart
coefficient, preserving the original low bound and existence time. The actual
ODE charts retain their literal lifts; uniqueness identifies their maps and
scalars with the supplied seed. No new minor or conic geometry is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference.FlowConstruction

/-- Construct the actual normalized chart family from the supplied seeds,
retaining each original `B`, `Rc`, time, minor and coefficient domain. All
current coefficient fields and the sharp direction bound follow from the
literal source pullbacks. The geometric domain-invariance premise holds for
the retained product coefficient domains, as proved by
`retained_coefficient_domain_mapsTo_source_contraction`.

The cap precedes every source scale and chart choice and also admits the
parent's arbitrary positive `δgeometry` on its unchanged conic geometry.
ODE uniqueness proves the seed/source flow and scalar identities. Consumers:
the finite retained baseline, normalized carrier profiles and normalized flow
profiles (`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-T`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_finite_source_charts_with_lifts
    {n : ℕ} {ι : Type*} [Fintype ι] (H : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUG : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {P : ι → Patch n} (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (Ω : ι → Set (Euclidean n × Euclidean 3)) (hΩ : ∀ i, IsOpen (Ω i))
    (zCell : ι → Euclidean 3) (ρc Rc B τlead δgeometry : ι → ℝ)
    (row col : ι → Fin n)
    (hRc : ∀ i, 0 < Rc i) (hB : ∀ i, 0 ≤ B i)
    (hδgeometry : ∀ i, 0 < δgeometry i)
    (hτeq : ∀ i, τlead i = existenceTime (Rc i) (liftedLowBound (T i) (B i)) / 4)
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρc i) ⊆ Ω i)
    (hpatch : ∀ i, Ω i ⊆ ball 0 (T i).physicalRadius ×ˢ parameterCube (2 * (P i).radius))
    (hΩU : ∀ i w, w ∈ Ω i → w.1 ∈ U)
    (hΩscale : ∀ i σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ω i) (Ω i))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρc i)))
    (seed : (i : ι) → Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i) H.map)
    (htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (seed i).Q.1 (seed i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧
      ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (i : ι) →
        Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
          ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
          (sourceDilation H.map σ),
      ∀ σ hσ i,
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        ODE.IsSmoothFlowOn (liftedDirection (T i) (current σ hσ i).Q (row i) (col i))
          (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i) (Rc i / 2)
          (existenceTime (Rc i) (liftedLowBound (T i) (B i))) Ψ ∧
        (current σ hσ i).forward = forwardFromLift Ψ ∧
        (current σ hσ i).inverse = footpointFromLift Ψ ∧
        IsImmersionOn (sourceDilation H.map σ) U ∧
        HasFullNormalRankOn (sourceDilation H.map σ) U ∧
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          ((current σ hσ i).Q.1 - fun _ ↦ cubeStress n) < δgeometry i ∧
        EqOn (current σ hσ i).forward (sourceTransportFlow (seed i).forward σ)
          (Ioo (-τlead i) (τlead i) ×ˢ
            ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) ∧
        EqOn (current σ hσ i).inverse (sourceTransportFlow (seed i).inverse σ)
          (current σ hσ i).D ∧
        EqOn ((current σ hσ i).scalar (fun _ ↦ σ))
          (sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        EqOn (fun w ↦ (current σ hσ i).scalar (fun _ ↦ σ) w •
            carrierNullvector (T i) (current σ hσ i).Q (col i) w)
          (sourceAmplitude (fun w ↦ (seed i).scalar (fun _ ↦ 1) w •
            carrierNullvector (T i) (seed i).Q (col i) w) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
          EqOn ((current σ hσ i).scalar (fun q ↦ σ * weight q))
            (fun w ↦ sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ w *
              weight ((current σ hσ i).inverse (coordinates (adaptedCoordinates (T i).data.adapted) w)))
            ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) := by
  classical
  obtain ⟨e, he, hesmall⟩ := Pi.exists_forall_pos_add_lt
    (fun i ↦ lt_min (T i).family.threshold_pos (hδgeometry i))
  have hemargin (i : ι) : e < (T i).family.threshold ∧ e < δgeometry i := by
    simpa only [zero_add, lt_min_iff] using hesmall i
  obtain ⟨cap, hcap, hcap1, hadmit⟩ :=
    SourceMatching.exists_joint_stress_scale_interval H hbounded he
  have hτ (i : ι) : 0 < τlead i := by
    rw [hτeq i]
    exact div_pos (existenceTime_pos (hRc i) (liftedLowBound_nonneg (T i) (hB i))) (by norm_num)
  have hτR (i : ι) : τlead i ≤ Rc i / 16 := by
    have hh := (existenceTime_le (hRc i) (liftedLowBound_nonneg (T i) (hB i))).1
    rw [hτeq i]
    linarith
  have hseedrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUG hx)
  have hlocal (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (i : ι) :
      ∃ current : Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ),
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        ODE.IsSmoothFlowOn (liftedDirection (T i) current.Q (row i) (col i))
          (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i) (Rc i / 2)
          (existenceTime (Rc i) (liftedLowBound (T i) (B i))) Ψ ∧
        current.forward = forwardFromLift Ψ ∧ current.inverse = footpointFromLift Ψ ∧
        IsImmersionOn (sourceDilation H.map σ) U ∧
        HasFullNormalRankOn (sourceDilation H.map σ) U ∧
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (current.Q.1 - fun _ ↦ cubeStress n) < δgeometry i ∧
        EqOn current.forward (sourceTransportFlow (seed i).forward σ)
          (Ioo (-τlead i) (τlead i) ×ˢ
            ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) ∧
        EqOn current.inverse (sourceTransportFlow (seed i).inverse σ) current.D ∧
        EqOn (current.scalar (fun _ ↦ σ)) (sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' current.D) ∧
        EqOn (fun w ↦ current.scalar (fun _ ↦ σ) w • carrierNullvector (T i) current.Q (col i) w)
          (sourceAmplitude (fun w ↦ (seed i).scalar (fun _ ↦ 1) w •
            carrierNullvector (T i) (seed i).Q (col i) w) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' current.D) ∧
        ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
          EqOn (current.scalar (fun q ↦ σ * weight q))
            (fun w ↦ sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ w *
              weight (current.inverse (coordinates (adaptedCoordinates (T i).data.adapted) w)))
            ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' current.D) := by
    have hσ1 : σ ≤ 1 := hσ.2.trans hcap1
    obtain ⟨hi, hrank, hframe, hsmall⟩ := hadmit σ hσ.1 hσ.2
    have hsmallCell : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < e := by
      apply (cNorm_mono_set_of_contDiffAt ((hphysical i).trans subset_closure)
        hbounded.isCompact_closure ?_).trans_lt hsmall
      exact fun x hx ↦ ((hframe x hx).sub contDiffAt_const).of_le (by simp)
    let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold} :=
      ⟨projectedStress (sourceDilation H.map σ),
        fun x hx ↦ (hframe x (subset_closure hx)).contDiffWithinAt,
        hsmallCell.trans (hemargin i).1⟩
    obtain ⟨current, Ψ, _, hΨ, hf, hy⟩ := exists_source_chart_with_lift_from_seed (T i)
      (hΩ i) (hKΩ i) (hpatch i) (hΩU i) (hRc i) (hB i) (hτeq i) (hbuffer i)
      H.contDiff hseedrank (hphysical i) (fun x _ ↦ H.inducedMetric_eq_one x)
      (seed i) (htrans i) hσ.1 hσ1 (hΩscale i σ ⟨hσ.1, hσ1⟩) Q rfl
    have hgeom : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (current.Q.1 - fun _ ↦ cubeStress n) < δgeometry i := by
      rw [current.frame_eq]
      exact hsmallCell.trans (hemargin i).2
    obtain ⟨hforward, hinverse, hscalar, hnullscale, _⟩ := RetainedLeading.retained_charts_source_dilation
      (T i) (hΩ i) (hKΩ i) (hpatch i) (hRc i) (hτ i) (hτR i) (hbuffer i)
      H.contDiff hseedrank (hphysical i) (seed i) (htrans i)
      (fun x _ ↦ H.inducedMetric_eq_one x) hσ.1 hσ1 current
    refine ⟨current, Ψ, hΨ, hf, hy, hi, hrank, hgeom, hforward, hinverse, hscalar, hnullscale, ?_⟩
    intro weight w hw
    change current.scalar (fun q ↦ σ * weight q) w =
      sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ w *
        weight (current.inverse (coordinates (adaptedCoordinates (T i).data.adapted) w))
    rw [← hscalar hw]
    simp only [Chart.scalar, carrierScalarAmplitude, transportFromFootpoint,
      characteristicTransport, scalarTransport]
    ring
  choose current hcurrent using hlocal
  exact ⟨cap, hcap, hcap1, current, hcurrent⟩

end JanetCartan.ContinuumRow.NormalizedChartFamily
