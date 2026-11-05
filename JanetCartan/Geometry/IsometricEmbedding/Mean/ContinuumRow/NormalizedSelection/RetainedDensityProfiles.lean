module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.FootpointProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCoefficientProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.DensityCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.SourceCoefficients

/-!
# Actual retained coefficient profiles in the original density class

The uniform unit and inverse-label profiles apply to the same seed chart and
every contracted chart with its original minor and flow cylinder. The seed
forward estimate retains the original initial scalar ball. This instantiates
the normalized carrier coefficient producer for `σ * sqrt (1 + v)`, keeping
one high density norm and the original low order `μ+14`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open PositiveReference.FlowConstruction RetainedLeading RetainedRowGeometry
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open ContinuumNormalReduction.TransportSymbol NormalizedCarrierProfiles

/-- Uniform coefficient bounds for the actual retained positive-density
carrier, with one high norm of the original density and exactly its original
`μ+14` low hypothesis. The seed's forward bound and the geometric label buffer
keep the entire coefficient chart in the original initial ball. All scalar
transport, source matching and inverse-label bounds are proved from those
retained charts; no varying-flow or carrier bound is a premise.

The constants precede `σ`, the actual contracted chart and the initial
density. Consumers: the full reflected amplitude's low and high budgets in
`app:ch_background:eq:bg-mixed-input`, `app:ch_background:eq:bg-commutator`
and `app:ch_background:prop:bg-normalized`. -/
theorem exists_retained_chart_source_density_profiles
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc Bflow τ L Mc : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hΩpatch : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 seed.forward ≤ Mc)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U) (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hlabel : ∀ p ∈ D.field.region, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region) :
    ∃ M > (0 : ℝ), ∃ B : ℕ → ℝ, (∀ p, 1 ≤ B p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      ∀ current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc Bflow τ row col (sourceDilation F σ),
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) v ≤ 1 →
      let d := TransportKernel.coefficientsOfCarrier
        (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
          (fun q ↦ positiveDensityAmplitude σ (v q)) hr hcell angular high)
        (FixedCutoffs.physical hr 1)
      (∀ p, D.Controls p M (B p)
        (1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) p v) d) ∧
      D.Controls (2 * (n + 1) + 1) M (2 * B (2 * (n + 1) + 1)) 1 d := by
  have hcoordinates := hflow.mono_right (outputCylinder_spec hRc hτ).2
  obtain ⟨hY, _, hzero, hparam, _⟩ :=
    exists_retained_chart_source_primitive_convergence_on_outputCylinder hP T
      hΩ hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
      hR hRT hRU hV hVP hflow D (D.field.ball_subset.trans hD) r hr hcell angular high
  obtain ⟨H, _, hfootbounds⟩ := exists_matched_source_densityFootpoint_all_order_profiles
    T seed.inverse hR hV hY hzero hparam D.field hD
  obtain ⟨M₀, hM₀, B₀, hB₀, hunit⟩ := exists_retained_chart_source_coefficient_profiles hP T
    hΩ hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hR hRT hRU hV hVP hcoordinates D hD hr hcell angular high ha hh
  obtain ⟨M, hM, B, hB, hweight⟩ := exists_density_weighted_coefficient_controls
    (N := N) T D ((0 : Euclidean (n - 1)), zCell) hL H hM₀.le B₀ hB₀
  refine ⟨M, hM, B, hB, ?_⟩
  intro σ hσ current v hv hpos hinterval hvnorm d
  have hσ1 : σ ≤ 1 := by linarith [hσ.2]
  have hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro w hw
    exact ⟨(hΩpatch hw).1.2,
      fun i ↦ ((hΩpatch hw).2 i).le.trans (by linarith [hP.1])⟩
  obtain ⟨_, hfoot, _, _, _⟩ := retained_charts_source_dilation T hΩ hKΩ hpatch
    hRc hτ hτR hbuffer hF hrank hphysical seed htrans hflat hσ.1 hσ1 current
  have hmatch : EqOn (densityFootpoint T current.inverse)
      (densityFootpoint T (NormalizedBackground.SourceGeometry.sourceTransportFlow seed.inverse σ))
      D.field.region := fun _ hp ↦ hfoot (current.small_subset (hcoordinates (hD hp)))
  obtain ⟨hfootSmooth, hfootBound⟩ := hfootbounds σ hσ current.inverse hmatch
  have hrange : MapsTo (densityFootpoint T current.inverse) D.field.region
      (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
    intro p hp
    rw [hmatch hp]
    apply sourceDensityFootpoint_mem_original_ball_of_forward_cNorm T hL hRc hτ hMc
      seed hforward (hflow (hD hp)) (hlabel p hp) _ hσ.1 hσ1
    change |(adaptedCoordinates T.data.adapted p.1).1| < L / (64 * Mc)
    rw [adaptedCoordinates_apply]
    have ht := abs_real_inner_le_norm T.data.adapted.normal p.1
    rw [T.data.adapted.normal_unit, one_mul] at ht
    exact (ht.trans_lt (mem_ball_zero_iff.mp (hD hp).1)).trans_le hRtime
  let e := TransportKernel.coefficientsOfCarrier
    (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
      (fun _ ↦ σ) hr hcell angular high) (FixedCutoffs.physical hr 1)
  have hprofiles := hweight e (hunit σ ⟨hσ.1, hσ1⟩ current) current.inverse hfootSmooth
    (hrange.mono_right (ball_subset_ball (by linarith : L / 16 ≤ L / 4)))
    ((hrange.mono_left D.field.ball_subset).mono_right
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : L / 16 ≤ L / 8))))
    hfootBound v hv hpos hinterval hvnorm
  have hd : d = {e with
      normal := fun p ↦ Real.sqrt (1 + v (densityFootpoint T current.inverse p)) • e.normal p} :=
    coefficientsOfCarrier_initial_mul T current.Q (sourceDilation F σ) row col
      current.forward current.inverse (fun _ ↦ σ) (fun q ↦ Real.sqrt (1 + v q))
      hr hcell angular high
  rw [hd]
  exact hprofiles

end JanetCartan.ContinuumRow.NormalizedSelection
