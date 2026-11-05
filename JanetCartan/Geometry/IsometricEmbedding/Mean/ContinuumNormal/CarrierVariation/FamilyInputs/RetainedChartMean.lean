module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.Bounds

/-!
# The mean of the same retained source charts

The finite charts below are supplied by
`FamilyInputs.exists_initialized_retained_source_charts`. Their unit scalars,
selected columns, positive-scale scalars and ODE maps are kept literally.
The weights, measures and compact carrier supports are unchanged.

The relative inputs `hflow₀` and `hflowσ` are exact product-domain inclusions.
Their producer is the retained chart/row geometry; the parent `FamilyInputs`
simultaneous source/row/mean assembly must instantiate them on its original
supports, including the open spatial neighborhood needed for `cNorm`.
This deduction does not wait for that geometric construction and does not
assert the wider-density comparison or unconditional normal coercivity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase

/-- Construct the normalized mean of the supplied retained scalar family.
The actual current normals and means agree with the seed pullbacks; the
constant limit is positive semidefinite, every finite-order mean error is
`O(σ)`, and the actual normals have a uniform positive lower bound on the
original supports. Smoothness and nonvanishing follow from the retained
scalar/Hamilton facts and the flat reference stress basis, not extra analytic
premises (`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-Hsigma`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_current_mean_bounds
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (hUG : U ⊆ G.domain.chart n)
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    {T : (a : A) → PatchQuantitativeFamily (P a) U hU}
    {Ω : A → Set (Euclidean n × Euclidean 3)}
    (hΩ : ∀ a, IsOpen (Ω a))
    {z₀ : A → Euclidean 3} {ρ Rc M τ : A → ℝ} {row col : A → Fin n}
    (hKΩ : ∀ a, closedBall ((0 : Euclidean n), z₀ a) (ρ a) ⊆ Ω a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    (hRc : ∀ a, 0 < Rc a) (hτ : ∀ a, 0 < τ a) (hτR : ∀ a, τ a ≤ Rc a / 16)
    (hbuffer : ∀ a, MapsTo (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a))
      (closedBall ((0 : Euclidean n), z₀ a) (ρ a)))
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (c₀ : (a : A) → Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
      ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (htrans : ∀ a, ∀ q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (c₀ a).Q.1 (c₀ a).Q.2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) (hcap1 : cap ≤ 1)
    (cσ : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (a : A) →
      Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
        ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a)
        (sourceDilation G.map σ))
    {U₀ D W : Set (Euclidean n)} (hU₀ : IsOpen U₀) (h0 : (0 : Euclidean n) ∈ U₀)
    (hU₀G : U₀ ⊆ G.domain.chart n) (hD : IsCompact D) (hW : IsOpen W) (hDW : D ⊆ W)
    (μ : A → Measure CarrierParameter) (K V : A → Set CarrierParameter)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (hflow₀ : ∀ a, MapsTo (densityCoordinates (T a)) (U₀ ×ˢ V a) (c₀ a).D)
    (hflowσ : ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) a,
      MapsTo (densityCoordinates (T a)) (W ×ˢ K a) (cσ σ hσ a).D)
    (w : A → CarrierParameter → ℝ)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a)) (hwpos : ∀ a z, 0 ≤ w a z)
    (hsupp : ∀ a z, z ∉ K a → w a z = 0) :
    let ν := fun a ↦ (c₀ a).normal (fun _ ↦ 1)
    let ξ := fun a ↦ covector (c₀ a)
    let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ carrierMean μ w
      (fun a ↦ (cσ σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (cσ σ hσ a))
    let H₀ := carrierMean μ w ν ξ 0
    let J := fun a q ↦ (normalizedPullback (unitAmplitude (c₀ a)) q,
      normalizedPullback (ξ a) q, normalizedPullback (ν a) q)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ cap ∧
      (∀ a, ContDiffOn ℝ ∞ (J a) (Ioo (-2 * σ₀) (2 * σ₀) ×ˢ B ×ˢ V a)) ∧
      H₀.PosSemidef ∧
      (∀ x, normalizedCarrierMean μ w ν ξ 0 x = H₀) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) a x, x ∈ B → ∀ z ∈ K a,
        (cσ σ hσ a).normal (fun _ ↦ σ) (x, z) = normalizedPullback (ν a) (σ, (x, z)) ∧
        covector (cσ σ hσ a) (x, z) = normalizedPullback (ξ a) (σ, (x, z))) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) x, x ∈ B →
        H σ hσ x = normalizedCarrierMean μ w ν ξ σ x ∧
        H σ hσ x = carrierMean μ w ν ξ (σ • x)) ∧
      (∃ c > 0, ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ →
        ∀ a x, x ∈ D → ∀ z ∈ K a, c ≤ ‖(cσ σ hσ a).normal (fun _ ↦ σ) (x, z)‖) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ →
        cNorm D s (fun x ↦ H σ hσ x - H₀) ≤ C * σ ∧
        ∀ a x, x ∈ D → ∀ z ∈ K a, ‖iteratedFDeriv ℝ s (J a) (σ, (x, z))‖ ≤ C := by
  classical
  let ν := fun a ↦ (c₀ a).normal (fun _ ↦ 1)
  let ξ := fun a ↦ covector (c₀ a)
  let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ carrierMean μ w
    (fun a ↦ (cσ σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (cσ σ hσ a))
  have hpatch₀ (a : A) : MapsTo
      (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (U₀ ×ˢ V a) (ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius)) := by
    intro p hp
    apply hpatch a
    have hh := (c₀ a).domain_coefficients (hflow₀ a hp)
    change (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (coordinates (adaptedCoordinates (T a).data.adapted) (p.1, parameter p.2)) ∈ Ω a at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  obtain ⟨B₁, hB₁, hDB₁, r, hr, _hr1, _hseg, hJ, hlo, hpos, hzero, _hres, hbound⟩ :=
    exists_normalized_mean_bounds hn G hP c₀ hτ hU₀ h0 hU₀G hD μ K V hV hK hKV
      hflow₀ hpatch₀ w hw hwpos hsupp
  let B := B₁ ∩ W
  let σ₀ := min r cap
  have hB : IsOpen B := hB₁.inter hW
  have hDB : D ⊆ B := fun _ hx ↦ ⟨hDB₁ hx, hDW hx⟩
  have hσ₀ : 0 < σ₀ := lt_min hr hcap
  have hσ₀r : σ₀ ≤ r := min_le_left _ _
  have hσ₀cap : σ₀ ≤ cap := min_le_right _ _
  have hfields (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (a : A) :
      EqOn ((cσ σ hσ a).normal (fun _ ↦ σ))
        (fun p ↦ normalizedPullback (ν a) (σ, p)) (W ×ˢ K a) ∧
      EqOn (covector (cσ σ hσ a))
        (fun p ↦ normalizedPullback (ξ a) (σ, p)) (W ×ˢ K a) := by
    have hp : Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterCube (2 * (P a).radius) :=
      fun p hp ↦ ⟨(hpatch a hp).1, fun j ↦ ((hpatch a hp).2 j).le⟩
    have hh := current_fields_eq_normalized (hΩ a) (hKΩ a) hp (hRc a) (hτ a) (hτR a)
      (hbuffer a) G.contDiff (fun x hx ↦ G.fullNormalRank x (hUG hx))
      (hphysical a) (c₀ a) (htrans a) (fun x _ ↦ G.inducedMetric_eq_one x)
      hσ.1 (hσ.2.trans hcap1) (cσ σ hσ a)
    exact ⟨hh.1.mono (hflowσ σ hσ a), hh.2.mono (hflowσ σ hσ a)⟩
  have hmean (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (x : Euclidean n) (hx : x ∈ W) :
      H σ hσ x = normalizedCarrierMean μ w ν ξ σ x := by
    simp only [H, normalizedCarrierMean, carrierMean]
    apply Finset.sum_congr rfl
    intro a _
    ext i j
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    by_cases hz : z ∈ K a
    · rw [(hfields σ hσ a).1 (show (x, z) ∈ W ×ˢ K a from ⟨hx, hz⟩),
        (hfields σ hσ a).2 (show (x, z) ∈ W ×ˢ K a from ⟨hx, hz⟩)]
    · simp only [hsupp a z hz, zero_mul]
  refine ⟨B, hB, hDB, σ₀, hσ₀, hσ₀cap, ?_, hpos, hzero, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hJ a).mono (fun q hq ↦
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2.1.1, hq.2.2⟩)
  · intro σ hσ a x hx z hz
    exact ⟨(hfields σ hσ a).1 ⟨hx.2, hz⟩, (hfields σ hσ a).2 ⟨hx.2, hz⟩⟩
  · intro σ hσ x hx
    exact ⟨hmean σ hσ x hx.2, hmean σ hσ x hx.2⟩
  · obtain ⟨c, hc, hlo⟩ := hlo
    refine ⟨c, hc, ?_⟩
    intro σ hσ hσle a x hx z hz
    rw [(hfields σ hσ a).1 ⟨hDW hx, hz⟩]
    exact hlo a σ ⟨hσ.1.le, hσle.trans hσ₀r⟩ x hx z hz
  · intro s
    obtain ⟨C, hC, hbound⟩ := hbound s
    refine ⟨C, hC, ?_⟩
    intro σ hσ hσle
    have he : cNorm D s (fun x ↦ H σ hσ x - carrierMean μ w ν ξ 0) =
        cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ σ x - carrierMean μ w ν ξ 0) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hW.mem_nhds (hDW hx)] with y hy
      rw [hmean σ hσ y hy]
    rw [he]
    exact hbound σ ⟨hσ.1.le, hσle.trans hσ₀r⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
