module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.WeightSelection
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.FixedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.NormalizedMeanSource

/-!
# The fixed source on the retained row's original external weights

Apply the retained mean-source construction with the original squared weights,
product Lebesgue measure and smallest fixed physical cutoff. The full external
weight supports, including their collars, lie in the supplied common cells.
The fixed buffer is the output of `WeightSelection` at the original selection
point, or `WeightBuffers` when the external weights have already been selected.

The result supplies the geometric smoothness and source bound required by
`SourceInverse.exists_small_uncorrectedDensity_of_normal_estimates`. The
uniform normal gap and primitive inverse/raw-adjoint estimates on these SAME
cutoffs are still required; no such analytic estimate is a premise here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ProjectedStressFrame UniformStep.Periodization

/-- The zero-density physical mean of the literal retained row is the mean
used in `RetainedAssembly.NormalizedMeanSource`, with exactly the same
external weights and Lebesgue measure. This is a definitional identification
of fields, not an identification of independent choices
(`app:ch_background:eq:bg-affine-mean`, `app:ch_background:eq:bg-Hsigma`). -/
theorem physicalDensityMean_retainedChart_zero
    {n N : ℕ} {A : Type} [Fintype A]
    {P : A → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : (a : A) → PatchQuantitativeFamily (P a) U hU}
    {Ω K : A → Set (Euclidean n × Euclidean 3)}
    {p₀ : A → Euclidean (n - 1) × Euclidean 3}
    {Rc M τ : A → ℝ} {row col : A → Fin n} {F : Euclidean n → Euclidean N}
    (c : (a : A) → Chart (T a) (Ω a) (K a) (p₀ a)
      (Rc a) (M a) (τ a) (row a) (col a) F)
    (initial : A → Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : A → CarrierParameter → ℝ) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : A → CarrierParameter → Euclidean (n - 1) → ℝ) (high : A → ℝ → ℝ) :
    physicalDensityMean (fun a ↦ data (T a) (c a).Q F (row a) (col a)
      (c a).forward (c a).inverse (initial a) hr hcell (angular a) (high a)) χ 0 =
      carrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
        (fun a ↦ (c a).normal (initial a)) (fun a ↦ covector (c a)) := by
  rw [physicalDensityMean_zero]
  rfl

/-- The original scalar formula and canonical completion give local
smoothness of the retained normal on the full weight buffer
(`app:ch_background:eq:bg-current-raising`, `app:ch_waves:thm:leading`). -/
theorem retained_chart_normal_contDiffOn
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω K p₀ Rc M τ row col F) {cP CP : ℝ} (hP : P.IsValid cP CP)
    (hτ : 0 < τ)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    {W : Set (Euclidean n)} {V : Set CarrierParameter} (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    (hrank : HasFullNormalRankOn F W)
    (hflow : MapsTo (densityCoordinates T) (W ×ˢ V) c.D)
    {σ : ℝ} (hσ : 0 < σ) :
    ContDiffOn ℝ ∞ (c.normal (fun _ ↦ σ)) (W ×ˢ V) ∧
      ContDiffOn ℝ ∞ (covector c) (W ×ˢ V) := by
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hψΩ : MapsTo ψ (W ×ˢ V) Ω := by
    intro p hp
    have hh := c.domain_coefficients (hflow hp)
    change (coordinates (adaptedCoordinates T.data.adapted)).symm
      (coordinates (adaptedCoordinates T.data.adapted) (ψ p)) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  have hξ : ContDiffOn ℝ ∞ (covector c) (W ×ˢ V) :=
    (T.carrierGradient_smooth hP c.Q).comp hψ.contDiffOn
      (fun p hp ↦ hpatch (hψΩ hp))
  have hα := (c.scalar_spec hτ (fun _ ↦ σ) contDiffOn_const (fun _ _ ↦ hσ)).1.comp
    hψ.contDiffOn hflow
  have hnull := c.null_smooth.comp hψ.contDiffOn hψΩ
  exact ⟨contDiffOn_canonicalPrincipalNormal hW hF himm hrank
    (fun _ hp ↦ hp.1) hξ (hα.smul hnull), hξ⟩

/-- Instantiate the normalized mean-source theorem on the SAME retained
charts with `μ = volume.prod volume`, `w = χ²`, the full supports of the
original external weights, and the smallest fixed physical cutoff. The
supplied product buffer is constructed before source contraction by
`exists_retained_external_weights_and_measurement_buffer`; the cell maps are
the retained chart compatibility conclusions. Local source smoothness is
proved from the actual chart scalar and canonical normal, and the all-order
bound is for the literal `fixedSourceToL2` used by the uncorrected inverse.
The same interval also gives a positive normal lower bound and mixed bounds
for the normalized seed amplitude, covector and normal on the entire support
(`app:ch_background:eq:bg-current-raising`, `app:ch_background:eq:bg-positive-profile`).

No inverse, mean-error bound or uniform gap is an input. Instantiating the
analytic row estimates and then fixing the corrected positive inverse remain
separate obligations of the positive-background construction. -/
theorem exists_retained_fixedSource_sobolev_bounds
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (hUG : U ⊆ G.domain.chart n)
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    {T : (a : A) → PatchQuantitativeFamily (P a) U hU}
    {Ω : A → Set (Euclidean n × Euclidean 3)} (hΩ : ∀ a, IsOpen (Ω a))
    {z₀ : A → Euclidean 3} {ρ Rc M τ : A → ℝ} {row col : A → Fin n}
    (hKΩ : ∀ a, closedBall ((0 : Euclidean n), z₀ a) (ρ a) ⊆ Ω a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    (hRc : ∀ a, 0 < Rc a) (hτ : ∀ a, 0 < τ a) (hτR : ∀ a, τ a ≤ Rc a / 16)
    (hbuffer : ∀ a, MapsTo (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a))
      (closedBall ((0 : Euclidean n), z₀ a) (ρ a)))
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (χ : A → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχcompact : ∀ a, HasCompactSupport (χ a))
    (E : A → Set (Euclidean n × CarrierParameter))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hball : closedBall (0 : Euclidean n) (6 * r) ⊆ U)
    (V : A → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hproduct : ∀ a, closedBall (0 : Euclidean n) (6 * r) ×ˢ V a ⊆ E a)
    (c₀ : (a : A) → Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
      ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (hseed : ∀ a, MapsTo (densityCoordinates (T a)) (E a) (c₀ a).D)
    (htrans : ∀ a, ∀ q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (c₀ a).Q.1 (c₀ a).Q.2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) (hcap1 : cap ≤ 1)
    (cσ : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (a : A) →
      Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
        ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a)
        (sourceDilation G.map σ))
    (hcurrent : ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) a,
      MapsTo (densityCoordinates (T a)) (E a) (cσ σ hσ a).D) :
    let μ : A → Measure CarrierParameter := fun _ ↦ volume.prod volume
    let w := fun a z ↦ χ a z ^ 2
    let H₀ := carrierMean μ w (fun a ↦ (c₀ a).normal (fun _ ↦ 1))
      (fun a ↦ covector (c₀ a)) 0
    let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ carrierMean μ w
      (fun a ↦ (cσ σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (cσ σ hσ a))
    let J := fun a q ↦ (normalizedPullback (unitAmplitude (c₀ a)) q,
      normalizedPullback (covector (c₀ a)) q,
      normalizedPullback ((c₀ a).normal (fun _ ↦ 1)) q)
    let Q := fun σ ↦ projectedStress (sourceDilation G.map σ)
    let R := fun σ hσ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ hσ)
    H₀.PosSemidef ∧
      ∃ hQ : ∀ σ ∈ Ioc (0 : ℝ) cap, ContDiffOn ℝ ∞ (Q σ) (ball 0 (4 * r)),
      ∃ hR : ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), ContDiffOn ℝ ∞ (R σ hσ) (ball 0 (4 * r)),
      ∃ σ₀ > (0 : ℝ), σ₀ ≤ cap ∧ ∃ cNormal > (0 : ℝ),
      ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
        (∀ a, ContDiffOn ℝ ∞ (J a)
          (Ioo (-2 * σ₀) (2 * σ₀) ×ˢ ball 0 (4 * r) ×ˢ V a)) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ s,
          (periodicSobolevScale n (Euclidean n)).gradeNorm s
            (fixedSourceToL2 hr hcell (Q σ) (R σ hσ) (hQ σ hσ) (hR σ hσ)) ≤ C s * σ ∧
          cNorm (closedBall 0 (4 * r)) s (fun x ↦ H σ hσ x - H₀) ≤ C s * σ ∧
          ∀ a x, x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
            ‖iteratedFDeriv ℝ s (J a) (σ, (x, z))‖ ≤ C s) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ a x,
          x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
            cNormal ≤ ‖(cσ σ hσ a).normal (fun _ ↦ σ) (x, z)‖) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) a x, x ∈ closedBall 0 (4 * r) →
          ∀ z ∈ tsupport (χ a),
            (cσ σ hσ a).normal (fun _ ↦ σ) (x, z) =
              normalizedPullback ((c₀ a).normal (fun _ ↦ 1)) (σ, (x, z)) ∧
            covector (cσ σ hσ a) (x, z) = normalizedPullback (covector (c₀ a)) (σ, (x, z))) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), EqOn (R σ hσ)
          (fun x ↦ H σ hσ x - H₀) (ball 0 (5 * r))) := by
  classical
  dsimp only
  let μ : A → Measure CarrierParameter := fun _ ↦ volume.prod volume
  let w := fun a z ↦ χ a z ^ 2
  let K := fun a ↦ tsupport (χ a)
  let W := ball (0 : Euclidean n) (5 * r)
  let ν := fun a ↦ (c₀ a).normal (fun _ ↦ 1)
  let ξ := fun a ↦ covector (c₀ a)
  let H₀ := carrierMean μ w ν ξ 0
  let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ carrierMean μ w
    (fun a ↦ (cσ σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (cσ σ hσ a))
  let Q := fun σ ↦ projectedStress (sourceDilation G.map σ)
  let R := fun σ hσ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ hσ)
  let (a : A) : IsFiniteMeasure ((μ a).restrict (K a)) :=
    ⟨by simpa [μ, K] using (hχcompact a).measure_lt_top (μ := volume.prod volume)⟩
  have hW6 : W ⊆ closedBall (0 : Euclidean n) (6 * r) :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
  have hWU : W ⊆ U := hW6.trans hball
  have h0W : (0 : Euclidean n) ∈ W := mem_ball_self (by positivity)
  have hflow₀ (a : A) : MapsTo (densityCoordinates (T a)) (W ×ˢ V a) (c₀ a).D :=
    (hseed a).mono_left ((prod_mono hW6 Subset.rfl).trans (hproduct a))
  have hflowσ (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (a : A) :
      MapsTo (densityCoordinates (T a)) (W ×ˢ V a) (cσ σ hσ a).D :=
    (hcurrent σ hσ a).mono_left ((prod_mono hW6 Subset.rfl).trans (hproduct a))
  have hw (a : A) : ContDiffOn ℝ ∞ (w a) (V a) := ((hχ a).pow 2).contDiffOn
  have hsupp (a : A) (z) (hz : z ∉ K a) : w a z = 0 := by
    simp only [w, image_eq_zero_of_notMem_tsupport hz, zero_pow (by decide : 2 ≠ 0)]
  have h4W : closedBall (0 : Euclidean n) (4 * r) ⊆ W :=
    closedBall_subset_ball (by linarith)
  obtain ⟨Bnormal, _hBnormal, hDBnormal, σnormal, hσnormal, _hσnormalCap,
    hJ, _hposNormal, _hzeroNormal, hfieldsNormal, _hmeanNormal,
    ⟨cNormal, hcNormal, hnormal⟩, hnormalBounds⟩ :=
    exists_current_mean_bounds hn G hUG hP hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical
      c₀ htrans hcap hcap1 cσ isOpen_ball h0W (hWU.trans hUG)
      (isCompact_closedBall 0 (4 * r)) isOpen_ball h4W
      μ K V hV hχcompact hχV hflow₀
      (fun σ hσ a ↦ (hflowσ σ hσ a).mono_left (prod_mono Subset.rfl (hχV a)))
      w hw (fun _ _ ↦ sq_nonneg _) hsupp
  obtain ⟨Bsource, _hB, _hDB, σsource, hσsource, hσsourceCap, hpos, _hzero, _hfields, _hmean,
    _hres, _heq, _hmeanBound, _hsmooth, hep, _hmem, hbound, _hjet⟩ :=
    RetainedAssembly.NormalizedMeanSource.exists_current_referenceSource_sobolev_bounds
      hn G hUG hP hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans hcap hcap1 cσ
      isOpen_ball h0W (hWU.trans hUG) (isCompact_closedBall 0 (4 * r)) isOpen_ball h4W
      μ K V hV hχcompact hχV hflow₀
      (fun σ hσ a ↦ (hflowσ σ hσ a).mono_left (prod_mono Subset.rfl (hχV a)))
      w hw (fun _ _ ↦ sq_nonneg _) hsupp (mul_pos (by norm_num) hr) hcell
      (FixedCutoffs.physical hr 0).contDiff (FixedCutoffs.physical_tsupport_four hr 0)
      (FixedCutoffs.physical_tsupport_four hr 0)
  have hflat (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (x : Euclidean n) :
      inducedMetric (sourceDilation G.map σ) x = 1 :=
    inducedMetric_sourceDilation_eq_one hσ.1 G.contDiff G.inducedMetric_eq_one x
  have himm (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      IsImmersionOn (sourceDilation G.map σ) W :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
      (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ hflat σ hσ x)
  have hrank (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      HasFullNormalRankOn (sourceDilation G.map σ) W := by
    apply (hasFullNormalRankOn_sourceDilation_iff hσ.1 G.contDiff W).mpr
    rintro _ ⟨x, hx, rfl⟩
    apply G.fullNormalRank _ (hUG (hWU ?_))
    have hx' : ‖x‖ < 5 * r := mem_ball_zero_iff.mp hx
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) (hσ.2.trans hcap1)).trans_lt hx'
  have hF (σ : ℝ) : ContDiffOn ℝ ∞ (sourceDilation G.map σ) W :=
    (contDiff_sourceDilation G.contDiff).contDiffOn
  have hQW (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞ (Q σ) W :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball (hF σ) (himm σ hσ) (hrank σ hσ))
  have hH (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞ (H σ hσ) W := by
    have hf (a : A) := retained_chart_normal_contDiffOn (cσ σ hσ a) (hP a) (hτ a)
      (hpatch a) isOpen_ball (hF σ) (himm σ hσ) (hrank σ hσ) (hflowσ σ hσ a) hσ.1
    exact contDiffOn_carrierMean_of_weight_support μ K V isOpen_ball hV hχcompact hχV
      w _ _ hw (fun a ↦ (hf a).1) (fun a ↦ (hf a).2) hsupp
  have hres (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      EqOn (R σ hσ) (fun x ↦ H σ hσ x - H₀) W :=
    referenceMeanResidual_eq_sub isOpen_ball (hF σ) (himm σ hσ)
      (fun x _ ↦ hflat σ hσ x) H₀ hpos.isHermitian.isSymm (H σ hσ)
  have hRW (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞ (R σ hσ) W :=
    ((hH σ hσ).sub contDiffOn_const).congr (fun x hx ↦ (hres σ hσ hx))
  have h4W' : ball (0 : Euclidean n) (4 * r) ⊆ W := ball_subset_ball (by linarith)
  let hQ := fun σ hσ ↦ (hQW σ hσ).mono h4W'
  let hR := fun σ hσ ↦ (hRW σ hσ).mono h4W'
  choose Csource hCsource hb using hbound
  choose Cnormal hCnormal hnb using hnormalBounds
  refine ⟨hpos, hQ, hR, min σsource σnormal, lt_min hσsource hσnormal,
    (min_le_left _ _).trans hσsourceCap, cNormal, hcNormal,
    (fun s ↦ max (Csource s) (Cnormal s)),
    (fun s ↦ (hCsource s).trans_le (le_max_left _ _)), ?_, ?_, ?_, ?_, hres⟩
  · intro a
    apply (hJ a).mono
    intro q hq
    exact ⟨⟨by linarith [hq.1.1, min_le_right σsource σnormal],
      by linarith [hq.1.2, min_le_right σsource σnormal]⟩,
      hDBnormal (ball_subset_closedBall hq.2.1), hq.2.2⟩
  · intro σ hσ hsmall s
    have hs := hb s σ hσ (hsmall.trans (min_le_left _ _))
    have hn' := hnb s σ hσ (hsmall.trans (min_le_right _ _))
    refine ⟨hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hσ.1.le),
      hn'.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hσ.1.le), ?_⟩
    intro a x hx z hz
    exact (hn'.2 a x hx z hz).trans (le_max_right _ _)
  · intro σ hσ hsmall
    exact hnormal σ hσ (hsmall.trans (min_le_right _ _))
  · intro σ hσ a x hx z hz
    exact hfieldsNormal σ hσ a x (hDBnormal hx) z hz

end JanetCartan.PositiveBackground
