module

public import JanetCartan.Iteration.PhysicalDensityContinuity.Buffers
public import JanetCartan.Iteration.PhysicalDensityContinuity.Coefficients
public import JanetCartan.Iteration.PhysicalInverseContinuity.Domains
public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# Actual same-source finite-carrier physical mean continuity

The finite continuum tuple, parameter weights, original charts and fixed
source contraction are unchanged. The external weight's entire support is
controlled in the original open product, including its collar outside the
detector support. A physical immersion-jet neighborhood
produces the current geometric gaps, original normal/covector differences,
and then the actual zero-density mean difference. No mean or field continuity
premise, successful source, sampled realization, or response estimate is used.
Consumer: `exists_measured_tangent_source_tolerance` and the current raising
step of `app:ch_background:prop:bg-current`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 6000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalDensityContinuity

open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CanonicalConic PositiveBackground
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {ι : Type} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {Ω K : ι → Set (Euclidean n × Euclidean 3)}
    {z₀ : ι → Euclidean 3} {Rc B τ : ι → ℝ} {row col : ι → Fin n}

variable
  (hdomain : ∀ i, ∀ z ∈ (T i).data.localReference.stateDomain, z.1 ∈ U)
  (hgeometry : ∀ i, ∃ (R : ℝ)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1)))),
    0 < R ∧ R < (T i).data.localReference.stateRadius ∧
    (∀ Q, ∀ q ∈ ball ((0 : ℝ), (T i).data.adapted.baseData) (3 * (T i).family.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ ((T i).family.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
    (∀ Q, ∀ q ∈ ((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters,
      (((T i).family.flow Q).position q, ((T i).family.flow Q).momentum q) ∈
        closedBall (0, (T i).data.center) R) ∧
    (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold},
      ∀ z ∈ closedBall (0, (T i).data.center) R,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, (T i).data.adapted.normal⟫_ℝ ≠ 0))

include hdomain hgeometry in
/-- The actual finite original carrier mean at fixed contraction is continuous
in the sole physical immersion jet of order `max 8 (m + 6)`. The original
`6 * μ < rᵢ` and coefficient support margins construct the mean's compact and
open products; every analytic field continuity input is proved below. -/
theorem exists_prescribed_source_density_mean_tolerance
    {c₁ C : ι → ℝ} (hP : ∀ i, (P i).IsValid (c₁ i) (C i))
    (hΩ : ∀ i, IsOpen (Ω i)) (hK : ∀ i, IsCompact (K i))
    (hKΩ : ∀ i, K i ⊆ Ω i)
    (hRc : ∀ i, 0 < Rc i) (hB : ∀ i, 0 ≤ B i) (hτ : ∀ i, 0 < τ i)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ i)) (Rc i)) (K i))
    (hτeq : ∀ i, τ i = existenceTime (Rc i) (liftedLowBound (T i) (B i)) / 4)
    (hKFU : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (hΩpatch : ∀ i, Ω i ⊆ (U ∩ ball (0 : Euclidean n) (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (hx : ∀ i, MapsTo Prod.fst (K i) (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius))
    (D : ι → CoefficientNormCharts n)
    (H : FlatReference n) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    (cSource : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
      (Rc i) (B i) (τ i) (row i) (col i) (sourceDilation H.map σ))
    {Rwork : ℝ} (hRwork : 0 < Rwork) (hworkChart : Rwork < H.domain.chartRadius)
    (hUwork : U ⊆ ball 0 Rwork)
    {R Mc : ι → ℝ} (hR : ∀ i, 0 < R i) (hMc : ∀ i, 0 < Mc i)
    (hforward : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n))
      (current : Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F),
      cNorm (Icc (-(τ i)) (τ i) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8))
        1 current.forward ≤ Mc i)
    {Rphysical : ι → ℝ} {Voriginal : ι → Set CarrierParameter}
    (hVoriginal : ∀ i, IsOpen (Voriginal i))
    (hRtime : ∀ i, Rphysical i ≤ R i / (64 * Mc i))
    (hflow : ∀ i, MapsTo (densityCoordinates (T i))
      (ball (0 : Euclidean n) (Rphysical i) ×ˢ Voriginal i)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (τ i)))
    (hlabelProduct : ∀ i p, p ∈ ball (0 : Euclidean n) (Rphysical i) ×ˢ Voriginal i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 64))
    (hDregion : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (Rphysical i) ×ˢ Voriginal i)
    {zRoot : ι → Euclidean 3} {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (hcell : ∀ i, 4 * r i < 1 / 2)
    (angular : ι → CarrierParameter → Euclidean (n - 1) → ℝ)
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (hr i) 1) ×ˢ
      carrierSupport (zRoot i) (r := r i) ⊆ (D i).field.carrier)
    {μ : ℝ} (hμ : 0 < μ) (hμr : ∀ i, 6 * μ < r i)
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i))
    (hχsupport : ∀ i, tsupport (χ i) ⊆ Voriginal i) :
    let F₀ := sourceDilation H.map σ
    let Kbig := closedBall (0 : Euclidean n) (max ((Rwork + H.domain.chartRadius) / 2) (6 * μ))
    let d₀ := fun i ↦ data (T i) (cSource i).Q F₀ (row i) (col i) (cSource i).forward
      (cSource i).inverse (fun _ ↦ σ) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    ∀ (m : ℕ) {ε : ℝ}, 0 < ε → ∃ δ > 0,
      ContDiffOn ℝ ∞ (physicalDensityMean d₀ χ 0) (ball 0 (4 * μ)) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)), ContDiff ℝ ∞ F →
        cNorm Kbig (max 8 (m + 6)) (F - F₀) < δ →
      ∀ current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F,
      let d := fun i ↦ data (T i) (current i).Q F (row i) (col i) (current i).forward
        (current i).inverse (fun _ ↦ σ) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
      ContDiffOn ℝ ∞ (physicalDensityMean d χ 0) (ball 0 (4 * μ)) ∧
        cNorm (closedBall 0 (3 * μ)) m (physicalDensityMean d χ 0 - physicalDensityMean d₀ χ 0) < ε := by
  classical
  intro F₀ Kbig d₀ m ε hε
  let reference := sourceDilationReference H hσ hσone
  let Rbig := (Rwork + H.domain.chartRadius) / 2
  have hworkBig : Rwork < Rbig := by dsimp only [Rbig]; linarith
  have hbigChart : Rbig < reference.domain.chartRadius := by
    change Rbig < H.domain.chartRadius
    dsimp only [Rbig]
    linarith
  obtain ⟨δg, hδg, Cg, _hCg, κg, hκg, hgeo⟩ :=
    CurrentGeometricNeighborhood.exists_geometric_neighborhood reference hRwork hworkBig hbigChart
      (by norm_num : (0 : ℝ) < 1)
  have hUbig : U ⊆ ball 0 Rbig := hUwork.trans (ball_subset_ball hworkBig.le)
  have hsub (i : ι) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall 0 Rwork := ((hKFU i).trans hUwork).trans ball_subset_closedBall
  have hnorm (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F) (i : ι) :
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 4 F ≤
      cNorm (closedBall (0 : Euclidean n) Rwork) 4 F :=
    cNorm_mono_set_of_contDiffAt (hsub i) (isCompact_closedBall _ _)
      (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
  have hG := hgeo univ reference.map isOpen_univ (subset_univ _) reference.contDiff.contDiffOn
    (by simpa only [sub_self, cNorm_zero] using hδg)
  have hiRef : IsImmersionOn F₀ U := fun x hx ↦ hG.1 x (hUbig hx)
  have hrankRef : HasFullNormalRankOn F₀ U := fun x hx ↦ hG.2.1 x (hUbig hx)
  have hKU (i : ι) : K i ⊆ CoefficientBounds.inputDomain (T i) := by
    intro p hp
    obtain ⟨hx, hz⟩ := hΩpatch i (hKΩ i hp)
    exact ⟨hx, fun j ↦ (hz j).trans_le (by linarith only [(hP i).1])⟩
  have hτRc (i : ι) : τ i ≤ Rc i / 16 := by
    have ht := (existenceTime_le (hRc i) (liftedLowBound_nonneg (T i) (hB i))).1
    rw [hτeq i]
    linarith
  let Dwide : ι → CoefficientNormCharts n := fun i ↦
    { D i with field := { (D i).field with
        region := ball (0 : Euclidean n) (Rphysical i) ×ˢ Voriginal i
        isOpen_region := isOpen_ball.prod (hVoriginal i)
        ball_subset := (D i).field.ball_subset.trans (hDregion i) } }
  have hSflow (i : ι) := hflow i
  have hlabels (i : ι) (p) (hp : p ∈ (Dwide i).field.region) := hlabelProduct i p hp
  have htime (i : ι) (p : Euclidean n × CarrierParameter) (hp : p ∈ (Dwide i).field.region) :
      |(densityCoordinates (T i) p).1| < R i / (64 * Mc i) := by
    have ht := abs_real_inner_le_norm (T i).data.adapted.normal p.1
    rw [(T i).data.adapted.normal_unit, one_mul] at ht
    change |(adaptedCoordinates (T i).data.adapted p.1).1| < R i / (64 * Mc i)
    rw [adaptedCoordinates_apply]
    exact (ht.trans_lt (mem_ball_zero_iff.mp hp.1)).trans_le (hRtime i)
  have hdom (i : ι) (F : Euclidean n → Euclidean (embeddingDimension n))
      (c : Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (B i) (τ i)
        (row i) (col i) F) :=
    PhysicalInverseContinuity.retained_region_input_and_footpoint (T i) (hRc i) (hτ i) (hτRc i)
      (hR i) (hMc i) (hbuffer i) (Dwide i) (hSflow i) (hlabels i) (htime i) c (hforward i F c)
  let V := Voriginal
  have hV := hVoriginal
  have hχV := hχsupport
  have hproduct := original_density_mean_product D zRoot hr hμr hDregion hsupportD
  have hVD (i) : ball (0 : Euclidean n) (6 * μ) ×ˢ V i ⊆ (Dwide i).field.region :=
    (Set.prod_mono ball_subset_closedBall Subset.rfl).trans (hproduct i)
  let J := fun i ↦ closedBall (0 : Euclidean n) (5 * μ) ×ˢ tsupport (χ i)
  have hJ (i) : IsCompact (J i) := (isCompact_closedBall _ _).prod (hχc i)
  have hJregion (i) : J i ⊆ (Dwide i).field.region :=
    (Set.prod_mono (closedBall_subset_closedBall (by linarith : 5 * μ ≤ 6 * μ))
      (hχsupport i)).trans (hproduct i)
  have hJW (i) : J i ⊆ ball (0 : Euclidean n) (6 * μ) ×ˢ V i :=
    Set.prod_mono (closedBall_subset_ball (by linarith)) (hχV i)
  have hUJ (i) : ball (0 : Euclidean n) (4 * μ) ×ˢ tsupport (χ i) ⊆ J i :=
    Set.prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) Subset.rfl
  have hfields (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F)
      (him : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
      (current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F) (i : ι) :
      ContDiffOn ℝ ∞ ((current i).normal (fun _ ↦ σ)) (ball (0 : Euclidean n) (6 * μ) ×ˢ V i) ∧
      ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
        (T i).carrierGradient (current i).Q p.1 (parameter p.2))
        (ball (0 : Euclidean n) (6 * μ) ×ˢ V i) := by
    have hd := hdom i F (current i)
    have hn := retained_originalScalar_coefficients_contDiffOn (current i) (hP i) (hRc i) (hτ i)
      (hKΩ i) (hKU i) hF.contDiffOn him hrank hd.1 (hSflow i) (hR i) (fun _ ↦ σ)
      contDiffOn_const (fun _ _ ↦ hσ) hd.2
    refine ⟨hn.1.mono (hVD i), ?_⟩
    apply ((T i).carrierGradient_smooth (hP i) (current i).Q).comp
      (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn
    intro p hp
    have hpk := hKU i (hd.1 (hVD i hp))
    exact ⟨hpk.1.2, hpk.2⟩
  have hν₀ (i) := (hfields F₀ reference.contDiff hiRef hrankRef cSource i).1
  have hξ₀ (i) := (hfields F₀ reference.contDiff hiRef hrankRef cSource i).2
  have hH₀ : ContDiffOn ℝ ∞ (physicalDensityMean d₀ χ 0) (ball 0 (6 * μ)) :=
    contDiffOn_physicalDensityMean_zero d₀ χ hχ hχc isOpen_ball V hV hχV hν₀ hξ₀
  obtain ⟨δmean, hδmean, hmean⟩ := PhysicalBackground.exists_physicalDensityMean_zero_sub_tolerance
    (isCompact_closedBall (0 : Euclidean n) (3 * μ)) isOpen_ball isOpen_ball
    (closedBall_subset_ball (by linarith : 3 * μ < 4 * μ))
    (ball_subset_ball (by linarith : 4 * μ ≤ 6 * μ)) χ hχ hχc V hV hχV J hJ hJW hUJ
    d₀ hν₀ hξ₀ m hε
  have hcomp (i : ι) := exists_retained_normal_covector_sub_tolerance (T i) (hdomain i) (hgeometry i)
    (hP i) (hΩ i) (hK i) (hKΩ i) (hRc i) (hB i) (hτ i) (hbuffer i) (hτeq i)
    (hKFU i) (hKU i) (hx i) (hJ i) ((hdom i F₀ (cSource i)).1.mono_left (hJregion i))
    ((hSflow i).mono_left (hJregion i)) (cSource i) reference.contDiff.contDiffOn hiRef hrankRef
    (M := Cg) (κmet := 1 / 4) (κnormal := κg) (by norm_num) hκg
    ((hnorm _ reference.contDiff i).trans hG.2.2.1)
    (fun x hx ↦ hG.2.2.2.1 x (hUbig (hKFU i hx)))
    (fun x hx ↦ hG.2.2.2.2.1 x (hUbig (hKFU i hx))) (hR i) (fun _ ↦ σ)
    contDiffOn_const (fun _ _ ↦ hσ) ((hdom i F₀ (cSource i)).2.mono_left (hJregion i)) m (hδmean i)
  choose δc hδc hcarrier using hcomp
  obtain ⟨δall, hδall, hδi⟩ := Pi.exists_forall_pos_add_lt hδc
  refine ⟨min δg δall, lt_min hδg hδall, hH₀.mono (ball_subset_ball (by linarith)), ?_⟩
  intro F hF hsmall current d
  have hjet {E : Set (Euclidean n)} (hE : E ⊆ Kbig) :
      cNorm E (max 8 (m + 6)) (F - F₀) ≤ cNorm Kbig (max 8 (m + 6)) (F - F₀) :=
    cNorm_mono_set_of_contDiffAt hE (isCompact_closedBall _ _)
      (fun _ _ ↦ (hF.sub reference.contDiff).contDiffAt.of_le (by simp))
  have hnow := hgeo univ F isOpen_univ (subset_univ _) hF.contDiffOn
    ((cNorm_mono_order (le_max_left 8 (m + 6))).trans_lt
      ((hjet (closedBall_subset_closedBall (le_max_left _ _))).trans_lt
        (hsmall.trans_le (min_le_left _ _))))
  have him : IsImmersionOn F U := fun x hx ↦ hnow.1 x (hUbig hx)
  have hrank : HasFullNormalRankOn F U := fun x hx ↦ hnow.2.1 x (hUbig hx)
  have hν (i) := (hfields F hF him hrank current i).1
  have hξ (i) := (hfields F hF him hrank current i).2
  have hH : ContDiffOn ℝ ∞ (physicalDensityMean d χ 0) (ball 0 (6 * μ)) :=
    contDiffOn_physicalDensityMean_zero d χ hχ hχc isOpen_ball V hV hχV hν hξ
  refine ⟨hH.mono (ball_subset_ball (by linarith)), hmean d hν hξ ?_⟩
  intro i
  have hclose : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius)
      (max 8 (m + 6)) (F - F₀) < δc i := by
    apply (hjet ((hsub i).trans
      (closedBall_subset_closedBall (hworkBig.le.trans (le_max_left _ _))))).trans_lt
    exact (hsmall.trans_le (min_le_right _ _)).trans (by simpa only [zero_add] using hδi i)
  exact hcarrier i F (current i) hF.contDiffOn him hrank ((hnorm _ hF i).trans hnow.2.2.1)
    (fun x hx ↦ hnow.2.2.2.1 x (hUbig (hKFU i hx)))
    (fun x hx ↦ hnow.2.2.2.2.1 x (hUbig (hKFU i hx)))
    ((hdom i F (current i)).2.mono_left (hJregion i)) hclose

end JanetCartan.PhysicalDensityContinuity
