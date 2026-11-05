module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CommonBalls
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.IncidenceScaling

/-!
# Actual mask refinement for the supported normalized shell

The normalized augmented derivative gap gives a uniform Lipschitz bound on
the existing input ball. Shrinking only the masks, and reducing the primitive
frame threshold for the central value, puts their fixed-sphere output in the
existing output ball. No transformed support containment is assumed.
The geometric inputs below are produced by `exists_common_conic_balls`;
`ActualGeometry` instantiates them for the retained projected-stress family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ}

private theorem augmented_derivative_norm_le
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (D : InputVariables n →L[ℝ] Variables n × Euclidean 2)
    (hgap : ‖A.symm.toContinuousLinearMap.comp D -
      ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) :
    ‖D‖ ≤ 2 * (‖A.toContinuousLinearMap‖ + 1) := by
  have he : D = A.toContinuousLinearMap.comp (A.symm.toContinuousLinearMap.comp D) := by
    apply ContinuousLinearMap.ext
    intro p
    exact (A.apply_symm_apply (D p)).symm
  have hb : ‖A.symm.toContinuousLinearMap.comp D‖ ≤ 2 := by
    have ht := norm_sub_le (A.symm.toContinuousLinearMap.comp D -
      ContinuousLinearMap.id ℝ (InputVariables n))
      (-ContinuousLinearMap.id ℝ (InputVariables n))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := InputVariables n)
    linarith
  calc
    ‖D‖ ≤ ‖A.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap.comp D‖ := by
      conv_lhs => rw [he]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A.toContinuousLinearMap‖ * 2 :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ 2 * (‖A.toContinuousLinearMap‖ + 1) := by linarith

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Smaller positive masks and a primitive frame threshold yield the exact
supported shell on the sphere of radius `‖k‖`. The half-gap is the existing
common-ball output and itself implies differentiability; no extra analytic
premise is added. The central
value comparison is proved here from primitive frame closeness. All choices
precede `Q`; the inverse and its larger domains are retained (`bg-Psi`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_refined_supported_shell {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a ρ τ : ℝ} (hr : 0 < r) (ha : 0 < a) (hρ : 0 < ρ) (hτ : 0 < τ) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    ∃ r' > (0 : ℝ), r' ≤ r ∧ r' ≤ ρ ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ r' ∧ 4 * a' < ρ ∧
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      ∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  let q₀ := frozenAugmentedChart T p₀
  let A := augmentedReferenceEquiv T hP hz₀ hinc hd
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hq₀ : q₀ = ((0, 0, k), spectatorCenter z₀) := frozenAugmentedChart_center T hP hz₀ hinc
  have hℓ : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hqnorm : ‖q₀.1.2.2‖ = ‖k‖ := by rw [hq₀]
  have hn : normalizeOutputRadius ‖k‖ q₀ = q₀ := normalizeOutputRadius_eq_self hℓ hqnorm
  obtain ⟨e, he, hnormalize⟩ := Metric.continuousAt_iff.mp
    (normalizeOutputRadius_continuousAt ‖k‖ (p := q₀) (by simpa only [hq₀] using hk)) τ hτ
  let B := 2 * (‖A.toContinuousLinearMap‖ + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  let d := min ρ (e / (4 * B))
  have hdpos : 0 < d := lt_min hρ (by positivity)
  have hdρ : d ≤ ρ := min_le_left _ _
  have hBd : B * d ≤ e / 4 := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right ρ (e / (4 * B))) hB.le
    have heq : B * (e / (4 * B)) = e / 4 := by field_simp
    exact hm.trans_eq heq
  obtain ⟨r', hr', hrr, hrd, a', ha', haa, har', had⟩ := exists_refined_mask_radii hr ha hdpos
  obtain ⟨δ, hδ, hcenter⟩ := exists_augmented_center_threshold T hP hz₀ k (show 0 < e / 4 by positivity)
  refine ⟨r', hr', hrr, hrd.trans hdρ, a', ha', haa, har', had.trans_le hdρ, δ, hδ, ?_⟩
  intro Q hQ hgap
  have hdiff : ∀ p ∈ closedBall p₀ ρ,
      DifferentiableAt ℝ (augmentedTransportGradient (transportPosition T Q)) p := by
    intro p hp
    by_contra hd
    have hg := hgap p hp
    rw [fderiv_zero_of_not_differentiableAt hd] at hg
    simp only [ContinuousLinearMap.comp_zero, zero_sub, norm_neg, ContinuousLinearMap.norm_id] at hg
    norm_num at hg
  apply supported_shell_of_normalized_image hℓ
  intro p hp
  let t := ‖ηb‖ / ‖p.2.2‖
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hηb) (norm_pos_iff.mpr hp.2.2.1)
  have hpd : scaleInput t p ∈ ball p₀ d :=
    conicMaskSupport_radial_section_mem_ball hηb hr' ha' had hrd hp
  have hpρ : scaleInput t p ∈ closedBall p₀ ρ :=
    closedBall_subset_closedBall hdρ (ball_subset_closedBall hpd)
  have hbound : ∀ q ∈ closedBall p₀ ρ,
      ‖fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) q‖ ≤ B :=
    fun q hq ↦ augmented_derivative_norm_le A _ (hgap q hq)
  have hmove := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall p₀ ρ) (mem_closedBall_self hρ.le) hpρ
  have hnear : dist (augmentedTransportGradient (transportPosition T Q) (scaleInput t p)) q₀ < e := by
    have hc := hcenter Q hQ
    have hpdist : ‖scaleInput t p - p₀‖ < d := mem_ball_iff_norm.mp hpd
    have hm := mul_lt_mul_of_pos_left hpdist hB
    have ht' := norm_add_le
      (augmentedTransportGradient (transportPosition T Q) (scaleInput t p) -
        augmentedTransportGradient (transportPosition T Q) p₀)
      (augmentedTransportGradient (transportPosition T Q) p₀ - q₀)
    rw [sub_add_sub_cancel] at ht'
    rw [dist_eq_norm]
    change ‖augmentedTransportGradient (transportPosition T Q) p₀ - q₀‖ ≤ e / 4 at hc
    linarith
  have hout := (hn ▸ hnormalize hnear).le
  rw [augmentedTransportGradient_scaleInput, normalizeOutputRadius_scale _ _ ht] at hout
  exact hout

/-- The canonical inverse has the uniform input-frequency bound with
`Cupper = 2`. Together with a radius-`1/4` incidence representative this
proves `Cupper * ℓ ≤ 1` for the supported carrier constructor (`bg-jacobian`). -/
theorem symbolInverse_norm_le_two
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    {p : Variables n × Euclidean 2} (hp : p ∈ symbolDomain T Q z₀ ηb r a) :
    ‖(symbolInverse T Q z₀ ηb r a p).2‖ ≤ 2 * ‖p.1.2.2‖ := by
  let q := inverseCoordinates (symbolInverse T Q z₀ ηb r a) p
  have hq := symbolInverse_maps T Q hηb hr hInv htrans hp
  have hb := htrans _ hq.1 _ hq.2
  have htriangle := norm_sub_le
    ((adaptedTransportChart T Q (q.2.1.2, q.1.1, q.1.2) (q.2.1.1, q.2.2)).2)
    (((adaptedTransportChart T Q (q.2.1.2, q.1.1, q.1.2) (q.2.1.1, q.2.2)).2) - q.2.2)
  rw [sub_sub_cancel] at htriangle
  have hproj := norm_snd_le (adaptedTransportChart T Q (q.2.1.2, q.1.1, q.1.2) (q.2.1.1, q.2.2))
  have hphys := adaptedTransportChart_norm_le_physical T Q
    (q.2.1.2, q.1.1, q.1.2) (q.2.1.1, q.2.2)
  have he := transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp
  change transportAveragedGradient (transportPosition T Q) q = p.1.2.2 at he
  change _ ≤ ‖transportAveragedGradient (transportPosition T Q) q‖ at hphys
  rw [he] at hphys
  have hw := (angularWidth_spec hηb hr).2.1
  have hn := norm_nonneg q.2.2
  change ‖q.2.2‖ ≤ 2 * ‖p.1.2.2‖
  nlinarith

end JanetCartan.ContinuumRow.CanonicalConic
