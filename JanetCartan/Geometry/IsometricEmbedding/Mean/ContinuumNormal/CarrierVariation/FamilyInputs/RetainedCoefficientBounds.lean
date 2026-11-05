module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.NormalCompletionScaling

/-!
# Primitive regularity on the original retained scalar domain

The supplied retained chart keeps its original initial scalar even when the
carrier initial tube has a different radius. Its actual ODE label range gives
smoothness of the literal normal and reduced coefficient on the norm-chart
buffer. These are the regularity inputs to the positive-reference weighted
matrix comparison; no coefficient continuity is assumed.

Sources: `app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`,
and `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol
open NormalizedBackground RetainedLeading

/-- Smoothness of the SAME retained normal and full reduced coefficient on
an original scalar buffer. The initial scalar is extended only inside the
proof; equality on neighborhoods of the actual ODE labels removes that
extension. The geometric range hypotheses are supplied by
`exists_supported_originalScalar_comparison_buffers` on the doubled support.
Consumer: primitive absolute bounds for the positive-reference weighted
comparison (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem retained_originalScalar_coefficients_contDiffOn
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hRc : 0 < Rc) (hτ : 0 < τ)
    (hKΩ : K ⊆ Ω) (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (him : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    {S : Set (Euclidean n × CarrierParameter)}
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S K)
    (hSflow : MapsTo (densityCoordinates T) S
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (hfoot : MapsTo (densityFootpoint T c.inverse) S
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16))) :
    ContDiffOn ℝ ∞ (c.normal initial) S ∧ ContDiffOn ℝ ∞ c.reduced S := by
  let initial' := positiveInitialExtension z₀ hR initial
  have hi' : ContDiff ℝ ∞ initial' := positiveInitialExtension_contDiff z₀ hR initial hi
  have hpos' (p) : 0 < initial' p := positiveInitialExtension_pos z₀ hR initial hipos p
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hψΩ : MapsTo ψ S Ω := fun p hp ↦ hKΩ (hSK hp)
  have hψD : MapsTo ψ S
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D) :=
    fun p hp ↦ c.small_subset ((outputCylinder_spec hRc hτ).2 (hSflow hp))
  have hα := ((c.scalar_spec hτ initial' hi'.contDiffOn (fun p _ ↦ hpos' p)).1).comp
    hψ.contDiffOn hψD
  have hnull := c.null_smooth.comp hψ.contDiffOn hψΩ
  have hξ := (T.carrierGradient_smooth hP c.Q).comp hψ.contDiffOn
    (fun p hp ↦ ⟨(hKU (hSK hp)).1.2, (hKU (hSK hp)).2⟩)
  have hx : MapsTo Prod.fst S U := fun p hp ↦ (hKU (hSK hp)).1.1
  have hν := contDiffOn_canonicalPrincipalNormal hU hF him hrank hx hξ (hα.smul hnull)
  change ContDiffOn ℝ ∞ (c.normal initial') S at hν
  have heq (p) (hp : p ∈ S) : c.normal initial' p = c.normal initial p := by
    have hh := normal_positiveInitialExtension_eventuallyEq c hR initial (fun _ ↦ 1)
      (c.small_subset ((outputCylinder_spec hRc hτ).2 (hSflow hp))) (hfoot hp)
    simpa only [mul_one, initial'] using hh.eq_of_nhds
  refine ⟨hν.congr (fun p hp ↦ (heq p hp).symm), ?_⟩
  have hstress : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ c.Q.1 p.1) S :=
    c.Q.2.1.comp contDiffOn_fst hx
  have hq := ActualCarriers.contDiff_quadratic.comp_contDiffOn (hstress.prodMk hξ)
  change ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
    (quadratic (c.Q.1 p.1) (T.carrierGradient c.Q p.1 (parameter p.2))).ofLp) S
  have hout := PiLp.contDiff_ofLp.comp_contDiffOn hq
  exact hout

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}

variable
  (hdomain : ∀ z ∈ T.data.localReference.stateDomain, z.1 ∈ U)
  (hgeometry : ∃ (R : ℝ)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1)))),
    0 < R ∧ R < T.data.localReference.stateRadius ∧
    (∀ Q, ∀ q ∈ ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (T.family.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
    (∀ Q, ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
      ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
        closedBall (0, T.data.center) R) ∧
    (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      ∀ z ∈ closedBall (0, T.data.center) R,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0))

include hdomain hgeometry

/-- Absolute primitive controls for the original retained positive family.
The reference and masks determine one bound before the varying immersion;
the already proved immersion comparison supplies every current finite norm.
Both original initial-scalar domains and the chosen null minor remain fixed.
The geometric buffer inclusions are exactly those needed by the retained
coefficient regularity lemma above. Consumer:
`WideDensity.exists_canonical_weighted_sub_le_of_primitive_norms`, for
`app:ch_background:prop:bg-frame` and `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_retained_originalScalar_coefficient_controls
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    (hKFU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hx : MapsTo Prod.fst K (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (D : CoefficientNormCharts n)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.field.region K)
    (hSflow : MapsTo (densityCoordinates T) D.field.region
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {F₀ : Euclidean n → Euclidean N}
    (c₀ : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (hrank₀ : HasFullNormalRankOn F₀ U)
    {M κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F₀ ≤ M)
    (hmet₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (hfoot₀ : MapsTo (densityFootpoint T c₀.inverse) D.field.region
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (hm : ContDiffOn ℝ ∞ (FixedCutoffs.physical hr 1) D.measurement.region)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region) (m : ℕ) :
    let a₀ := TransportKernel.coefficientsOfCarrier
      (data T c₀.Q F₀ row col c₀.forward c₀.inverse initial hr hcell angular high)
      (FixedCutoffs.physical hr 1)
    ∃ Mc > (0 : ℝ), D.Controls (m + 1) Mc (Mc + 1) 1 a₀ ∧
      ∃ δ > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N)
        (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
        (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
          ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
          ∀ w ∈ normalSpace F x,
            κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        MapsTo (densityFootpoint T c.inverse) D.field.region
          (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
          (max 8 (max 1 m + 6)) (F - F₀) < δ →
        D.Controls m Mc (Mc + 1) 1 (TransportKernel.coefficientsOfCarrier
          (data T c.Q F row col c.forward c.inverse initial hr hcell angular high)
          (FixedCutoffs.physical hr 1)) := by
  dsimp only
  have hs₀ := retained_originalScalar_coefficients_contDiffOn c₀ hP hRc hτ hKΩ hKU
    hF₀ hi₀ hrank₀ hSK hSflow hR initial hi hipos hfoot₀
  let Mc := cNorm D.measurement.carrier (m + 1) (FixedCutoffs.physical hr 1) +
    cNorm D.angular.carrier (m + 1) (fun p ↦ angular p.1 p.2) +
    cNorm D.high.carrier (m + 1) high +
    cNorm D.field.carrier (m + 1) (c₀.normal initial) +
    cNorm D.field.carrier (m + 1) c₀.reduced + 1
  have hm₀ := cNorm_nonneg D.measurement.carrier (m + 1) (FixedCutoffs.physical hr 1)
  have ha₀ := cNorm_nonneg D.angular.carrier (m + 1) (fun p ↦ angular p.1 p.2)
  have hh₀ := cNorm_nonneg D.high.carrier (m + 1) high
  have hn₀ := cNorm_nonneg D.field.carrier (m + 1) (c₀.normal initial)
  have hq₀ := cNorm_nonneg D.field.carrier (m + 1) c₀.reduced
  have hMc : 0 < Mc := by dsimp only [Mc]; linarith only [hm₀, ha₀, hh₀, hn₀, hq₀]
  have hparts :
      cNorm D.measurement.carrier (m + 1) (FixedCutoffs.physical hr 1) ≤ Mc ∧
      cNorm D.angular.carrier (m + 1) (fun p ↦ angular p.1 p.2) ≤ Mc ∧
      cNorm D.high.carrier (m + 1) high ≤ Mc ∧
      cNorm D.field.carrier (m + 1) (c₀.normal initial) + 1 ≤ Mc ∧
      cNorm D.field.carrier (m + 1) c₀.reduced + 1 ≤ Mc := by
    dsimp only [Mc]
    exact ⟨by linarith only [hm₀, ha₀, hh₀, hn₀, hq₀],
      by linarith only [hm₀, ha₀, hh₀, hn₀, hq₀],
      by linarith only [hm₀, ha₀, hh₀, hn₀, hq₀],
      by linarith only [hm₀, ha₀, hh₀, hn₀, hq₀],
      by linarith only [hm₀, ha₀, hh₀, hn₀, hq₀]⟩
  have hcontrols {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup H] [NormedSpace ℝ H] (D : PrimitiveNormChart E)
      {f : E → H} {j k : ℕ} (h1 : 1 ≤ k) (hjk : j ≤ k)
      (hf : ContDiffOn ℝ ∞ f D.region) (hb : cNorm D.carrier k f ≤ Mc) :
      D.Controls j Mc (Mc + 1) 1 f := by
    refine ⟨hf, (cNorm_mono_order h1).trans hb, ?_⟩
    have hb' := (cNorm_mono_order hjk).trans hb
    simpa only [mul_one, add_comm] using add_le_add_left hb' 1
  have hfixed (j) (hj : j ≤ m + 1) :
      D.measurement.Controls j Mc (Mc + 1) 1 (FixedCutoffs.physical hr 1) ∧
      D.angular.Controls j Mc (Mc + 1) 1 (fun p ↦ angular p.1 p.2) ∧
      D.high.Controls j Mc (Mc + 1) 1 high :=
    ⟨hcontrols _ (by omega) hj hm hparts.1,
      hcontrols _ (by omega) hj ha hparts.2.1,
      hcontrols _ (by omega) hj hh hparts.2.2.1⟩
  refine ⟨Mc, hMc, ?_, ?_⟩
  · rw [c₀.coefficients_eq]
    refine ⟨(hfixed (m + 1) le_rfl).1, (hfixed (m + 1) le_rfl).2.1,
      (hfixed (m + 1) le_rfl).2.2,
      hcontrols _ (by omega) le_rfl hs₀.1 ?_, hcontrols _ (by omega) le_rfl hs₀.2 ?_⟩
    · linarith only [hparts.2.2.2.1]
    · linarith only [hparts.2.2.2.2]
  obtain ⟨δ, hδ, hcompare⟩ := RetainedLeading.exists_originalScalar_immersion_sub_tolerance
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx
    (isCompact_closedBall D.field.center D.field.radius)
    (fun p hp ↦ hSK (D.field.ball_subset hp))
    (fun p hp ↦ hSflow (D.field.ball_subset hp)) c₀ hF₀ hi₀ hrank₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos
    (fun p hp ↦ hfoot₀ (D.field.ball_subset hp)) (max 1 m) zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hsmall
  have hs := retained_originalScalar_coefficients_contDiffOn c hP hRc hτ hKΩ hKU
    hF him hrank hSK hSflow hR initial hi hipos hfoot
  have hp := hcompare F c hF him hrank hlow hmet hnormal
    (fun p hp ↦ hfoot (D.field.ball_subset hp)) hsmall
  change cNorm D.field.carrier (max 1 m + 2)
      (transportPosition T c.Q - transportPosition T c₀.Q) +
    cNorm D.field.carrier (max 1 m) (c.normal initial - c₀.normal initial) +
    cNorm D.field.carrier (max 1 m) (c.reduced - c₀.reduced) +
    cNorm D.field.carrier (max 1 m)
      (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < 1 at hp
  have hnc : cNorm D.field.carrier (max 1 m) (c.normal initial - c₀.normal initial) ≤ 1 := by
    linarith only [hp, cNorm_nonneg D.field.carrier (max 1 m + 2)
      (transportPosition T c.Q - transportPosition T c₀.Q),
      cNorm_nonneg D.field.carrier (max 1 m) (c.reduced - c₀.reduced),
      cNorm_nonneg D.field.carrier (max 1 m) (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)]
  have hqc : cNorm D.field.carrier (max 1 m) (c.reduced - c₀.reduced) ≤ 1 := by
    linarith only [hp, cNorm_nonneg D.field.carrier (max 1 m + 2)
      (transportPosition T c.Q - transportPosition T c₀.Q),
      cNorm_nonneg D.field.carrier (max 1 m) (c.normal initial - c₀.normal initial),
      cNorm_nonneg D.field.carrier (max 1 m) (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)]
  have hbound {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      {f f₀ : Euclidean n × CarrierParameter → H}
      (hf : ContDiffOn ℝ ∞ f D.field.region) (hf₀ : ContDiffOn ℝ ∞ f₀ D.field.region)
      (hd : cNorm D.field.carrier (max 1 m) (f - f₀) ≤ 1)
      (hb : cNorm D.field.carrier (m + 1) f₀ + 1 ≤ Mc) :
      cNorm D.field.carrier (max 1 m) f ≤ Mc := by
    have hsum := cNorm_add_le_of_contDiffAt (r := max 1 m)
      (isCompact_closedBall D.field.center D.field.radius)
      (fun p hp ↦ ((hf.sub hf₀).contDiffAt (D.field.isOpen_region.mem_nhds
        (D.field.ball_subset hp))).of_le (by simp))
      (fun p hp ↦ (hf₀.contDiffAt (D.field.isOpen_region.mem_nhds
        (D.field.ball_subset hp))).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hsum
    change cNorm D.field.carrier (max 1 m) f ≤
      cNorm D.field.carrier (max 1 m) (f - f₀) + cNorm D.field.carrier (max 1 m) f₀ at hsum
    have hmono := cNorm_mono_order (s := D.field.carrier) (f := f₀) (by omega : max 1 m ≤ m + 1)
    linarith only [hsum, hd, hb, hmono]
  rw [c.coefficients_eq]
  exact ⟨(hfixed m (by omega)).1, (hfixed m (by omega)).2.1, (hfixed m (by omega)).2.2,
    hcontrols _ (le_max_left ..) (le_max_right ..) hs.1 (hbound hs.1 hs₀.1 hnc hparts.2.2.2.1),
    hcontrols _ (le_max_left ..) (le_max_right ..) hs.2 (hbound hs.2 hs₀.2 hqc hparts.2.2.2.2)⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
