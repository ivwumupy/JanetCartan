module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.InitialScalar
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.CanonicalFields

/-!
# Primitive comparison of the original retained scalar and normal

The original scalar is smooth and positive only on its original `R / 8` ball.
Its positive extension is used inside the ODE estimate and removed using
neighborhood equality at the actual inverse footpoint. The carrier radius `Rc`
is independent of `R`. The chart and footpoint-range inputs are produced by
`exists_full_leading_originalScalar_chart_before_budgets`.

Consumer: the retained-leading family assembly for
`app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`, and
`app:ch_osc:prop:osc-normal`, Step 4'. The Hamilton-gradient and frame differences
remain primitive inputs; this is not the immersion-only comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}

/-- Remove the auxiliary extension on a neighborhood of the ACTUAL inverse
footpoint. This preserves all normal jets, including arbitrary initial weights,
without changing either flow or null column (`app:ch_waves:eq:joint-tame`). -/
theorem normal_positiveInitialExtension_eventuallyEq
    (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    {R : ℝ} (hR : 0 < R) (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {p : Euclidean n × CarrierParameter}
    (hp : densityCoordinates T p ∈ c.D)
    (hfoot : densityFootpoint T c.inverse p ∈
      ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) :
    c.normal (fun q ↦ positiveInitialExtension z₀ hR initial q * weight q) =ᶠ[𝓝 p]
      c.normal (fun q ↦ initial q * weight q) := by
  have hcont : ContinuousAt (densityFootpoint T c.inverse) p :=
    ((c.inverse_smooth.contDiffAt (c.domain_open.mem_nhds hp)).continuousAt).comp
      (densityCoordinates T).continuous.continuousAt
  filter_upwards [hcont.eventually (isOpen_ball.mem_nhds hfoot)] with q hq
  exact normalField_positiveInitialExtension_eq T c.Q F row col c.forward c.inverse
    z₀ hR initial weight hq

private theorem exists_chart_primitives_sub_tolerance
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T) (hx : MapsTo Prod.fst K KF)
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S K)
    (hSflow : MapsTo (densityCoordinates T) S
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {F₀ : Euclidean n → Euclidean N}
    (c₀ : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (hrank₀ : HasFullNormalRankOn F₀ U)
    {M κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm KF 4 F₀ ≤ M)
    (hmet₀ : ∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ KF, ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8), 0 < initial p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm KF 4 F ≤ M →
      (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm KF (m + 1) (c.Q.1 - c₀.Q.1) +
        cNorm K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
          T.carrierGradient c₀.Q p.1 p.2) + cNorm KF (m + 2) (F - F₀) < δ →
      cNorm S m (c.normal initial - c₀.normal initial) +
        cNorm S m (c.reduced - c₀.reduced) +
        cNorm S m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε := by
  have he : 0 < ε / 4 := by positivity
  have hα₀ := c₀.scalar_contDiffAt hRc hτ initial hi hipos hSflow
  obtain ⟨dN, hdN, hnormal⟩ := exists_normalField_primitive_sub_tolerance T hP
    hK hKF hS hKFU hKU hx hSK c₀.Q c₀.frame_eq hF₀ hi₀ hrank₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ row col c₀.forward c₀.inverse initial hα₀ m he
  obtain ⟨dD, hdD, hdet⟩ := exists_canonical_reduced_sub_tolerance T hP
    hK hS hKU hSK c₀.Q m he
  obtain ⟨A, hA, hinput⟩ := exists_actualInput_sub_bound T hP hK hKF hKFU hKU hx
  have hfε : 0 < min (ε / 4) (dN / 4) := lt_min he (by positivity)
  obtain ⟨dF, hdF, hflow⟩ := c₀.exists_primitive_transport_sub_tolerance hP hΩ hK hKΩ
    hRc hB hbuffer hτeq hKF hKFU hKU hx (Kphysical := ∅) isCompact_empty hS
    (mapsTo_empty _ _) hSflow hF₀ hi₀ initial hi hipos m hfε
  have hAm := hA m
  let δ := min (dN / 4) (min dF (dD / (A m + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min hdF (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro F c hF him hrank hlow hmet hnormalgap hsmall
  have hframe : cNorm KF (m + 1) (c.Q.1 - c₀.Q.1) < δ := by
    have := cNorm_nonneg K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
      T.carrierGradient c₀.Q p.1 p.2)
    have := cNorm_nonneg KF (m + 2) (F - F₀)
    linarith
  have hgrad : cNorm K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
      T.carrierGradient c₀.Q p.1 p.2) < δ := by
    have := cNorm_nonneg KF (m + 1) (c.Q.1 - c₀.Q.1)
    have := cNorm_nonneg KF (m + 2) (F - F₀)
    linarith
  have himm : cNorm KF (m + 2) (F - F₀) < δ := by
    have := cNorm_nonneg KF (m + 1) (c.Q.1 - c₀.Q.1)
    have := cNorm_nonneg K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
      T.carrierGradient c₀.Q p.1 p.2)
    linarith
  obtain ⟨_, _, hflow'⟩ := hflow F c hF
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hscalar : cNorm S m ((fun p ↦ c.scalar initial (p.1, parameter p.2)) -
      (fun p ↦ c₀.scalar initial (p.1, parameter p.2))) < dN / 4 := by
    have hh := hflow'.trans_le (min_le_right _ _)
    have := cNorm_nonneg (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) m (c.forward - c₀.forward)
    have := cNorm_nonneg (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) m (c.inverse - c₀.inverse)
    have := cNorm_nonneg (∅ : Set (Euclidean n × Euclidean 3)) m (c.scalar initial - c₀.scalar initial)
    have := cNorm_nonneg S m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)
    linarith
  have hfoot : cNorm S m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε / 4 := by
    have hh := hflow'.trans_le (min_le_left _ _)
    have := cNorm_nonneg (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) m (c.forward - c₀.forward)
    have := cNorm_nonneg (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) m (c.inverse - c₀.inverse)
    have := cNorm_nonneg (∅ : Set (Euclidean n × Euclidean 3)) m (c.scalar initial - c₀.scalar initial)
    have := cNorm_nonneg S m ((fun p ↦ c.scalar initial (p.1, parameter p.2)) -
      (fun p ↦ c₀.scalar initial (p.1, parameter p.2)))
    linarith
  have hframe₀ : cNorm KF m (c.Q.1 - c₀.Q.1) < δ :=
    (cNorm_mono_order (Nat.le_succ m)).trans_lt hframe
  have hgrad₀ : cNorm K m (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
      T.carrierGradient c₀.Q p.1 p.2) < δ :=
    (cNorm_mono_order (Nat.le_succ m)).trans_lt hgrad
  have hnormal' : cNorm S m (c.normal initial - c₀.normal initial) < ε / 4 := by
    apply hnormal c.Q F c.forward c.inverse initial c.frame_eq hF him hrank hlow hmet
      hnormalgap (c.scalar_contDiffAt hRc hτ initial hi hipos hSflow)
    have htN : δ ≤ dN / 4 := min_le_left _ _
    dsimp only [Chart.scalar] at hscalar
    linarith only [himm, hframe₀, hgrad₀, hscalar, htN]
  have hdet' : cNorm S m (c.reduced - c₀.reduced) < ε / 4 := by
    apply hdet c.Q
    apply (hinput c.Q c₀.Q m).trans_lt
    have hb : 0 < A m + 1 := by linarith
    have htD : δ ≤ dD / (A m + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have htd := (le_div_iff₀ hb).mp htD
    have hqs := mul_lt_mul_of_pos_left hframe₀ (hA m)
    nlinarith only [hqs, hgrad₀, htd]
  linarith

/-- Primitive frame, Hamilton-gradient and immersion differences control the
SAME original normal, full reduced vector and ACTUAL ODE density footpoint.
The original scalar is prescribed on `R / 8`; no radius equality or scalar-gauge
hypothesis is used. The chart and range assumptions are concrete outputs of
`exists_full_leading_originalScalar_chart_before_budgets`. Source:
`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_originalScalar_primitives_sub_tolerance
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T) (hx : MapsTo Prod.fst K KF)
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S K)
    (hSflow : MapsTo (densityCoordinates T) S
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {F₀ : Euclidean n → Euclidean N}
    (c₀ : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (hrank₀ : HasFullNormalRankOn F₀ U)
    {M κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm KF 4 F₀ ≤ M)
    (hmet₀ : ∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ KF, ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (hfoot₀ : MapsTo (densityFootpoint T c₀.inverse) S
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm KF 4 F ≤ M →
      (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) S
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      cNorm KF (m + 1) (c.Q.1 - c₀.Q.1) +
        cNorm K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
          T.carrierGradient c₀.Q p.1 p.2) + cNorm KF (m + 2) (F - F₀) < δ →
      cNorm S m (c.normal initial - c₀.normal initial) +
        cNorm S m (c.reduced - c₀.reduced) +
        cNorm S m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε := by
  let ie := positiveInitialExtension z₀ hR initial
  have hie : ContDiff ℝ ∞ ie := positiveInitialExtension_contDiff z₀ hR initial hi
  have hiep : ∀ p, 0 < ie p := positiveInitialExtension_pos z₀ hR initial hipos
  obtain ⟨δ, hδ, hcompare⟩ := exists_chart_primitives_sub_tolerance hP hΩ hK hKΩ
    hRc hB hτ hbuffer hτeq hKF hKFU hKU hx hS hSK hSflow c₀ hF₀ hi₀ hrank₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ ie hie.contDiffOn (fun p _ ↦ hiep p) m hε
  refine ⟨δ, hδ, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hsmall
  have hout := hcompare F c hF him hrank hlow hmet hnormal hsmall
  have he : cNorm S m (c.normal ie - c₀.normal ie) =
      cNorm S m (c.normal initial - c₀.normal initial) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro p hp
    have h₁ := normal_positiveInitialExtension_eventuallyEq c hR initial (fun _ ↦ 1)
      (c.small_subset ((outputCylinder_spec hRc hτ).2 (hSflow hp))) (hfoot hp)
    have h₀ := normal_positiveInitialExtension_eventuallyEq c₀ hR initial (fun _ ↦ 1)
      (c₀.small_subset ((outputCylinder_spec hRc hτ).2 (hSflow hp))) (hfoot₀ hp)
    simpa only [mul_one] using h₁.sub h₀
  rwa [he] at hout

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
