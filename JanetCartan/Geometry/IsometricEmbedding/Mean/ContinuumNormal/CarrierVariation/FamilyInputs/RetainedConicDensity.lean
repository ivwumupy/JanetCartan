module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Canonical

/-!
# Original density class on the retained positive conic family

The two labels below are the actual retained scalar ODE footpoints, composed
with the genuine conic inverse. The positive-reference immersion comparison
supplies their small differences. Constants precede tolerance and density,
and the original fixed-low density budget is retained.

Consumer: the positive-reference weighted matrix assembly in `FamilyInputs`.
Sources: `app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`,
and `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol
open WideDensity AmplitudeDifference.PrimitiveDensity

private theorem norm_le_reference_add_one {E H : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set E} (hS : IsCompact S) {f f₀ : E → H} (m : ℕ)
    (hf : ∀ p ∈ S, ContDiffAt ℝ ∞ f p) (hf₀ : ∀ p ∈ S, ContDiffAt ℝ ∞ f₀ p)
    (hd : cNorm S m (f - f₀) ≤ 1) : cNorm S m f ≤ cNorm S m f₀ + 1 := by
  have h := cNorm_add_le_of_contDiffAt (r := m) hS
    (fun p hp ↦ ((hf p hp).sub (hf₀ p hp)).of_le (by simp))
    (fun p hp ↦ (hf₀ p hp).of_le (by simp))
  simp only [Pi.add_def, sub_add_cancel] at h
  change cNorm S m f ≤ cNorm S m (f - f₀) + cNorm S m f₀ at h
  linarith only [h, hd]

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}

/-- Quantitative substitution of both actual ODE labels at a moving conic
inverse. The outer-field and inverse differences are the primitive conclusions
of `exists_retained_conic_primitives_sub_tolerance`; this deduction does not
assume continuity of a density or replace its ODE footpoint by the Hamilton
transport map. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_retained_conic_footpoints_sub_le
    (D : CoefficientNormCharts n) (hRc : 0 < Rc) (hτ : 0 < τ)
    (hSflow : MapsTo (densityCoordinates T) D.field.carrier
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {F₀ : Euclidean n → Euclidean N}
    (c₀ : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F₀)
    {Ki : Set (InputVariables n)} {Q Ωi : Set (Variables n × Euclidean 2)}
    (hKi : IsCompact Ki) (hQ : IsCompact Q) (hΩi : IsOpen Ωi) (hQΩi : Q ⊆ Ωi)
    (hend : ∀ side, MapsTo (densityEndpoint side) Ki D.field.carrier)
    (u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (hu₀ : ContDiffOn ℝ ∞ u₀ Ωi) (hrange₀ : MapsTo (inverseCoordinates u₀) Q Ki)
    (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (d : ℝ),
      0 ≤ d → d ≤ 1 → ContDiffOn ℝ ∞ u Ωi → MapsTo (inverseCoordinates u) Q Ki →
      cNorm D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) ≤ d →
      cNorm Q m (inverseCoordinates u - inverseCoordinates u₀) ≤ d →
      let g := fun side p ↦ densityFootpoint T c.inverse (densityEndpoint side (inverseCoordinates u p))
      let g₀ := fun side p ↦ densityFootpoint T c₀.inverse (densityEndpoint side (inverseCoordinates u₀ p))
      (∀ side p, p ∈ Q → ContDiffAt ℝ ∞ (g side) p ∧ ContDiffAt ℝ ∞ (g₀ side) p) ∧
      ∀ side, cNorm Q m (g side - g₀ side) ≤ C * d := by
  have hS : IsCompact D.field.carrier := isCompact_closedBall _ _
  have hfoot {F : Euclidean n → Euclidean N}
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (p) (hp : p ∈ D.field.carrier) : ContDiffAt ℝ ∞ (densityFootpoint T c.inverse) p := by
    have hmem := (outputCylinder_spec hRc hτ).2 (hSflow hp)
    exact c.densityFootpoint_spec.2.1.contDiffAt
      (((isOpen_Ioo.prod isOpen_ball).preimage (densityCoordinates T).continuous).mem_nhds hmem)
  have hi₀ (p) (hp : p ∈ Q) : ContDiffAt ℝ ∞ (inverseCoordinates u₀) p :=
    (inverseCoordinates_contDiffOn hu₀).contDiffAt (hΩi.mem_nhds (hQΩi hp))
  let M := cNorm Q m (inverseCoordinates u₀) + 1
  have hM : 0 ≤ M := add_nonneg (cNorm_nonneg ..) zero_le_one
  have he (side : Bool) := exists_fixed_evaluation_bounds hQ hKi
    (fun _ _ ↦ (densityEndpoint_contDiff side).contDiffAt) m hM
  choose E hE he using he
  have hc (side : Bool) := exists_cNorm_comp_sub_le_fixed_reference hQ hS
    (hfoot c₀) m (hE side).le
  choose C hC hc using hc
  let A := C false * (1 + E false) + C true * (1 + E true)
  have hA : 0 < A := add_pos
    (mul_pos (hC false) (by linarith [hE false]))
    (mul_pos (hC true) (by linarith [hE true]))
  refine ⟨A, hA, ?_⟩
  intro F c u d hd hd1 hu hrange hfdiff hidiff g g₀
  have hi (p) (hp : p ∈ Q) : ContDiffAt ℝ ∞ (inverseCoordinates u) p :=
    (inverseCoordinates_contDiffOn hu).contDiffAt (hΩi.mem_nhds (hQΩi hp))
  have hiM : cNorm Q m (inverseCoordinates u) ≤ M :=
    norm_le_reference_add_one hQ m hi hi₀ (hidiff.trans hd1)
  have hi₀M : cNorm Q m (inverseCoordinates u₀) ≤ M := by
    dsimp only [M]; linarith
  have hev (side : Bool) := he side (inverseCoordinates u) (inverseCoordinates u₀)
    d hd hi hi₀ hrange hrange₀ hiM hi₀M hidiff
  have hsm (side) (p) (hp : p ∈ Q) :
      ContDiffAt ℝ ∞ (g side) p ∧ ContDiffAt ℝ ∞ (g₀ side) p :=
    ⟨(hfoot c _ (hend side (hrange hp))).comp
      (f := densityEndpoint side ∘ inverseCoordinates u) p (hev side |>.1 p hp).1,
      (hfoot c₀ _ (hend side (hrange₀ hp))).comp
      (f := densityEndpoint side ∘ inverseCoordinates u₀) p (hev side |>.1 p hp).2⟩
  refine ⟨hsm, ?_⟩
  intro side
  have hb := hc side (densityFootpoint T c.inverse)
    (densityEndpoint side ∘ inverseCoordinates u)
    (densityEndpoint side ∘ inverseCoordinates u₀) ((1 + E side) * d)
    (mul_nonneg (by linarith [hE side]) hd) (hfoot c)
    (fun p hp ↦ (hev side |>.1 p hp).1) (fun p hp ↦ (hev side |>.1 p hp).2)
    ((hend side).comp hrange) ((hend side).comp hrange₀)
    (hev side).2.1 (hev side).2.2.1
    (hfdiff.trans (by nlinarith [hE side])) ((hev side).2.2.2.trans (by nlinarith))
  change cNorm Q m (g side - g₀ side) ≤ C side * ((1 + E side) * d) at hb
  have hle : C side * (1 + E side) ≤ A := by
    cases side
    · exact le_add_of_nonneg_right (mul_nonneg (hC true).le (by linarith [hE true]))
    · exact le_add_of_nonneg_left (mul_nonneg (hC false).le (by linarith [hE false]))
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hle hd])


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

/-- A density-uniform positive-reference tolerance for BOTH retained ODE
labels after genuine conic inverse substitution. All finite primitive and
composed-label differences are derived from the immersion difference; the
wider density has only its original low norm, with `m + 1 ≤ d₀`. The original
scalar label ball is retained even when its radius differs from the carrier
tube. The common conic domain and gap premises remain the geometric producer's
obligation on these SAME maps. Source: `app:ch_background:prop:bg-frame`,
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_retained_conic_densityPair_comparison
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
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.field.carrier K)
    (hSflow : MapsTo (densityCoordinates T) D.field.carrier
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
    (hfoot₀ : MapsTo (densityFootpoint T c₀.inverse) D.field.carrier
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    (hDV : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    {Ki W Bi : Set (InputVariables n)} {Q Ωi : Set (Variables n × Euclidean 2)}
    (hKi : IsCompact Ki) (hconv : Convex ℝ Ki) (hW : IsOpen W) (hKiW : Ki ⊆ W)
    (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hQ : IsCompact Q) (hΩi : IsOpen Ωi) (hQΩi : Q ⊆ Ωi)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (hu₀ : ContDiffOn ℝ ∞ u₀ Ωi)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (slice : TransportSliceCoordinates n)
    (hrange₀ : MapsTo (inverseCoordinates u₀) Q Ki)
    (heq₀ : ∀ p ∈ Ωi, transportAveragedGradient (transportPosition T c₀.Q)
      (inverseCoordinates u₀ p) = p.1.2.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hgap₀ : ∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian slice (transportPosition T c₀.Q) p)
    (hend : ∀ side, MapsTo (densityEndpoint side) Ki D.field.carrier)
    (m : ℕ) :
    let L := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
    let g₀ := fun side p ↦ densityFootpoint T c₀.inverse (densityEndpoint side (inverseCoordinates u₀ p))
    ∃ C > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ δ > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) D.field.carrier
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      ContDiffOn ℝ ∞ u Ωi → MapsTo (inverseCoordinates u) Q Ki →
      (∀ p ∈ Ωi, transportAveragedGradient (transportPosition T c.Q)
        (inverseCoordinates u p) = p.1.2.2) →
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T c.Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian slice (transportPosition T c.Q) p) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (m + 6)) (F - F₀) < δ →
      ∀ d₀ : ℕ, m + 1 ≤ d₀ → ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      let g := fun side p ↦ densityFootpoint T c.inverse (densityEndpoint side (inverseCoordinates u p))
      (∀ side p, p ∈ Q → ContDiffAt ℝ ∞ (g side) p ∧ ContDiffAt ℝ ∞ (g₀ side) p) ∧
      (∀ side, MapsTo (g side) Q L ∧ MapsTo (g₀ side) Q L) ∧
      (∀ side, cNorm Q m (g side) ≤ C ∧ cNorm Q m (g₀ side) ≤ C ∧
        cNorm Q m (g side - g₀ side) < ε) ∧
      cNorm Q m (densityPair v g) ≤ C ∧ cNorm Q m (densityPair v g₀) ≤ C ∧
      cNorm Q m (densityPair v g - densityPair v g₀) < ε := by
  dsimp only
  let L := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
  let g₀ := fun side p ↦ densityFootpoint T c₀.inverse (densityEndpoint side (inverseCoordinates u₀ p))
  obtain ⟨Cg, hCg, hlabels⟩ := exists_retained_conic_footpoints_sub_le T D hRc hτ
    hSflow c₀ hKi hQ hΩi hQΩi hend u₀ hu₀ hrange₀ m
  let Mv := cNorm Q m (g₀ false) + cNorm Q m (g₀ true) + 1
  have hMv : 0 ≤ Mv := by
    dsimp only [Mv]
    exact add_nonneg (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)) zero_le_one
  have hMv₀ (side) : cNorm Q m (g₀ side) + 1 ≤ Mv := by
    cases side <;> dsimp only [Mv] <;> linarith only [cNorm_nonneg Q m (g₀ false), cNorm_nonneg Q m (g₀ true)]
  obtain ⟨Cv, hCv, hdensity⟩ := exists_densityPair_sub_bound hQ
    (isCompact_closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
    (convex_closedBall _ _) m hMv
  refine ⟨1 + Mv + Cv, by positivity, ?_⟩
  intro ε hε
  let tol := min 1 (min (1 / Cg) (ε / ((1 + Cv) * Cg)))
  have htol : 0 < tol := lt_min zero_lt_one (lt_min (div_pos zero_lt_one hCg)
    (div_pos hε (mul_pos (by linarith) hCg)))
  obtain ⟨δ, hδ, hprimitive⟩ := exists_retained_conic_primitives_sub_tolerance
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx D hSK hSflow
    c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀
    hDV hKi hconv hW hKiW hBi hWBi hQ hΩi hQΩi hIt hIIt hsegT hseg u₀ hu₀ A slice
    hrange₀ heq₀ hgap hgap₀ m htol
  refine ⟨δ, hδ, ?_⟩
  intro F c u hF him hrank hlow hmet hnormal hfoot hu hrange heq hdiffGap hJgap hsmall
    d₀ horder v hv hvm
  let g := fun side p ↦ densityFootpoint T c.inverse (densityEndpoint side (inverseCoordinates u p))
  have hp := hprimitive F c u hF him hrank hlow hmet hnormal hfoot hu hrange heq hdiffGap hJgap hsmall
  let d := cNorm D.field.carrier (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q) +
    cNorm D.field.carrier m (c.normal initial - c₀.normal initial) +
    cNorm D.field.carrier m (c.reduced - c₀.reduced) +
    cNorm D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) +
    cNorm Ki m (augmentedTransportGradient (transportPosition T c.Q) -
      augmentedTransportGradient (transportPosition T c₀.Q)) +
    cNorm Q m (inverseCoordinates u - inverseCoordinates u₀) +
    cNorm Ki m (transportAbsoluteJacobian slice (transportPosition T c.Q) -
      transportAbsoluteJacobian slice (transportPosition T c₀.Q)) +
    cNorm Ki m ((fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c.Q) p)⁻¹) -
      (fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c₀.Q) p)⁻¹))
  change d < tol at hp
  have h₁ := cNorm_nonneg D.field.carrier (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q)
  have h₂ := cNorm_nonneg D.field.carrier m (c.normal initial - c₀.normal initial)
  have h₃ := cNorm_nonneg D.field.carrier m (c.reduced - c₀.reduced)
  have h₄ := cNorm_nonneg D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)
  have h₅ := cNorm_nonneg Ki m (augmentedTransportGradient (transportPosition T c.Q) -
    augmentedTransportGradient (transportPosition T c₀.Q))
  have h₆ := cNorm_nonneg Q m (inverseCoordinates u - inverseCoordinates u₀)
  have h₇ := cNorm_nonneg Ki m (transportAbsoluteJacobian slice (transportPosition T c.Q) -
    transportAbsoluteJacobian slice (transportPosition T c₀.Q))
  have h₈ := cNorm_nonneg Ki m ((fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c.Q) p)⁻¹) -
    (fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c₀.Q) p)⁻¹))
  have hd : 0 ≤ d := by dsimp only [d]; linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  have hlabel := hlabels F c u d hd (hp.le.trans (min_le_left _ _)) hu hrange
    (by dsimp only [d]; linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈])
    (by dsimp only [d]; linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈])
  have hCd1 : Cg * d ≤ 1 := by
    have hh := hp.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    change d ≤ 1 / Cg at hh
    have hh' := (le_div_iff₀ hCg).mp hh
    nlinarith only [hh']
  have hCdε : (1 + Cv) * (Cg * d) < ε := by
    have hh := hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (lt_div_iff₀ (mul_pos (show 0 < 1 + Cv by linarith) hCg)).mp hh
    nlinarith only [hh']
  have hnorm (side) : cNorm Q m (g side) ≤ Mv :=
    (norm_le_reference_add_one hQ m (fun p hp ↦ (hlabel.1 side p hp).1)
      (fun p hp ↦ (hlabel.1 side p hp).2) ((hlabel.2 side).trans hCd1)).trans (hMv₀ side)
  have hnorm₀ (side) : cNorm Q m (g₀ side) ≤ Mv := by linarith only [hMv₀ side]
  have hrangeL (side) : MapsTo (g side) Q L ∧ MapsTo (g₀ side) Q L := by
    have hball : ball ((0 : Euclidean (n - 1)), z₀) (R / 16) ⊆ L :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    exact ⟨fun p hp ↦ hball (hfoot (hend side (hrange hp))),
      fun p hp ↦ hball (hfoot₀ (hend side (hrange₀ hp)))⟩
  have hvpair := hdensity v g g₀ (Cg * d) (mul_nonneg hCg.le hd) hv
    ((cNorm_mono_order horder).trans hvm)
    (fun side p hp ↦ (hlabel.1 side p hp).1) (fun side p hp ↦ (hlabel.1 side p hp).2)
    (fun side ↦ (hrangeL side).1) (fun side ↦ (hrangeL side).2)
    hnorm hnorm₀ hlabel.2
  refine ⟨hlabel.1, hrangeL, ?_, hvpair.2.1.trans (by linarith),
    hvpair.2.2.1.trans (by linarith), hvpair.2.2.2.trans_lt ?_⟩
  · intro side
    refine ⟨(hnorm side).trans (by linarith), (hnorm₀ side).trans (by linarith),
      (hlabel.2 side).trans_lt ?_⟩
    nlinarith only [hCdε, mul_nonneg hCv.le (mul_nonneg hCg.le hd)]
  · nlinarith only [hCdε, mul_nonneg hCg.le hd]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
