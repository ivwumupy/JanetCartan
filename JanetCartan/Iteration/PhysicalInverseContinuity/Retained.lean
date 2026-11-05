module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Fields
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficientBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ImmersionComparison

/-!
# Actual retained-immersion finite-jet kernel neighborhood

The kernel is the literal original `CanonicalCarrier.data`, with the supplied
original initial scalar and the same physical/angular/high masks. The existing
actual Hamilton/normal/ODE comparison supplies all varying-field differences.
Only eight immersion derivatives are needed here, independently of the finite
frequency radius and target tolerance. The frequency truncation appears only
in this estimate, not in the row or source. Consumer: strong fixed-reference raw
inverse continuity for `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInverseContinuity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol
open AmplitudeBound

private theorem norm_le_cNorm_zero_of_continuousOn
    {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set E} (hS : IsCompact S) {f : E → H} (hf : ContinuousOn f S)
    {p : E} (hp : p ∈ S) : ‖f p‖ ≤ cNorm S 0 f := by
  have hb : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ 0 f x‖) '' S) := by
    simpa only [norm_iteratedFDeriv_zero] using hS.bddAbove_image hf.norm
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_cNorm_of_bddAbove hb hp (le_refl 0)

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}

/-- An actual finite physical immersion-jet neighborhood gives arbitrary
finite-frequency kernel closeness for the same retained charts and initial
scalar. Every field difference is produced by the existing original-scalar
immersion comparison; none is assumed as an analytic continuity premise. -/
theorem exists_retained_carrierKernel_sub_tolerance
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
    (hSphase : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
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
    (hangular : ∀ z η, |angular z η| ≤ 1) (hhigh : ∀ ρ, |high ρ| ≤ 1)
    {Z : Set CarrierParameter} (hzero : ∀ z ∉ Z, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical hr 1) ×ˢ Z ⊆ D.field.carrier)
    {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) D.field.region
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 8 (F - F₀) < δ →
      ∀ (x : Torus n) (u : CarrierVariable n), ‖u.2‖ ≤ Λ →
        ‖carrierKernel (data T c.Q F row col c.forward c.inverse initial hr hcell angular high) x u -
          carrierKernel (data T c₀.Q F₀ row col c₀.forward c₀.inverse initial hr hcell angular high) x u‖ ≤ ε := by
  let S := D.field.carrier
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSV : S ⊆ D.field.region := D.field.ball_subset
  have hreg₀ := retained_originalScalar_coefficients_contDiffOn c₀ hP hRc hτ hKΩ hKU
    hF₀ hi₀ hrank₀ hSK hSflow hR initial hi hipos hfoot₀
  let Bν := cNorm S 0 (c₀.normal initial)
  let Bq := cNorm S 0 c₀.reduced
  have hBν : 0 ≤ Bν := cNorm_nonneg _ _ _
  have hBq : 0 ≤ Bq := cNorm_nonneg _ _ _
  let Lq := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  let L := 1 + ‖Lq‖
  have hL : 1 ≤ L := by dsimp [L]; linarith [norm_nonneg Lq]
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  let Mfield := 1 + Bν + L * (1 + Bq)
  have hLprod : 0 ≤ L * (1 + Bq) := by positivity
  have hMf : 0 ≤ Mfield := by dsimp [Mfield]; linarith only [hLprod, hBν]
  let Ckernel := Real.sqrt Λ * L * (Λ * Mfield ^ 3 + 3 * Mfield ^ 2)
  have hCkernel : 0 ≤ Ckernel := by dsimp [Ckernel]; positivity
  let t := min 1 (ε / (1 + Ckernel))
  have ht : 0 < t := lt_min zero_lt_one (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htε : t * (1 + Ckernel) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 1 + Ckernel)).mp (min_le_right _ _)
  obtain ⟨δ, hδ, hcompare⟩ := exists_originalScalar_immersion_sub_tolerance T hdomain hgeometry
    hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx hS
    (fun p hp ↦ hSK (hSV hp)) (fun p hp ↦ hSflow (hSV hp))
    c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos
    (fun p hp ↦ hfoot₀ (hSV hp)) 0 ht
  refine ⟨δ, hδ, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hsmall x u hη
  have hdiff := hcompare F c hF him hrank hlow hmet hnormal
    (fun p hp ↦ hfoot (hSV hp)) (by simpa only [show max 8 (0 + 6 : ℕ) = 8 by decide] using hsmall)
  have hreg := retained_originalScalar_coefficients_contDiffOn c hP hRc hτ hKΩ hKU
    hF him hrank hSK hSflow hR initial hi hipos hfoot
  have hY : ContinuousOn (transportPosition T c.Q - transportPosition T c₀.Q) S :=
    (((transportPosition_smooth T c.Q hP).mono hSphase).continuousOn.sub
      ((transportPosition_smooth T c₀.Q hP).mono hSphase).continuousOn).mono hSV
  have hνdiff : ContinuousOn (c.normal initial - c₀.normal initial) S :=
    (hreg.1.continuousOn.sub hreg₀.1.continuousOn).mono hSV
  have hqdiff : ContinuousOn (c.reduced - c₀.reduced) S :=
    (hreg.2.continuousOn.sub hreg₀.2.continuousOn).mono hSV
  have hparts : cNorm S 0 (transportPosition T c.Q - transportPosition T c₀.Q) ≤ t ∧
      cNorm S 0 (c.normal initial - c₀.normal initial) ≤ t ∧
      cNorm S 0 (c.reduced - c₀.reduced) ≤ t := by
    have hYmono := cNorm_mono_order (s := S)
      (f := transportPosition T c.Q - transportPosition T c₀.Q) (by omega : 0 ≤ 0 + 2)
    have hY0 := cNorm_nonneg S (0 + 2) (transportPosition T c.Q - transportPosition T c₀.Q)
    have hν0 := cNorm_nonneg S 0 (c.normal initial - c₀.normal initial)
    have hq0 := cNorm_nonneg S 0 (c.reduced - c₀.reduced)
    have hf0 := cNorm_nonneg S 0 (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)
    exact ⟨by linarith only [hdiff, hYmono, hν0, hq0, hf0],
      by linarith only [hdiff, hY0, hq0, hf0], by linarith only [hdiff, hY0, hν0, hf0]⟩
  by_cases hm : FixedCutoffs.physical hr 1 (centeredTorusRepresentative x) = 0
  · by_cases hchart : x ∈ PeriodicLocalL2.torusChart (closedBall (0 : Euclidean n) (4 * r)) <;>
      simpa [carrierKernel, carrierAmplitude, data, hm, hchart] using hε.le
  by_cases hz : u.1 ∈ Z
  · let p : Euclidean n × CarrierParameter := (centeredTorusRepresentative x, u.1)
    have hp : p ∈ S := hsupport ⟨subset_tsupport _ hm, hz⟩
    have hνd : ‖c.normal initial p - c₀.normal initial p‖ ≤ t :=
      (norm_le_cNorm_zero_of_continuousOn hS hνdiff hp).trans hparts.2.1
    have hqd : ‖c.reduced p - c₀.reduced p‖ ≤ t :=
      (norm_le_cNorm_zero_of_continuousOn hS hqdiff hp).trans hparts.2.2
    have hνbase : ‖c₀.normal initial p‖ ≤ Bν :=
      norm_le_cNorm_zero_of_continuousOn hS (hreg₀.1.continuousOn.mono hSV) hp
    have hqbase : ‖c₀.reduced p‖ ≤ Bq :=
      norm_le_cNorm_zero_of_continuousOn hS (hreg₀.2.continuousOn.mono hSV) hp
    have hνcur : ‖c.normal initial p‖ ≤ 1 + Bν := by
      have hh := norm_add_le (c.normal initial p - c₀.normal initial p) (c₀.normal initial p)
      rw [sub_add_cancel] at hh
      linarith only [hh, hνd, hνbase, ht1]
    have hqcur : ‖c.reduced p‖ ≤ 1 + Bq := by
      have hh := norm_add_le (c.reduced p - c₀.reduced p) (c₀.reduced p)
      rw [sub_add_cancel] at hh
      linarith only [hh, hqd, hqbase, ht1]
    have hνM : ‖c.normal initial p‖ ≤ Mfield := hνcur.trans (by dsimp [Mfield]; linarith only [hLprod, hBν])
    have hνM₀ : ‖c₀.normal initial p‖ ≤ Mfield := hνbase.trans (by dsimp [Mfield]; linarith only [hLprod, hBν])
    have hqM : ‖Lq (c.reduced p)‖ ≤ Mfield := by
      calc
        ‖Lq (c.reduced p)‖ ≤ ‖Lq‖ * ‖c.reduced p‖ := Lq.le_opNorm _
        _ ≤ L * (1 + Bq) := mul_le_mul (by dsimp [L]; linarith [norm_nonneg Lq])
          hqcur (norm_nonneg _) hL0
        _ ≤ Mfield := by dsimp [Mfield]; linarith only [hLprod, hBν]
    have hqd' : ‖Lq (c.reduced p) - Lq (c₀.reduced p)‖ ≤ L * t := by
      rw [← map_sub]
      exact (Lq.le_opNorm _).trans (mul_le_mul
        (by dsimp [L]; linarith [norm_nonneg Lq]) hqd (norm_nonneg _) hL0)
    have htL : t ≤ L * t := by nlinarith only [ht.le, hL]
    have hYd : ‖transportPosition T c.Q p - transportPosition T c₀.Q p‖ ≤ L * t :=
      ((norm_le_cNorm_zero_of_continuousOn hS hY hp).trans hparts.1).trans htL
    have hperiodic : |FixedCutoffs.periodic hr hcell 1 x| ≤ 1 := by
      rw [abs_of_nonneg (FixedCutoffs.periodic_mem_Icc hr hcell 1 x).1]
      exact (FixedCutoffs.periodic_mem_Icc hr hcell 1 x).2
    have hmaskBound : |FixedCutoffs.periodic hr hcell 1 x *
        angular u.1 (‖u.2‖⁻¹ • u.2) * high ‖u.2‖| ≤ 1 := by
      rw [abs_mul, abs_mul]
      have hleft : |FixedCutoffs.periodic hr hcell 1 x| * |angular u.1 (‖u.2‖⁻¹ • u.2)| ≤ 1 :=
        (mul_le_mul hperiodic (hangular _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      exact (mul_le_mul hleft (hhigh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hk := norm_carrierKernel_sub_le_of_field_differences
      (data T c.Q F row col c.forward c.inverse initial hr hcell angular high)
      (data T c₀.Q F₀ row col c₀.forward c₀.inverse initial hr hcell angular high)
      rfl x u hMf (mul_nonneg hL0 ht.le) rfl hmaskBound hYd hνM hνM₀
      (by rw [reducedCovector_data]; exact hqM)
      (hνd.trans htL) (by rw [reducedCovector_data, reducedCovector_data]; exact hqd')
    calc
      _ ≤ Real.sqrt ‖u.2‖ * (L * t) * (‖u.2‖ * Mfield ^ 3 + 3 * Mfield ^ 2) := hk
      _ ≤ Real.sqrt Λ * (L * t) * (Λ * Mfield ^ 3 + 3 * Mfield ^ 2) := by gcongr
      _ = Ckernel * t := by dsimp [Ckernel]; ring
      _ ≤ ε := by nlinarith only [htε, ht.le]
  · simpa [carrierKernel, carrierAmplitude, data, hzero u.1 hz _] using hε.le

end JanetCartan.PhysicalInverseContinuity
