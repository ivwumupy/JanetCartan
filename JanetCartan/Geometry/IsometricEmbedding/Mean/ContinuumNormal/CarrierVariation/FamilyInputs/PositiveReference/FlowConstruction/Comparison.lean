module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# Comparison of the actual retained null charts

Instantiate `NullFlowDependence.exists_cNorm_carrier_transport_sub_lt` with
all the witnesses of the constructed charts. The resulting estimate includes
the literal density footpoint. Then instantiate `CoefficientDependence` to
reduce the input to frame, Hamilton-gradient and immersion differences.
Consumer: the parent's final immersion comparison, for
`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow

private theorem add_controlled_error_lt {a b c d e B ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (he : e ≤ B * b) (hs : (a + b + c + d) * (B + 1) < ε) :
    a + b + c + d + e < ε := by
  have hb : b ≤ a + b + c + d := by linarith
  calc
    a + b + c + d + e ≤ (a + b + c + d) + B * b := add_le_add le_rfl he
    _ ≤ (a + b + c + d) + B * (a + b + c + d) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hB)
    _ = (a + b + c + d) * (B + 1) := by ring
    _ < ε := hs

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ} {row col : Fin n}

/-- Fixed compact inner output cylinder, chosen before the order or tolerance
in `app:ch_background:prop:bg-frame`. It lies strictly inside the common
inverse cylinder, so the same set also supports forward comparisons. -/
def outputCylinder (p₀ : Euclidean (n - 1) × Euclidean 3) (R τ : ℝ) :
    Set (ℝ × (Euclidean (n - 1) × Euclidean 3)) :=
  Icc (-(τ / 2)) (τ / 2) ×ˢ closedBall p₀ (R / 64)

/-- The constructed cylinder is compact and contained in the common domain
of every retained inverse (`app:ch_waves:thm:leading`). -/
theorem outputCylinder_spec (hR : 0 < R) (hτ : 0 < τ) :
    IsCompact (outputCylinder p₀ R τ) ∧
    outputCylinder p₀ R τ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 32) := by
  refine ⟨isCompact_Icc.prod (isCompact_closedBall _ _), ?_⟩
  rintro ⟨t, p⟩ ⟨ht, hp⟩
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
    closedBall_subset_ball (by linarith : R / 64 < R / 32) hp⟩

/-- Primitive coefficient differences control the SAME retained forward map,
inverse, literal scalar and density footpoint on fixed compact output sets.
Every ODE premise is discharged by the constructed chart fields; no flow
comparison is assumed. Source: `app:ch_waves:thm:leading`,
`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem Chart.exists_coefficients_transport_sub_tolerance
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K)
    (hτeq : τ = existenceTime R (liftedLowBound T M) / 4)
    {KΦ KY : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hKΦ : KΦ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
    (hKYc : IsCompact KY) (hKY : KY ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 32))
    {Kphysical : Set (Euclidean n × Euclidean 3)}
    {Kcarrier : Set (Euclidean n × ContinuumRow.CarrierParameter)}
    (hKphysical : IsCompact Kphysical) (hKcarrier : IsCompact Kcarrier)
    (hphysical : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)) Kphysical KY)
    (hcarrier : MapsTo (densityCoordinates T) Kcarrier KY)
    {F₀ : Euclidean n → Euclidean N} (c₀ : Chart T Ω K p₀ R M τ row col F₀)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball p₀ (R / 8)))
    (hipos : ∀ p ∈ ball p₀ (R / 8), 0 < initial p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N) (c : Chart T Ω K p₀ R M τ row col F),
      cNorm K m (carrierTransportDirection T c.Q row col -
        carrierTransportDirection T c₀.Q row col) +
      cNorm K m (carrierTransportPotential T c.Q F row col -
        carrierTransportPotential T c₀.Q F₀ row col) < δ →
      (∀ w ∈ Kphysical, 0 < c.scalar initial w) ∧
      (∀ w ∈ Kcarrier, 0 < c.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) ∧
      cNorm KΦ m (c.forward - c₀.forward) + cNorm KY m (c.inverse - c₀.inverse) +
        cNorm Kphysical m (c.scalar initial - c₀.scalar initial) +
        cNorm Kcarrier m ((fun w ↦ c.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) -
          (fun w ↦ c₀.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2))) +
        cNorm Kcarrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε := by
  obtain ⟨B, hB, hb⟩ := exists_densityFootpoint_sub_bound T hKcarrier hKYc hcarrier
  have hB' : 0 < B m + 1 := by linarith [hB m]
  obtain ⟨q, δ, hδ, hq, hcompare⟩ :=
    NullFlowDependence.exists_cNorm_carrier_transport_sub_lt T hΩ hK hKΩ hR hM
      hbuffer hτeq hKΦ hKYc hKY hKphysical hKcarrier hphysical hcarrier
      c₀.Q F₀ row col c₀.direction_smooth c₀.potential_smooth c₀.direction_bound
      c₀.domain_open c₀.small_subset c₀.subset_big c₀.forward_smooth c₀.inverse_smooth
      c₀.forward_range c₀.inverse_range c₀.initial c₀.ode c₀.forward_inverse
      initial hi hipos m (div_pos hε hB')
  subst q
  refine ⟨δ, hδ, ?_⟩
  intro F c hsmall
  have hd := cNorm_nonneg K m (carrierTransportDirection T c.Q row col -
    carrierTransportDirection T c₀.Q row col)
  have hc := cNorm_nonneg K m (carrierTransportPotential T c.Q F row col -
    carrierTransportPotential T c₀.Q F₀ row col)
  obtain ⟨hpos, hpos', hout⟩ := hcompare c.Q F c.forward c.inverse c.D
    c.direction_smooth c.potential_smooth c.direction_bound c.domain_open c.small_subset
    c.subset_big c.forward_smooth c.inverse_smooth c.forward_range c.inverse_range
    c.initial c.ode c.forward_inverse
      ((le_add_of_nonneg_right hc).trans_lt hsmall)
      ((le_add_of_nonneg_left hd).trans_lt hsmall)
  have hfoot := hb c.inverse c₀.inverse
    (fun w hw ↦ c.inverse_smooth.contDiffAt (c.domain_open.mem_nhds (c.small_subset (hKY hw))))
    (fun w hw ↦ c₀.inverse_smooth.contDiffAt (c₀.domain_open.mem_nhds (c₀.small_subset (hKY hw)))) m
  refine ⟨hpos, hpos', ?_⟩
  have he := (lt_div_iff₀ hB').mp hout
  dsimp only [Chart.scalar]
  exact add_controlled_error_lt (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
    (cNorm_nonneg _ _ _) (hB m).le hfoot he

/-- Instantiation of the published primitive coefficient implication and ODE
comparison for the retained charts. Only frame, actual Hamilton-gradient and
immersion differences remain. The parent's Hamilton comparison is the producer
of the gradient term; no flow/output continuity is a premise. Source:
`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem Chart.exists_primitive_transport_sub_tolerance
    {c C : ℝ} (hP : P.IsValid c C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K)
    (hτeq : τ = existenceTime R (liftedLowBound T M) / 4)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T) (hx : MapsTo Prod.fst K KF)
    {Kphysical : Set (Euclidean n × Euclidean 3)}
    {Kcarrier : Set (Euclidean n × ContinuumRow.CarrierParameter)}
    (hKphysical : IsCompact Kphysical) (hKcarrier : IsCompact Kcarrier)
    (hphysical : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted))
      Kphysical (outputCylinder p₀ R τ))
    (hcarrier : MapsTo (densityCoordinates T) Kcarrier (outputCylinder p₀ R τ))
    {F₀ : Euclidean n → Euclidean N} (c₀ : Chart T Ω K p₀ R M τ row col F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball p₀ (R / 8)))
    (hipos : ∀ p ∈ ball p₀ (R / 8), 0 < initial p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N) (c : Chart T Ω K p₀ R M τ row col F),
      ContDiffOn ℝ ∞ F U →
      cNorm KF (m + 1) (c.Q.1 - c₀.Q.1) +
        cNorm K (m + 1) (fun w ↦ T.carrierGradient c.Q w.1 w.2 -
          T.carrierGradient c₀.Q w.1 w.2) + cNorm KF (m + 2) (F - F₀) < δ →
      (∀ w ∈ Kphysical, 0 < c.scalar initial w) ∧
      (∀ w ∈ Kcarrier, 0 < c.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) ∧
      cNorm (outputCylinder p₀ R τ) m (c.forward - c₀.forward) +
        cNorm (outputCylinder p₀ R τ) m (c.inverse - c₀.inverse) +
        cNorm Kphysical m (c.scalar initial - c₀.scalar initial) +
        cNorm Kcarrier m ((fun w ↦ c.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) -
          (fun w ↦ c₀.scalar initial (w.1, ContinuumRow.CanonicalCarrier.parameter w.2))) +
        cNorm Kcarrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε := by
  have hτ : 0 < τ := by
    rw [hτeq]
    exact div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hM)) (by norm_num)
  obtain ⟨hL, hLi⟩ := outputCylinder_spec (p₀ := p₀) hR hτ
  have hLf : outputCylinder p₀ R τ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 8) :=
    fun _ hw ↦ ⟨(hLi hw).1, ball_subset_ball (by linarith) (hLi hw).2⟩
  obtain ⟨d, hd, hcompare⟩ := c₀.exists_coefficients_transport_sub_tolerance hΩ hK hKΩ
    hR hM hbuffer hτeq hLf hL hLi hKphysical hKcarrier hphysical hcarrier initial hi hipos m hε
  obtain ⟨δ, hδ, hcoeff⟩ := exists_carrier_coefficients_primitive_sub_tolerance T hP
    hK hKF hKFU hKU hx c₀.Q hF₀ hi₀ row col
    (fun w hw ↦ (c₀.null_spec w (hKΩ hw)).2.2.2.2) m hd
  exact ⟨δ, hδ, fun F c hF hsmall ↦ hcompare F c (hcoeff c.Q F hF hsmall)⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
