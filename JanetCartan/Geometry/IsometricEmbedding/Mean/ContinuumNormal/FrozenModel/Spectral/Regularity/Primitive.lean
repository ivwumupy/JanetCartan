module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Coefficients

/-!
# Primitive regularity and the frozen Jacobian quotient

These are the concrete inputs to spectator integrability in the frozen step
of `app:ch_background:prop:bg-frame`. The geometric hypotheses are precisely
outputs of `exists_frozen_conic_inputs`. The determinant quotient is bounded
from the retained positive gap and the proved radial scaling identity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

include hP hr har hcarrier

omit T Q hηb ha in
/-- The original frozen input labels are in the coefficient domain, using
only the retained carrier buffer (`app:ch_background:eq:bg-Nsigma`). -/
theorem frozenInputDomain_carrier_subset :
    MapsTo (fun p : InputVariables n ↦ p.2.1) (frozenInputDomain z₀ ηb r (6 * a))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
  intro p hp i
  have hz := carrierInterior_of_frozenInputDomain hr har hcarrier hp i
  exact hz.trans_le (by linarith [hP.1])

omit T Q hηb in
/-- The compact support of the original angular mask stays in the seed
coefficient domain (`app:ch_background:defn:bg-row`). -/
theorem frozenCarrierSupport_subset :
    carrierSupport z₀ (r := a) ⊆ parameter ⁻¹' parameterInterior (2 * P.radius) := by
  intro z hz i
  have hsmall : a / 2 ≤ 3 * r := by linarith
  have hm := hcarrier (a := (z.2, z.1))
    ⟨closedBall_subset_closedBall hsmall hz.2,
      closedBall_subset_closedBall hsmall hz.1⟩ i
  change |parameter z i| < 3 * P.radius / 2 at hm
  exact hm.trans_le (by linarith [hP.1])

variable
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ)

local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)

include hP hηb hr har hcarrier hf hInv htrans hcJ

/-- All fields of the existing primitive regularity interface are proved
for the literal unit-initial frozen coefficients (`new:lem:scaling`). -/
theorem frozenPrimitiveRegularity_unit
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3) :
    PrimitiveRegularity
      (uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
        (angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1)
        FixedCutoffs.highFrequency) J₀ (frozenInputDomain z₀ ηb r (6 * a)) := by
  have hm := frozenInputDomain_carrier_subset (ηb := ηb) hP hr har hcarrier
  have hn := (frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).comp
    contDiffOn_snd.fst hm
  have hq := (PiLp.contDiff_ofLp.comp_contDiffOn (frozenSeedDetector_smooth T Q hP)).comp
    contDiffOn_snd.fst hm
  exact ⟨contDiffOn_const, contDiffOn_const,
    angularMask_smooth z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1,
    FixedCutoffs.highFrequency_smooth, hn, hn,
    contDiffOn_pi.mp hq, contDiffOn_pi.mp hq,
    frozenJacobian_smooth T Q hP hηb hr har hcarrier hInv htrans hf hcJ,
    fun _ hp ↦ (frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hp).ne',
    fun _ hp ↦ hp.2.2.1⟩

/-- Uniform boundedness of the exact half-order/Jacobian quotient.
Its constant is the local determinant gap divided by the fixed reference
covector norm, with no frequency-dependent lower-bound premise
(`app:ch_background:eq:bg-jacobian`). -/
theorem frozenJacobian_quotient_le {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r (6 * a)) :
    ‖p.2.2‖ / J₀ p ≤ ‖ηb‖ / cJ := by
  have hμ := norm_pos_iff.mpr hηb
  have hη : 0 < ‖p.2.2‖ := norm_pos_iff.mpr hp.2.2.1
  have hw : radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2) ∈
      dataBox z₀ ηb (2 * r) :=
    prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (normalizedInput_mem_dataSet (u := (p.2.1.1, p.2.2)) hηb hr hp.2)
  have hl := (hInv.differential_bounds (p.2.1.2, 0, 0) hp.1 _ hw).2.2
  change cJ ≤ adaptedJacobian T Q (p.2.1.2, 0, 0)
    (radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2)) at hl
  rw [adaptedJacobian_radialScale T Q hηb hr hf hInv htrans (p := (p.2.1.2, 0, 0)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2
    (div_pos hμ hη)] at hl
  have hd := adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf (p := (p.2.1.2, 0, 0)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2
  have he := frozenJacobian_eq_origin T Q hP hr har hcarrier (adaptedSliceCoordinates T) hp
  rw [transportAbsoluteJacobian_eq_adaptedJacobian T Q (originInput p) hd] at he
  change J₀ p = adaptedJacobian T Q (p.2.1.2, 0, 0) (p.2.1.1, p.2.2) at he
  rw [← he] at hl
  have hj := frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hp
  apply (div_le_div_iff₀ hj hcJ).mpr
  have hl' := (le_div_iff₀ hη).mp
    (show cJ ≤ ‖ηb‖ * J₀ p / ‖p.2.2‖ by simpa [div_mul_eq_mul_div] using hl)
  nlinarith

end JanetCartan.ContinuumNormal.FrozenModel
