module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions

/-!
# The extended amplitude represents the original canonical kernel

The cap is chosen before the immersion, initial scalar and actual inverse
flow. The footpoint domain is proved from the retained `C¹` flow estimate
and time-zero identities. Hamilton conservation then identifies the same
footpoint with the phase derivative. Thus the fixed extensions preserve
the literal canonical kernel in `app:ch_background:eq:bg-T`.

Consumer: the final amplitude-profile instantiation of
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ActualFlow FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

set_option maxHeartbeats 400000 in
/-- The three fixed amplitude extensions and the supported phase extension
give EXACTLY the original canonical kernel. No footpoint-buffer or normal
factorization premise is added: these follow from the retained flow outputs
of `exists_projected_local_positive_amplitude` and the primitive low immersion
bound. The angular mask, half-order radial factor, measures and Fourier
normalization are unchanged (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-T`). -/
theorem exists_extendedScalarTransportData_kernel_cap
    {c C₁ : ℝ} (hP : P.IsValid c C₁)
    {K : Set (Euclidean n)} (hKU : K ⊆ U) (z₀ : Euclidean 3)
    {τ R H₁ : ℝ} (hτ : 0 < τ) (hR : 0 < R) (hH₁ : 0 < H₁) (M : ℝ) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ} (ha : 0 < a), a < cap →
      ∀ (hcell : 4 * a < 1 / 2) (θ₀ : Euclidean (n - 1)) {b : ℝ} (hb : 0 < b)
        (high : ℝ → ℝ)
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      let p₀ := ((0 : Euclidean (n - 1)), z₀)
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
      ContDiffOn ℝ ∞ F U → HasFullNormalRankOn F U →
      Q.1 = ProjectedStressFrame.projectedStress F → cNorm K 6 F ≤ M →
      Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      C ⁻¹' D ⊆ (ball 0 T.physicalRadius ∩ interior K) ×ˢ
        parameterInterior (3 * P.radius / 2) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ L) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ L) →
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      cNorm J 1 Φ + cNorm J 1 Y ≤ H₁ * (1 + cNorm K 6 F) →
      (∀ p ∈ L, Φ (0, p) = p) →
      (∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, Y (t, Φ (t, p)) = p) →
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) →
      (∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, (Φ (t, p)).2 = p.2) →
      (∀ q ∈ D, (Y q).2 = q.2.2) →
      (∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, HasDerivAt (fun s ↦ Φ (s, p))
        ((adaptedCoordinates T.data.adapted
          (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) →
      (∀ w ∈ C ⁻¹' D,
        carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
        carrierConullvector T Q row w ᵥ*
          reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
        carrierAdaptedDenominator T Q row col w ≠ 0) →
      ∀ Yext : Euclidean n × CarrierParameter → Euclidean (n - 1),
        EqOn Yext (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ a) →
        let d := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell
          (CanonicalConic.angularMask z₀ θ₀ ha hb) high
        carrierKernel (scalarTransportData d Yext
          (extendedInitialScalar z₀ hR initial)
          (extendedFlowFactor T Q F row col Φ Y z₀ ha)
          (extendedGeometricNormal T Q F col z₀ ha)) = carrierKernel d := by
  obtain ⟨cap, hcap, hbuffer⟩ := exists_supportedChart_initialBuffer_cap T (N := N)
    K z₀ hτ hR hH₁ M
  refine ⟨cap, hcap, ?_⟩
  intro a ha hacap hcell θ₀ b hb high Q F row col D Φ Y initial p₀ L J C
    hF hrank hQF hFM hsmall hgeom hΦD hYD hY hflow hinit hYΦ hinv
    hcarrier hYcarrier hode hnull Yext hYext
  have hsymm := projected_frame_symmetry T Q F hF hrank hQF
  obtain ⟨hwork, hfoot⟩ := hbuffer ha hacap F Φ Y hFM hY hflow hinit hYΦ
  have hsupport : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (supportedChart z₀ a) D := by
    intro p hp
    apply hsmall
    have hh := hwork hp
    exact ⟨⟨by linarith [hh.1.1], by linarith [hh.1.2]⟩,
      (mem_closedBall.mp hh.2).trans_lt (by linarith)⟩
  apply canonical_scalarTransportData_kernel_eq T Q F row col Φ Y initial ha hcell
    z₀ θ₀ hb high Yext (extendedInitialScalar z₀ hR initial)
    (extendedFlowFactor T Q F row col Φ Y z₀ ha)
    (extendedGeometricNormal T Q F col z₀ ha) hYext
  intro p hp
  have he := odeInitialPoint_eq_transportPosition T Q row col hP hKU hsymm hτ Φ Y
    hgeom hΦD hYD hinit hinv hcarrier hYcarrier hode hnull (hsupport hp)
  have hr : extendedInitialScalar z₀ hR initial (p.2, Yext p) =
      initialScalar initial (p.2, Yext p) := by
    apply (extendedInitialScalar_eventuallyEq z₀ hR initial ?_).eq_of_nhds
    rw [hYext hp, ← he]
    exact hfoot hp
  have hfloweq := (extendedFlowFactor_eventuallyEq T Q F row col Φ Y z₀ ha
    (p := (p.2, p.1)) hp).eq_of_nhds
  have hnormeq := (extendedGeometricNormal_eventuallyEq T Q F col z₀ ha
    (p := (p.2, p.1)) hp).eq_of_nhds
  rw [hr, hfloweq, hnormeq, hYext hp]
  exact (normalField_eq_initialScalar_transportPosition T Q row col hP hKU hsymm hτ Φ Y
    hgeom hΦD hYD hinit hinv hcarrier hYcarrier hode hnull F initial (hsupport hp)).symm

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
