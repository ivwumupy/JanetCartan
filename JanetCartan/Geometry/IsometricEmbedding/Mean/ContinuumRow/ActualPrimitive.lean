module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.PositiveAmplitudeConstruction.LocalConstruction

/-!
# Construct the flow used by the canonical primitive budgets

This leaf discharges every coefficient, flow and scalar regularity premise of
`CanonicalCarrier.exists_canonical_primitive_controls` using the actual positive
transport construction. The flow domains and minor precede the geometric
budgets; the same flow is chosen before the initial scalar and all derivative
orders. Only containment of the supplied field chart in the constructed product
neighborhood and the original mask support remain explicit. The row assembly
must match this neighborhood to the supported conic geometry.

The result supplies primitive estimates, not the completed continuum row.
The original map C15 bound is supplied for histories by
`HistoryGeometry.exists_initialScale_for_carrier_low_bound`. Prepared-scalar
C15 bounds and identification with a retained full leading family remain
separate obligations of the parent construction.
Sources: `app:ch_background:eq:bg-mixed-input`, `bg-T`, and
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude ProjectedStressFrame FullPhaseCharts.ActualComparison
open ContinuumNormalReduction.TransportSymbol

/-- Construct the actual positive transport maps and instantiate the primitive
carrier budgets for them. The fixed geometric buffers are constructed, while all
flow, scalar, null-amplitude, normal, phase and detector estimates are proved
from the original immersion and initial-scalar budgets. Constants precede the
immersion, initial scalar and high derivative order. No carrier operator bound
is an input or a conclusion of this local construction (`bg-T`, `bg-mixed-input`). -/
theorem exists_actual_canonical_primitive_controls {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R τ : ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < τ ∧ τ ≤ R / 16 ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) ∧
      ∃ ε > (0 : ℝ),
      let X := ball (0 : Euclidean n) ε
      let V := ball (z 0, spectatorCenter z) ε
      ∀ (Dc : CoefficientNormCharts n) (_hregion : Dc.field.region ⊆ X ×ˢ V)
        {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
        (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
        (_hang : ContDiff ℝ ∞ (Function.uncurry angular))
        {Zp : Set CarrierParameter} (_hZp : IsCompact Zp)
        (_hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
        (_hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ Dc.field.carrier),
      ∀ (M₁₅ Mᵣ κmet κ : ℝ), 0 ≤ M₁₅ → 0 ≤ Mᵣ → 0 < κmet → 0 < κ →
      ∃ δ > 0, ∃ M > 0, ∃ Cmask ≥ 0, ∃ B : ℕ → ℝ, (∀ j, 1 ≤ B j) ∧
        ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
          (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
          cNorm K 15 F ≤ M₁₅ →
          (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
          (∀ x ∈ K, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
          cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let C := coordinates (adaptedCoordinates T.data.adapted)
        let p₀ := ((0 : Euclidean (n - 1)), z)
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen D ∧ Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D ∧
          D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) ∧
          (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) ∧
          (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            ContDiffOn ℝ ∞ initial (ball p₀ (R / 4)) →
            (∀ p ∈ ball p₀ (R / 8), 0 < initial p) →
            cNorm (closedBall p₀ (R / 8)) 15 initial ≤ Mᵣ →
          let α := carrierScalarAmplitude T Q F row col Φ Y initial
          let e := data T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          (∀ p ∈ ball p₀ (R / 8), α (T.data.adapted.embedding p.1, p.2) = initial p) ∧
          (∀ w ∈ C ⁻¹' D, 0 < α w) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
              carrierTransportPotential T Q F row col w * α w = 0) ∧
          ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col Φ Y initial)) (X ×ˢ V) ∧
          (∀ i : Fin n, ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
            quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)) i) (X ×ˢ V)) ∧
          StronglyMeasurable (Function.uncurry (carrierKernel e)) ∧
          (∀ x u, ‖carrierAmplitude e x u‖ ≤ Cmask * Real.sqrt ‖u.2‖) ∧
          ContDiffOn ℝ ∞ (transportPosition T Q) Dc.field.region ∧
          cNorm Dc.field.carrier 3 (transportPosition T Q) ≤ M ∧
          ∀ s, let Hhigh := 1 + cNorm K (s + 14) F +
            cNorm (closedBall p₀ (R / 8)) (s + 14) initial
          Dc.Controls s M (B s) Hhigh
            (TransportKernel.coefficientsOfCarrier e (FixedCutoffs.physical hr 1)) ∧
          1 + cNorm Dc.field.carrier (s + 2) (transportPosition T Q) ≤ B s * Hhigh := by
  obtain ⟨row, col, ρ, R, η, τ, g, hρ, hR, hη, hτ, _,
    hbuffer, hτR, hactual⟩ :=
    CurrentCoefficientProfiles.exists_local_positive_amplitude_before_geometry (N := N)
      hn hP T hK hKU hball z hz
  obtain ⟨ε, hε, ρdet, hρdet, hXK, hXU, hc, hLWbig, hregion, hphaseBig,
    hx, hc₀, hLaBig⟩ := exists_canonical_flow_buffers hP T hKU hball z hz hR hτ
  let X := ball (0 : Euclidean n) ε
  let V := ball (z 0, spectatorCenter z) ε
  have hX : IsOpen X := isOpen_ball
  have hV : IsOpen V := isOpen_ball
  refine ⟨row, col, ρ, R, τ, hρ, hR, hτ, hτR, hbuffer, ε, hε, ?_⟩
  dsimp only
  intro Dc hfieldRegion r hr hcell angular hang Zp hZp hangular hsupport
    M₁₅ Mᵣ κmet κ hM₁₅ hMᵣ hκmet hκ
  obtain ⟨haX, haV⟩ := coefficientNormCharts_ball_projections Dc hfieldRegion
  have haK := haX.trans hXK
  have hLW := hLWbig.mono_left (Dc.field.ball_subset.trans hfieldRegion)
  have hLa := hLaBig.mono_left (Dc.field.ball_subset.trans hfieldRegion)
  have hphaseRegion := hfieldRegion.trans hphaseBig
  let adet : Euclidean n × Euclidean 3 := (0, z)
  obtain ⟨A, H, hA, hH, hactual⟩ := hactual M₁₅ κmet κ hκmet hκ
  obtain ⟨δ, hδ, M, hM, Cmask, hCmask, B, hB, hcontrols⟩ :=
    exists_canonical_primitive_controls T hP hK hKU hball z hρ hR hτ hτR hbuffer
      A H hA hH Dc hX hV hXU haX haV haK hc hLW hregion hfieldRegion hphaseRegion
      adet hρdet hx hc₀ hLa hr hcell angular hang hZp hangular hsupport
      hM₁₅ hMᵣ hκmet hκ
  obtain ⟨_, _, _, _, hnormalSmooth⟩ := exists_projected_normalField_bounds T (N := N)
    hP hK hKU hball z hρ hR hτ hτR hbuffer A H hA hH
    Dc.field.center Dc.field.radius_pos hX hV hXU haX haV haK hc hLW hregion
    hM₁₅ hMᵣ hκmet hκ
  refine ⟨min η δ, lt_min hη hδ, M, hM, Cmask, hCmask, B, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hF4 : cNorm K 4 F ≤ M₁₅ := (cNorm_mono_order (by omega)).trans hFM
  obtain ⟨hlow, D, Φ, Y, hD, hsmall, hbig, _, _, _, hΦD, hYD, hΦ₀,
    hYΦ, hΦY, _, hYcarrier, _, _, hcoeff, hflow, hreg, hΦ, hY, _, _, _, hscalar⟩ :=
    hactual F hF hi hrank hF4 hmet hnormal (hclose.trans_le (min_le_left _ _))
  refine ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hΦ₀, hYΦ, hΦY, hYcarrier, ?_⟩
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hsmallNorm : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) ≤ cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) :=
    cNorm_mono_set_of_contDiffAt hball hK (fun x hx ↦
      ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))
  intro initial hinitial hpositive hinitialBound
  obtain ⟨hα, hb, hα₀, hαpos, _, htransport, _⟩ :=
    hscalar initial (hinitial.mono (ball_subset_ball (by linarith))) hpositive
  have hnorm := hnormalSmooth Q F rfl hF hi hrank hFM hmet hnormal row col D Φ Y initial
    hD hsmall hbig hΦD hYD hΦ hY hreg hcoeff hflow hinitial hα hb hinitialBound
  have hquad : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))) (X ×ˢ V) :=
    (quadratic_canonical_smooth T hP Q).mono (fun p hp ↦
      ⟨⟨hXU hp.1, (hc hp).1⟩, (hc hp).2⟩)
  refine ⟨hα, hα₀, hαpos, htransport, hnorm.1,
    (contDiffOn_piLp 2).mp hquad, ?_⟩
  exact hcontrols Q F rfl hF hi hrank hFM hmet hnormal
    (hsmallNorm.trans_lt (hclose.trans_le (min_le_right _ _))) row col D Φ Y initial
    hD hsmall hbig hΦD hYD hΦ hY hreg hcoeff hflow hinitial hα hb hinitialBound

end JanetCartan.ContinuumRow.CanonicalCarrier
