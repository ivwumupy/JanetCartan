module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.DirectionComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.ScalarFormula

/-!
# Primitive coefficients control the same positive null transport

This is the conditional coefficient implication consumed by
`FamilyInputs.PositiveReference` in `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'. The equations, low bounds, original
buffers and smoothness are supplied by `ActualAmplitude.UniformFlow`, inside
`ActualAmplitude.LocalConstruction` (`app:ch_waves:thm:leading`). The parent
must instantiate them and prove immersion-to-direction/potential comparison.

The initial scalar is fixed and smooth on the original open label ball, which
contains every compact label buffer selected in the proof. A positive initial
scalar, including one, is retained as such. This implication does not establish
the parent's immersion-level theorem or uniformity over the wider density class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Finite-order differences of the primitive direction and potential control
the SAME retained `Φ`, inverse ODE map `Y`, and literal `carrierScalarAmplitude`,
on fixed compact adapted, physical and carrier sets. The order `q = m` and
positive threshold are chosen before the varying frame, immersion and maps.

All flow comparisons follow from the ODE, initial values and inverse identity,
including uniqueness of the independent comparison lifts. All scalar
comparisons follow from the characteristic integral/exponential formula.
The common buffers, low norm, smoothness, initial/range/ODE/inverse premises
are produced by `exists_uniform_actual_flow_chart`; potential smoothness and
the initial scalar are the inputs of `exists_projected_local_positive_amplitude`.
The parent's immersion comparison and actual instantiation remain separate.
Source: `app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4',
and `app:ch_waves:thm:leading`. -/
theorem exists_cNorm_carrier_transport_sub_lt
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ}
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
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F₀ : Euclidean n → Euclidean N) (row col : Fin n)
    (hd₀ : ContDiffOn ℝ ∞ (carrierTransportDirection T Q₀ row col) Ω)
    (hc₀ : ContDiffOn ℝ ∞ (carrierTransportPotential T Q₀ F₀ row col) Ω)
    (hlow₀ : cNorm K 1 (carrierTransportDirection T Q₀ row col) ≤ M)
    {D₀ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    {Φ₀ Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    (hD₀ : IsOpen D₀)
    (hsmall₀ : Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D₀)
    (hbig₀ : D₀ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4))
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hY₀ : ContDiffOn ℝ ∞ Y₀ D₀)
    (hΦD₀ : MapsTo (fun q ↦ (q.1, Φ₀ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D₀)
    (hYD₀ : MapsTo (fun q ↦ (q.1, Y₀ q)) D₀ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hinit₀ : ∀ p ∈ ball p₀ (R / 8), Φ₀ (0, p) = p)
    (hode₀ : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ₀ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q₀ row col
          ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
            (t, Φ₀ (t, p))))).2, 0) t)
    (hΦY₀ : ∀ q ∈ D₀, Φ₀ (q.1, Y₀ q) = q.2)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball p₀ (R / 8)))
    (hipos : ∀ p ∈ ball p₀ (R / 8), 0 < initial p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ δ > 0, q = m ∧ ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (F : Euclidean n → Euclidean N)
      (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω →
      ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ω →
      cNorm K 1 (carrierTransportDirection T Q row col) ≤ M → IsOpen D →
      Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) → ContDiffOn ℝ ∞ Y D →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) →
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
        HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
            ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
              (t, Φ (t, p))))).2, 0) t) →
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) →
      cNorm K q (carrierTransportDirection T Q row col -
        carrierTransportDirection T Q₀ row col) < δ →
      cNorm K q (carrierTransportPotential T Q F row col -
        carrierTransportPotential T Q₀ F₀ row col) < δ →
      let α := carrierScalarAmplitude T Q F row col Φ Y initial
      let α₀ := carrierScalarAmplitude T Q₀ F₀ row col Φ₀ Y₀ initial
      (∀ w ∈ Kphysical, 0 < α w) ∧
      (∀ w ∈ Kcarrier, 0 < α (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) ∧
      cNorm KΦ m (Φ - Φ₀) + cNorm KY m (Y - Y₀) +
        cNorm Kphysical m (α - α₀) +
        cNorm Kcarrier m ((fun w ↦ α (w.1, ContinuumRow.CanonicalCarrier.parameter w.2)) -
          (fun w ↦ α₀ (w.1, ContinuumRow.CanonicalCarrier.parameter w.2))) < ε := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let W := Ioo (-τ) τ ×ˢ ball p₀ (R / 8)
  let L := closedBall ((0 : ℝ), p₀) R
  let V := C.symm ⁻¹' Ω
  let c₀ := carrierTransportPotential T Q₀ F₀ row col ∘ C.symm
  let a₀ := transportFromFootpoint (flowTransportCoefficient c₀ Φ₀) 0 initial Y₀
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_ball
  have hV : IsOpen V := hΩ.preimage C.symm.continuous
  have hL : IsCompact L := isCompact_closedBall _ _
  have hLV : L ⊆ V := fun _ hq ↦ hKΩ (hbuffer hq)
  have hτ : 0 < τ := by
    rw [hτeq]
    exact div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hM)) (by norm_num)
  have hτR : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hM)).1
    rw [hτeq]
    linarith
  have hbox : Ioo (-τ) τ ×ˢ ball p₀ (R / 4) ⊆ L := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨by simpa only [Real.dist_eq, sub_zero] using
      (abs_le.mpr ⟨ht.1.le, ht.2.le⟩).trans (by linarith : τ ≤ R),
      (mem_ball.mp hp).le.trans (by linarith)⟩
  have hc₀' : ContDiffOn ℝ ∞ c₀ V :=
    hc₀.comp C.symm.contDiff.contDiffOn (fun _ hq ↦ hq)
  have hY₀' : ∀ q ∈ KY, ContDiffAt ℝ ∞ Y₀ q :=
    fun _ hq ↦ hY₀.contDiffAt (hD₀.mem_nhds (hsmall₀ (hKY hq)))
  have hrange₀ : MapsTo (fun q ↦ (q.1, Φ₀ q)) W L :=
    fun _ hq ↦ hbox (hbig₀ (hΦD₀ hq))
  obtain ⟨Bp, hBp, hpb⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := ℝ) hKphysical hKYc (fun _ _ ↦ C.contDiff.contDiffAt) hphysical
  obtain ⟨Bc, hBc, hcb⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := ℝ) hKcarrier hKYc (fun _ _ ↦ (densityCoordinates T).contDiff.contDiffAt) hcarrier
  let H := 1 + Bp m + Bc m
  have hH : 0 < H := by dsimp [H]; linarith [hBp m, hBc m]
  obtain ⟨S, _hS, hSW, d, hd, hscalar⟩ := exists_cNorm_flowScalar_sub_lt
    hτ (by positivity : 0 < R / 8) hV hL hLV hKYc hc₀' hi hΦ₀ hrange₀ hY₀'
    (fun _ hq ↦ hYD₀ (hsmall₀ (hKY hq))) m (div_pos (half_pos hε) hH)
  obtain ⟨B, hB, hpot⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := ℝ) hL hK (fun _ _ ↦ C.symm.contDiff.contDiffAt) hbuffer
  have stable {S' : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
      (hS' : S' ⊆ W) {e : ℝ} (he : 0 < e) :=
    exists_cNorm_carrier_characteristics_sub_lt T hΩ hK hKΩ hR hM hbuffer hτeq
      hS' hKY Q₀ row col hd₀ hlow₀ hsmall₀ hbig₀ hΦD₀ hYD₀ hinit₀ hode₀ hΦY₀ m he
  obtain ⟨df, hdf, hflow⟩ := stable hSW hd
  obtain ⟨dout, hdout, hout⟩ := stable hKΦ (half_pos hε)
  refine ⟨m, min df (min dout (d / B m)), lt_min hdf (lt_min hdout (div_pos hd (hB m))), rfl, ?_⟩
  intro Q F Φ Y D hdirection hpotential hlow hD hsmall hbig hΦ hY hΦD hYD hinit hode hΦY
    hclosed hclosec
  let c := carrierTransportPotential T Q F row col ∘ C.symm
  let a := transportFromFootpoint (flowTransportCoefficient c Φ) 0 initial Y
  have hc : ContDiffOn ℝ ∞ c V :=
    hpotential.comp C.symm.contDiff.contDiffOn (fun _ hq ↦ hq)
  have hY' : ∀ q ∈ KY, ContDiffAt ℝ ∞ Y q :=
    fun _ hq ↦ hY.contDiffAt (hD.mem_nhds (hsmall (hKY hq)))
  have hrange : MapsTo (fun q ↦ (q.1, Φ q)) W L :=
    fun _ hq ↦ hbox (hbig (hΦD hq))
  have hflows := hflow Q Φ Y D hdirection hlow hsmall hbig hΦD hYD hinit hode hΦY
    (hclosed.trans_le (min_le_left _ _))
  have houtputs := hout Q Φ Y D hdirection hlow hsmall hbig hΦD hYD hinit hode hΦY
    (hclosed.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hcsmall : cNorm L m (c - c₀) < d := by
    have hh := hpot (carrierTransportPotential T Q F row col -
      carrierTransportPotential T Q₀ F₀ row col)
      (fun w hw ↦ (hpotential.contDiffAt (hΩ.mem_nhds (hKΩ hw))).sub
        (hc₀.contDiffAt (hΩ.mem_nhds (hKΩ hw)))) m
    apply hh.trans_lt
    have hh' := hclosec.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [mul_comm] using (lt_div_iff₀ (hB m)).mp hh'
  have hasmall : cNorm KY m (a - a₀) < (ε / 2) / H :=
    hscalar c Φ Y hc hΦ hrange hY' hcsmall
      (by linarith [cNorm_nonneg KY m (Y - Y₀)])
      (by linarith [cNorm_nonneg S m (Φ - Φ₀)])
  have smooth (c' : ℝ × (Euclidean (n - 1) × Euclidean 3) → ℝ)
      (Φ' Y' : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (D' : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
      (hc' : ContDiffOn ℝ ∞ c' V) (hΦ' : ContDiffOn ℝ ∞ Φ' W)
      (hr' : MapsTo (fun q ↦ (q.1, Φ' q)) W L)
      (hD' : IsOpen D') (hKD' : KY ⊆ D') (hY' : ContDiffOn ℝ ∞ Y' D')
      (hYr' : MapsTo (fun q ↦ (q.1, Y' q)) D' W) :
      ∀ q ∈ KY, ContDiffAt ℝ ∞
        (transportFromFootpoint (flowTransportCoefficient c' Φ') 0 initial Y') q := by
    have hco := contDiffOn_flowTransportCoefficient hc' hΦ' (fun _ hq ↦ hLV (hr' hq))
    exact fun q hq ↦ (contDiffOn_transportFromFootpoint isOpen_Ioo ordConnected_Ioo
      isOpen_ball hco hi ⟨neg_neg_of_pos hτ, hτ⟩ hY' hYr').contDiffAt
        (hD'.mem_nhds (hKD' hq))
  have ha : ∀ q ∈ KY, ContDiffAt ℝ ∞ (a - a₀) q := fun q hq ↦
    (smooth c Φ Y D hc hΦ hrange hD (hKY.trans hsmall) hY hYD q hq).sub
      (smooth c₀ Φ₀ Y₀ D₀ hc₀' hΦ₀ hrange₀ hD₀ (hKY.trans hsmall₀) hY₀ hYD₀ q hq)
  have hpos (w : Euclidean n × Euclidean 3) (hw : C w ∈ KY) :
      0 < carrierScalarAmplitude T Q F row col Φ Y initial w :=
    transportFromFootpoint_pos _ _ _ _ _ (hipos _ (hYD (hsmall (hKY hw))).2)
  refine ⟨fun w hw ↦ hpos w (hphysical hw), fun w hw ↦ hpos _ (hcarrier hw), ?_⟩
  have hp := hpb (a - a₀) ha m
  have hb := hcb (a - a₀) ha m
  change cNorm Kphysical m (carrierScalarAmplitude T Q F row col Φ Y initial -
    carrierScalarAmplitude T Q₀ F₀ row col Φ₀ Y₀ initial) ≤ Bp m * cNorm KY m (a - a₀) at hp
  have hexp : H * cNorm KY m (a - a₀) < ε / 2 := by
    simpa only [mul_comm] using (lt_div_iff₀ hH).mp hasmall
  dsimp only [H] at hexp
  change cNorm KΦ m (Φ - Φ₀) + cNorm KY m (Y - Y₀) +
    cNorm Kphysical m (carrierScalarAmplitude T Q F row col Φ Y initial -
      carrierScalarAmplitude T Q₀ F₀ row col Φ₀ Y₀ initial) +
    cNorm Kcarrier m ((a - a₀) ∘ densityCoordinates T) < ε
  nlinarith [cNorm_nonneg KY m (a - a₀)]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
