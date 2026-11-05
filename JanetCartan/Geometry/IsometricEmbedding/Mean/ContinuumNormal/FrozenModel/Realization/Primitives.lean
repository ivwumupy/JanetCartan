module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Masks

/-!
# Primitive regularity of the actual zero-scale carrier

These are inputs to the supported carrier constructor in the frozen step of
`app:ch_background:prop:bg-frame`. The linear phase is the actual normalized
Hamilton derivative. The normal and detector are the original seed values,
and all measurement, angular and high masks are retained. The finite budgets
below are for a fixed seed; they do not assert uniformity as the seed varies.
The conic geometry and the global operator realization remain separate inputs
to the parent construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)

include hP

/-- Smoothness of the actual linear frozen transport field, on every physical
position and the original seed parameter buffer (`new:lem:scaling`). This is
the geometry regularity input of the supported carrier constructor. -/
theorem normalizedTransportPosition_zero_smooth :
    ContDiffOn ℝ ∞ (normalizedTransportPosition T Q 0)
      (univ ×ˢ (parameter ⁻¹' parameterInterior (3 * P.radius / 2))) := by
  have hζ : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦
      T.reference.spatialPatch (parameter z))
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :=
    (T.reference.spatialPatch_smooth hP).comp parameter.contDiff.contDiffOn
      (fun _ hz i ↦ (hz i).trans_le (by linarith [hP.1]))
  have hD := ((seedCovector_smooth T Q).fderiv_of_isOpen isOpen_ball
    (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).comp hζ
      (fun _ hz ↦ spatialPatch_mem_phaseBuffer T hP (fun i ↦ (hz i).le))
  have hA := (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hD
  have hAp := hA.comp (s := (univ : Set (Euclidean n)) ×ˢ
    (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    contDiffOn_snd (fun _ hp ↦ hp.2)
  apply (hAp.clm_apply contDiffOn_fst).congr
  intro p hp
  exact normalizedTransportPosition_zero T Q
    (spatialPatch_mem_phaseBuffer T hP (fun i ↦ (hp.2 i).le)) p.1

variable (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

omit hP in
/-- For the paper's unit initial amplitude the actual frozen carrier is
independent of the retained flow witnesses. This follows by evaluating the
literal transport at time zero, not by replacing the flow in positive scale
(`new:lem:scaling`). -/
theorem normalizedCarrierData_zero_unit_independent_flow
    (Φ' Y' : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {a : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha hcell angular high 0 =
      normalizedCarrierData T Q F row col Φ' Y' (fun _ ↦ 1) ha hcell angular high 0 := by
  simp only [normalizedCarrierData, data]
  congr 1
  funext x z
  rw [normalizedNormal_zero_unit, normalizedNormal_zero_unit]

/-- Smooth initial data on the retained flow give the actual zero-scale
normal on a physical/carrier buffer. Only the seed section of the original
footpoint is used (`new:lem:scaling`, `app:ch_background:eq:bg-Nsigma`). -/
theorem normalizedNormal_zero_smooth
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial D) (hY : ContDiffOn ℝ ∞ Y Dflow)
    {Z : Set CarrierParameter}
    (hZ : Z ⊆ parameter ⁻¹' parameterInterior (2 * P.radius))
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      Z Dflow) (hYrange : MapsTo Y Dflow D) :
    ContDiffOn ℝ ∞ (Function.uncurry (normalizedNormal T Q F row col Φ Y initial 0))
      (univ ×ˢ Z) := by
  have hy := hY.comp
    (contDiffOn_const.prodMk (contDiffOn_const.prodMk parameter.contDiff.contDiffOn)) hseed
  have hn := frozenSeedNormal_smooth T Q F row col Φ Y hP initial hi hZ hy
    (hYrange.comp hseed)
  apply (hn.comp contDiffOn_snd (fun _ hp ↦ hp.2)).congr
  intro p _
  exact normalizedNormal_zero T Q F row col Φ Y initial p.1 p.2

omit hP in
private theorem enlargePrimitiveControls {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D : PrimitiveNormChart E} {s : ℕ} {M M' B B' H : ℝ} {f : E → G}
    (h : D.Controls s M B H f) (hM : M ≤ M') (hB : B ≤ B') (hH : 0 ≤ H) :
    D.Controls s M' B' H f :=
  ⟨h.smooth, h.low.trans hM, h.high.trans (mul_le_mul_of_nonneg_right hB hH)⟩

/-- Every primitive coefficient and the geometry field of the fixed frozen
seed has a finite budget on the supplied compact charts. The five controls
refer to the literal `normalizedCarrierData` and its original cutoffs.
The constants precede the derivative order and high budget, but may depend
on the fixed seed and initial datum; no uniform family estimate is claimed.
Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`;
sources: `new:lem:scaling`, `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_frozen_primitive_controls
    {Dinitial : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial Dinitial) (hY : ContDiffOn ℝ ∞ Y Dflow)
    (D : CoefficientNormCharts n)
    (hparam : MapsTo Prod.snd D.field.region
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (hseed : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter p.2))) D.field.region Dflow)
    (hYrange : MapsTo Y Dflow Dinitial)
    {a : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hang : ContDiff ℝ ∞ (Function.uncurry angular)) :
    ∃ M ≥ (0 : ℝ), ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧
      ContDiffOn ℝ ∞ (normalizedTransportPosition T Q 0) D.field.region ∧
      cNorm D.field.carrier 3 (normalizedTransportPosition T Q 0) ≤ M ∧
      ∀ s H, 1 ≤ H →
        D.Controls s M (B s) H (TransportKernel.coefficientsOfCarrier
          (normalizedCarrierData T Q F row col Φ Y initial ha hcell angular
            FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha 1)) ∧
        1 + cNorm D.field.carrier (s + 2) (normalizedTransportPosition T Q 0) ≤ B s * H := by
  let ν := fun p : Euclidean n × CarrierParameter ↦ normalField T Q F row col Φ Y initial 0 p.2
  let q := fun p : Euclidean n × CarrierParameter ↦
    (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2))).ofLp
  let ψ := normalizedTransportPosition T Q 0
  have hparam' : MapsTo Prod.snd D.field.region
      (parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    fun p hp i ↦ (hparam hp i).trans_le (by linarith [hP.1])
  have hνunit := (frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).comp
    contDiffOn_snd hparam'
  have hν : ContDiffOn ℝ ∞ ν D.field.region := by
    have hy := hY.comp
      (contDiffOn_const.prodMk (contDiffOn_const.prodMk
        (parameter.contDiff.comp_contDiffOn contDiffOn_snd))) hseed
    apply ((hi.comp hy (hYrange.comp hseed)).smul hνunit).congr
    intro p _
    exact frozenSeedNormal_initial_factor T Q F row col Φ Y initial p.2
  have hq : ContDiffOn ℝ ∞ q D.field.region :=
    (PiLp.contDiff_ofLp.comp_contDiffOn (frozenSeedDetector_smooth T Q hP)).comp
      contDiffOn_snd hparam'
  have hψ := (normalizedTransportPosition_zero_smooth T Q hP).mono
    (fun p hp ↦ ⟨mem_univ p.1, hparam hp⟩)
  obtain ⟨Mmask, hMmask, Bmask, hBmask, hmasks⟩ :=
    exists_fixedMask_controls D ha angular hang.contDiffOn
  let M := Mmask + cNorm D.field.carrier 1 ν + cNorm D.field.carrier 1 q +
    cNorm D.field.carrier 3 ψ
  let B := fun s ↦ Bmask s + cNorm D.field.carrier s ν + cNorm D.field.carrier s q +
    cNorm D.field.carrier (s + 2) ψ
  have hn₀ := cNorm_nonneg D.field.carrier 1 ν
  have hq₀ := cNorm_nonneg D.field.carrier 1 q
  have hψ₀ := cNorm_nonneg D.field.carrier 3 ψ
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hMM : Mmask ≤ M := by dsimp [M]; linarith
  have hB (s) : 1 ≤ B s := by
    dsimp [B]
    linarith [hBmask s, cNorm_nonneg D.field.carrier s ν,
      cNorm_nonneg D.field.carrier s q, cNorm_nonneg D.field.carrier (s + 2) ψ]
  refine ⟨M, hM, B, hB, hψ, ?_, ?_⟩
  · change cNorm D.field.carrier 3 ψ ≤ M
    dsimp [M]; linarith
  intro s H hH
  have hn₁ := cNorm_nonneg D.field.carrier s ν
  have hq₁ := cNorm_nonneg D.field.carrier s q
  have hψ₁ := cNorm_nonneg D.field.carrier (s + 2) ψ
  have hBB : Bmask s ≤ B s := by dsimp [B]; linarith
  have hBH : B s ≤ B s * H := le_mul_of_one_le_right (zero_le_one.trans (hB s)) hH
  obtain ⟨hm, ha, hh⟩ := hmasks s H hH
  constructor
  · rw [coefficientsOfCarrier_normalizedCarrierData_zero]
    refine ⟨enlargePrimitiveControls hm hMM hBB (zero_le_one.trans hH),
      enlargePrimitiveControls ha hMM hBB (zero_le_one.trans hH),
      enlargePrimitiveControls hh hMM hBB (zero_le_one.trans hH),
      ⟨hν, ?_, ?_⟩, ⟨hq, ?_, ?_⟩⟩
    · change cNorm D.field.carrier 1 ν ≤ M
      dsimp [M]; linarith
    · change 1 + cNorm D.field.carrier s ν ≤ B s * H
      apply le_trans _ hBH
      dsimp [B]; linarith [hBmask s]
    · change cNorm D.field.carrier 1 q ≤ M
      dsimp [M]; linarith
    · change 1 + cNorm D.field.carrier s q ≤ B s * H
      apply le_trans _ hBH
      dsimp [B]; linarith [hBmask s]
  · apply le_trans _ hBH
    dsimp [B]; linarith [hBmask s]

/-- Finite primitive budgets for the paper's unit-initial frozen carrier.
No smooth-flow or initial-section premise remains: the time-zero identity
discharges it for the original retained witnesses. The fixed-seed constants
are not uniform over immersions (`new:lem:scaling`, `bg-mixed-input`). -/
theorem exists_frozen_unit_primitive_controls
    (D : CoefficientNormCharts n)
    (hparam : MapsTo Prod.snd D.field.region
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    {a : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hang : ContDiff ℝ ∞ (Function.uncurry angular)) :
    ∃ M ≥ (0 : ℝ), ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧
      ContDiffOn ℝ ∞ (normalizedTransportPosition T Q 0) D.field.region ∧
      cNorm D.field.carrier 3 (normalizedTransportPosition T Q 0) ≤ M ∧
      ∀ s H, 1 ≤ H →
        D.Controls s M (B s) H (TransportKernel.coefficientsOfCarrier
          (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha hcell angular
            FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha 1)) ∧
        1 + cNorm D.field.carrier (s + 2) (normalizedTransportPosition T Q 0) ≤ B s * H := by
  rw [normalizedCarrierData_zero_unit_independent_flow T Q F row col Φ Y Φ (fun _ ↦ 0)]
  exact exists_frozen_primitive_controls T Q hP F row col Φ (fun _ ↦ 0) (fun _ ↦ 1)
    (Dinitial := univ) (Dflow := univ) contDiffOn_const contDiffOn_const D hparam
    (fun _ _ ↦ mem_univ _) (fun _ _ ↦ mem_univ _) ha hcell angular hang

end JanetCartan.ContinuumNormal.FrozenModel
