module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds.PrimitiveBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.PhaseBounds

/-!
# Primitive coefficient bounds for the full orthogonal correction

These estimates concern exactly `fullCorrectionCovector`, including its
induced Christoffel terms. The analytic inputs are smoothness and low/high
budgets of the primitive immersion, stress frame, phase gradient and scalar
amplitude. The scalar's producer is `FullModulation.scalarAmplitude_spec` in
`FullModulation/Transport/Amplitude`; its quantitative producers and the
actual-family geometric gaps must be instantiated by the parent construction.
The low immersion jet bound follows from
`ProjectedStressFrame.norm_stressJet_le_cNorm_four` and the fixed `C⁴` budget.

For `app:ch_waves:eq:WKB-grading` and `app:ch_waves:thm:wkb`, the constants
precede the frequency, scalar datum, flow, frame and immersion. The finite
losses are two for the immersion and one for the other primitive values.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary.CorrectionBounds
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
  (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The literal primitive values for the SAME full correction, with independent
carrier and covector parameters (`app:ch_waves:eq:primary-algebraic-correction`). -/
def fullPrimitiveValues (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Values n :=
  ((Q.1 w.1, phaseGradient T Q w.1 w.2.2), scalarAmplitude T Q F row col Φ Y r w)

/-- Smoothness is obtained from the actual frame and phase and the primitive
scalar transport input. No correction regularity is assumed
(`app:ch_waves:eq:WKB-grading`). -/
theorem contDiffOn_fullPrimitiveValues
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hx : MapsTo Prod.fst Ω U) (hphase : Ω ⊆ domain T)
    (hscalar : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞ (fullPrimitiveValues T Q F row col Φ Y r) Ω :=
  ((Q.2.1.comp contDiffOn_fst hx).prodMk
    ((phaseGradient_joint_smooth T Q).mono hphase)).prodMk hscalar

/-- Splitting the primitive value budget involves only the original frame,
phase gradient and scalar amplitude, with no derivative loss
(`app:ch_waves:eq:WKB-grading`). -/
theorem cNorm_fullPrimitiveValues_le
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (ρ : ℝ) (m : ℕ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hball : closedBall a ρ ⊆ Ω)
    (hx : MapsTo Prod.fst Ω U) (hphase : Ω ⊆ domain T)
    (hscalar : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    cNorm (closedBall a ρ) m (fullPrimitiveValues T Q F row col Φ Y r) ≤
      (m + 1 : ℝ) ^ 2 *
        (cNorm (closedBall a ρ) m (fun w ↦ Q.1 w.1) +
          cNorm (closedBall a ρ) m (fun w ↦ phaseGradient T Q w.1 w.2.2) +
          cNorm (closedBall a ρ) m (scalarAmplitude T Q F row col Φ Y r)) := by
  have hQ := Q.2.1.comp contDiffOn_fst hx
  have hξ := (phaseGradient_joint_smooth T Q).mono hphase
  have hinner := cNorm_pair_le a m hΩ hball hQ hξ
  have houter := cNorm_pair_le a m hΩ hball (hQ.prodMk hξ) hscalar
  apply houter.trans
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add hinner (le_refl (cNorm (closedBall a ρ) m (scalarAmplitude T Q F row col Φ Y r))))
    (by positivity : (0 : ℝ) ≤ m + 1)
  apply hh.trans
  have ha := cNorm_nonneg (closedBall a ρ) m (scalarAmplitude T Q F row col Φ Y r)
  have hm : (m + 1 : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  dsimp only [Function.comp_def]
  nlinarith [mul_le_mul_of_nonneg_right hm ha]

/-- Primitive frame, phase-gradient and transported-scalar profiles supply the
packed input profile used below. Thus this interface introduces no independent
analytic budget (`app:cor:fixed-profile-transfer`). -/
theorem hasDerivativeProfile_fullPrimitiveValues
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (ρ : ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hball : closedBall a ρ ⊆ Ω)
    (hx : MapsTo Prod.fst Ω U) (hphase : Ω ⊆ domain T)
    (hscalar : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {R : ℕ} {scale : ℝ} {AQ Aξ Aα : ℕ → ℝ}
    (hQ : HasDerivativeProfile (closedBall a ρ) (fun w ↦ Q.1 w.1) R scale AQ)
    (hξ : HasDerivativeProfile (closedBall a ρ)
      (fun w ↦ phaseGradient T Q w.1 w.2.2) R scale Aξ)
    (hα : HasDerivativeProfile (closedBall a ρ) (scalarAmplitude T Q F row col Φ Y r) R scale Aα) :
    HasDerivativeProfile (closedBall a ρ) (fullPrimitiveValues T Q F row col Φ Y r)
      R scale (fun m ↦ (m + 1 : ℝ) ^ 2 * (AQ m + Aξ m + Aα m)) := by
  intro m
  apply (cNorm_fullPrimitiveValues_le T Q F row col Φ Y r a ρ m
    hΩ hball hx hphase hscalar).trans
  exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hQ m) (hξ m)) (hα m))
    (sq_nonneg _)).trans_eq (by ring)

/-- Exact finite-jet identification of the published correction; the physical
derivatives and induced connection are unchanged
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem correctionJetValue_eq_fullCorrectionCovector
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hF : ContDiffAt ℝ ∞ F w.1)
    (hv : DifferentiableAt ℝ (fullPrimitiveValues T Q F row col Φ Y r) w) :
    correctionJetValue col (primitiveJet F (fullPrimitiveValues T Q F row col Φ Y r) w) =
      fullCorrectionCovector T Q F row col Φ Y r w := by
  rw [correctionJetValue, reducedLeadingJet_primitiveJet col hF hv]
  rfl

variable {T Q F row col Φ Y r}

set_option maxHeartbeats 800000 in
/-- Local regularity of the SAME correction from primitive smoothness, metric
injectivity, characteristicity and its original fixed minor
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiffAt_fullCorrectionCovector_of_primitiveJets
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hx : MapsTo Prod.fst Ω U) (hphase : Ω ⊆ domain T)
    (hF : ContDiffOn ℝ ∞ F U)
    (hscalar : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hmet : IsUnit (firstJetMetric (fderiv ℝ F w.1)))
    (hminor : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0) :
    ContDiffAt ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) w := by
  have hv := contDiffOn_fullPrimitiveValues T Q F row col Φ Y r hx hphase hscalar
  have hj := contDiffOn_primitiveJet hU hΩ hx hF hv
  have hchar : (symbolValue (fullPrimitiveValues T Q F row col Φ Y r w)).det = 0 :=
    phase_characteristic T Q (hphase hw)
  have hs := (contDiffAt_correctionJetValue
    (p := primitiveJet F (fullPrimitiveValues T Q F row col Φ Y r) w)
    row col hmet hchar hminor).comp w
    (hj.contDiffAt (hΩ.mem_nhds hw))
  apply hs.congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hw] with y hy
  exact (correctionJetValue_eq_fullCorrectionCovector T Q F row col Φ Y r
    (hF.contDiffAt (hU.mem_nhds (hx hy)))
    ((hv.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))).symm

/-- One-high finite-loss estimate and fixed-profile transfer for the literal
full correction (`app:ch_waves:eq:WKB-grading`, `app:ch_waves:thm:wkb`).
The gaps and low bound refer only to primitive immersion and symbol data.
The phase's characteristic equation is supplied by its actual construction.
The parent must instantiate the scalar budget and the primitive gaps. -/
theorem exists_fullCorrectionCovector_bounds
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K)
    (hxK : MapsTo Prod.fst (closedBall a ρ) K) (hKU : K ⊆ U)
    (row col : Fin n) (M L : ℝ) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
        IsOpen Ω → closedBall a ρ ⊆ Ω → MapsTo Prod.fst Ω U → Ω ⊆ domain T →
        ContDiffOn ℝ ∞ F U →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        cNorm (closedBall a ρ) 1 (fullPrimitiveValues T Q F row col Φ Y r) ≤ L →
        (∀ x ∈ K, ‖stressJet F x‖ ≤ M) →
        (∀ x ∈ K, ∀ u, κ * ‖u‖ ^ 2 ≤ ‖fderiv ℝ F x u‖ ^ 2) →
        (∀ w ∈ closedBall a ρ,
          δ ≤ |(reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col|) →
        (∀ m, cNorm (closedBall a ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          C m * (1 + cNorm K (m + 2) F +
            cNorm (closedBall a ρ) (m + 1) (fullPrimitiveValues T Q F row col Φ Y r))) ∧
        ∀ (RF RV ν : ℕ) (scale : ℝ) (AF AV : ℕ → ℝ),
          HasDerivativeProfile K F RF scale AF →
          HasDerivativeProfile (closedBall a ρ) (fullPrimitiveValues T Q F row col Φ Y r) RV scale AV →
          1 ≤ scale → (∀ m, 0 ≤ AF m) → (∀ m, 0 ≤ AV m) →
          2 + ν ≤ RF → 1 + ν ≤ RV →
          HasDerivativeProfile (closedBall a ρ) (fullCorrectionCovector T Q F row col Φ Y r)
            ν scale (fun m ↦ C m * (1 + AF (m + 2) + AV (m + 1))) ∧
          ∀ j k : ℕ, k ≤ ν → ∀ w ∈ closedBall a ρ,
            ‖iteratedFDeriv ℝ (j + k) (fullCorrectionCovector T Q F row col Φ Y r) w‖ ≤
              C (j + k) * (1 + AF (j + k + 2) + AV (j + k + 1)) * scale ^ j := by
  obtain ⟨C, hC, hb⟩ := exists_primitiveCorrection_tame (N := N)
    a hρ hK hxK row col M L hκ hδ
  refine ⟨C, hC, ?_⟩
  intro Q F Φ Y r Ω hΩ hball hx hphase hF hscalar hlow hM hmet hminor
  have hv := contDiffOn_fullPrimitiveValues T Q F row col Φ Y r hx hphase hscalar
  have hc (w) (hw : w ∈ closedBall a ρ) :
      (symbolValue (fullPrimitiveValues T Q F row col Φ Y r w)).det = 0 :=
    phase_characteristic T Q (hphase (hball hw))
  have hnorm (m : ℕ) : cNorm (closedBall a ρ) m
      (correctionJetValue col ∘ primitiveJet F (fullPrimitiveValues T Q F row col Φ Y r)) =
      cNorm (closedBall a ρ) m (fullCorrectionCovector T Q F row col Φ Y r) := by
    apply cNorm_eq_of_eventuallyEq _ m
    intro w hw
    filter_upwards [hΩ.mem_nhds (hball hw)] with y hy
    exact correctionJetValue_eq_fullCorrectionCovector T Q F row col Φ Y r
      (hF.contDiffAt (hU.mem_nhds (hx hy)))
      ((hv.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  have hbound (m : ℕ) := hb U Ω hU hΩ hKU hball hx F
    (fullPrimitiveValues T Q F row col Φ Y r) hF hv hlow hM hmet hc hminor m
  simp only [hnorm] at hbound
  refine ⟨hbound, ?_⟩
  intro RF RV ν scale AF AV hPF hPV hscale hAF hAV hRF hRV
  have hprofile : HasDerivativeProfile (closedBall a ρ)
      (fullCorrectionCovector T Q F row col Φ Y r) ν scale
        (fun m ↦ C m * (1 + AF (m + 2) + AV (m + 1))) := by
    intro m
    have hFgrade : cNorm K (m + 2) F ≤ AF (m + 2) * scale ^ (m - ν) :=
      (hPF (m + 2)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hscale (by omega : m + 2 - RF ≤ m - ν)) (hAF _))
    have hVgrade : cNorm (closedBall a ρ) (m + 1) (fullPrimitiveValues T Q F row col Φ Y r) ≤
        AV (m + 1) * scale ^ (m - ν) :=
      (hPV (m + 1)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hscale (by omega : m + 1 - RV ≤ m - ν)) (hAV _))
    apply (hbound m).trans
    have hsum := add_le_add (add_le_add (one_le_pow₀ hscale : 1 ≤ scale ^ (m - ν)) hFgrade) hVgrade
    exact (mul_le_mul_of_nonneg_left hsum (hC m).le).trans_eq (by ring)
  refine ⟨hprofile, ?_⟩
  intro j k hk w hw
  have hs (y) (hy : y ∈ closedBall a ρ) :
      ContDiffAt ℝ (j + k) (fullCorrectionCovector T Q F row col Φ Y r) y :=
    (contDiffAt_fullCorrectionCovector_of_primitiveJets hΩ hx hphase hF hscalar (hball hy)
      (firstJetMetric_isUnit_of_gap (J := stressJet F y.1) hκ (hmet y.1 (hxK hy)))
      (abs_pos.mp (hδ.trans_le (hminor y hy)))).of_le (by simp)
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
    hs hw le_rfl).trans
  apply (hprofile (j + k)).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hscale (by omega : j + k - ν ≤ j))
    (mul_nonneg (hC _).le (by have := hAF (j + k + 2); have := hAV (j + k + 1); positivity))

end JanetCartan.RawPrimary.CorrectionBounds
