module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.ColumnBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds

/-!
# Bounds for the same retained full correction

The selected null-column lower bound is an actual conclusion of
`exists_finite_retained_leading_family_before_geometry`. It gives the compact
primitive range needed by the published correction formula, without a new
selected-minor assumption. The selected transport row, column, scalar and
flows remain unchanged (`app:ch_waves:eq:primary-algebraic-correction`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1000000

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary.RetainedCorrection
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile
open ActualCarriers.ConstructedCarrierJets CorrectionBounds
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

section Primitive
variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

private theorem exists_primitiveCorrection_tame_of_retained_column
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hx : MapsTo Prod.fst (closedBall a ρ) K) (col : Fin n)
    (M L : ℝ) {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (U : Set (Euclidean n)) (Ω : Set (Euclidean n × Z)),
        IsOpen U → IsOpen Ω → K ⊆ U → closedBall a ρ ⊆ Ω → MapsTo Prod.fst Ω U →
      ∀ (F : Euclidean n → Euclidean N) (v : Euclidean n × Z → Values n),
        ContDiffOn ℝ ∞ F U → ContDiffOn ℝ ∞ v Ω →
        cNorm (closedBall a ρ) 1 v ≤ L →
        (∀ x ∈ K, ‖stressJet F x‖ ≤ M) →
        (∀ x ∈ K, ∀ u, κ * ‖u‖ ^ 2 ≤ ‖fderiv ℝ F x u‖ ^ 2) →
        (∀ w ∈ closedBall a ρ, (symbolValue (v w)).det = 0) →
        (∀ w ∈ closedBall a ρ, b ≤ ‖right col (v w).1‖) →
        ∀ m, cNorm (closedBall a ρ) m (correctionJetValue col ∘ primitiveJet F v) ≤
          C m * (1 + cNorm K (m + 2) F + cNorm (closedBall a ρ) (m + 1) v) := by
  obtain ⟨C, hC, hbound⟩ := exists_correctionJetValue_tame_of_retained_column (N := N) a hρ col M L hκ hb
  obtain ⟨A, hA, ha⟩ := exists_cNorm_fixed_pullback_le (G := StressJet n N)
    (isCompact_closedBall a ρ) hK (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  refine ⟨fun m ↦ C m * (1 + 2 * A m),
    fun m ↦ mul_pos (hC m) (by have := hA m; positivity), ?_⟩
  intro U Ω hU hΩ hKU hball hΩU F v hF hv hlow hM hmet hchar hcolumn m
  have hJ := (contDiffOn_stressJet hU hF).comp contDiffOn_fst hΩU
  have hout := hbound Ω hΩ hball v (fun w ↦ stressJet F w.1) hv hJ hlow
    (fun w hw ↦ hM w.1 (hx hw)) (fun w hw ↦ hmet w.1 (hx hw)) hchar hcolumn m
  have hjet := cNorm_stressJet_le hK (fun x hx ↦ hF.contDiffAt (hU.mem_nhds (hKU hx))) m
  have hpull := ha (stressJet F)
    (fun x hx ↦ (contDiffOn_stressJet hU hF).contDiffAt (hU.mem_nhds (hKU hx))) m
  have hJhigh := hpull.trans (mul_le_mul_of_nonneg_left hjet (hA m).le)
  have htotal : 1 + cNorm (closedBall a ρ) m (fun w ↦ stressJet F w.1) +
      cNorm (closedBall a ρ) (m + 1) v ≤
      (1 + 2 * A m) * (1 + cNorm K (m + 2) F + cNorm (closedBall a ρ) (m + 1) v) := by
    have := hA m
    have := cNorm_nonneg K (m + 2) F
    have := cNorm_nonneg (closedBall a ρ) (m + 1) v
    dsimp only [Function.comp_def] at hJhigh
    nlinarith
  exact hout.trans ((mul_le_mul_of_nonneg_left htotal (hC m).le).trans_eq (by ring))

end Primitive

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}

/-- The literal correction has losses two in the immersion and one in its
primitive values, using only the retained quantitative null-column output.
The selected transport row and all scalar/flow witnesses are preserved.
Consumer: the reserve-fourteen estimate in `app:ch_waves:eq:WKB-grading`. -/
theorem exists_fullCorrectionCovector_primitive_bounds_of_retained_column
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K)
    (hxK : MapsTo Prod.fst (closedBall a ρ) K) (hKU : K ⊆ U)
    (row col : Fin n) (M L : ℝ) {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) :
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
          b ≤ ‖nullvector T Q col w‖) →
        ∀ m, cNorm (closedBall a ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          C m * (1 + cNorm K (m + 2) F +
            cNorm (closedBall a ρ) (m + 1) (fullPrimitiveValues T Q F row col Φ Y r)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_primitiveCorrection_tame_of_retained_column (N := N)
    a hρ hK hxK col M L hκ hb
  refine ⟨C, hC, ?_⟩
  intro Q F Φ Y r Ω hΩ hball hx hphase hF hscalar hlow hM hmet hcolumn
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
  have hbound (m : ℕ) := hbudget U Ω hU hΩ hKU hball hx F
    (fullPrimitiveValues T Q F row col Φ Y r) hF hv hlow hM hmet hc hcolumn m
  simp only [hnorm] at hbound
  exact hbound

end JanetCartan.RawPrimary.RetainedCorrection
