module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.DensityScalar
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.DensityFootpoint
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# One-high dependence on the original initial density

The actual carrier normal factors through the SAME inverse ODE label.
Uniform bounds for this label give an estimate linear in one high norm of the
initial density, with constants chosen before both the flow and density.
There is no uniform all-order bound over densities with unbounded high jets.

Consumer: `CoefficientNormCharts.Controls.normal` for the normalized reflected
amplitude. Sources: `app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-mixed-input`, `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedCarrierProfiles
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier NullTransport
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ContinuumNormalReduction.TransportSymbol LeadingWave

/-- The prescribed initial multiplier acts at the literal inverse ODE
footpoint, with the original scalar, completion and phase unchanged. This
identity is valid in particular for initial scalar `σ` and weight
`sqrt (1+v)`; it does not replace that footpoint by the Hamilton position.
Source: `app:ch_background:eq:bg-T`, `app:ch_waves:thm:leading`. -/
theorem normalField_initial_mul
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (x : Euclidean n) (z : CarrierParameter) :
    normalField T Q F row col Φ Y (fun q ↦ initial q * weight q) x z =
      weight (densityFootpoint T Y (x, z)) • normalField T Q F row col Φ Y initial x z := by
  rw [normalField_eq_scalar_smul, normalField_eq_scalar_smul, smul_smul]
  congr 1
  simp only [carrierScalarAmplitude, transportFromFootpoint,
    characteristicTransport, scalarTransport, densityFootpoint_eq]
  ring

/-- Uniform inverse-ODE budgets give the literal square-root multiplier a
single high density norm, with no derivative loss. Only its actual footpoint
norms are supplied, by `both-normalized-flow-profiles`; no multiplier estimate
is assumed. The constants precede every flow and density. Thus the low
`μ+1` estimate below uses the original finite density class `q=μ+14`, while
the unbounded high density jets remain explicit.
Source: `app:ch_background:eq:bg-mixed-input`,
`app:ch_background:prop:bg-normalized`. -/
theorem exists_densityFootpoint_sqrt_one_high_bounds
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (p₀ : Euclidean (n - 1) × Euclidean 3) {R : ℝ} (hR : 0 < R)
    (H : ℕ → ℝ) :
    ∃ B : ℕ → ℝ, (∀ p, 0 < B p) ∧
      ∀ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        ContDiffOn ℝ ∞ (densityFootpoint T Y) D.region →
        MapsTo (densityFootpoint T Y) D.region (ball p₀ (R / 4)) →
        MapsTo (densityFootpoint T Y) D.carrier (closedBall p₀ (R / 8)) →
        (∀ p, cNorm D.carrier p (densityFootpoint T Y) ≤ H p) →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
        ContDiffOn ℝ ∞ v (ball p₀ (R / 4)) →
        (∀ q ∈ ball p₀ (R / 4), 0 < 1 + v q) →
        (∀ q ∈ closedBall p₀ (R / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt (1 + v (densityFootpoint T Y q))) D.region ∧
        (∀ p, cNorm D.carrier p (fun q ↦ Real.sqrt (1 + v (densityFootpoint T Y q))) ≤
          B p * (1 + cNorm (closedBall p₀ (R / 8)) p v)) ∧
        (cNorm (closedBall p₀ (R / 8)) (2 * (n + 1) + 14) v ≤ 1 →
          cNorm D.carrier (2 * (n + 1) + 1)
            (fun q ↦ Real.sqrt (1 + v (densityFootpoint T Y q))) ≤
              2 * B (2 * (n + 1) + 1)) := by
  obtain ⟨A, hA, hscalar⟩ := LeadingPrimitive.DensityScalar.exists_initial_scalar_tame_bounds n p₀ hR
  let B := fun p ↦ compositionMultiplicity p * A p * (1 + |H p|) ^ p + 1
  have hmult (p) : 0 ≤ compositionMultiplicity p :=
    Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  have hB (p) : 0 < B p := by
    dsimp only [B]
    have := hmult p
    have := hA p
    positivity
  refine ⟨B, hB, ?_⟩
  intro Y hY hmap hcompact hH v hv hpos hinterval
  let w := fun q ↦ Real.sqrt (1 + v q)
  have hw : ContDiffOn ℝ ∞ w (ball p₀ (R / 4)) := by
    simpa only [positiveDensityAmplitude, one_mul] using
      contDiffOn_positiveDensityAmplitude 1 hv hpos
  have hwnorm (p) : cNorm (closedBall p₀ (R / 8)) p w ≤
      A p * (1 + cNorm (closedBall p₀ (R / 8)) p v) := by
    simpa only [positiveDensityAmplitude, one_mul] using
      hscalar 1 zero_le_one v hv hpos hinterval p
  have hKU : closedBall p₀ (R / 8) ⊆ ball p₀ (R / 4) :=
    closedBall_subset_ball (by linarith)
  have hhigh (p) : cNorm D.carrier p (w ∘ densityFootpoint T Y) ≤
      B p * (1 + cNorm (closedBall p₀ (R / 8)) p v) := by
    have hYat (x) (hx : x ∈ D.carrier) : ContDiffAt ℝ p (densityFootpoint T Y) x :=
      (hY.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hx))).of_le (by simp)
    have hwat (x) (hx : x ∈ closedBall p₀ (R / 8)) : ContDiffAt ℝ p w x :=
      (hw.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).of_le (by simp)
    have hcomp := cNorm_comp_le_polynomial hYat
      (fun x hx ↦ hwat _ (hcompact hx))
      (fun _ hj ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt (isCompact_closedBall ..) hYat hj)
      (cNorm_nonneg (closedBall p₀ (R / 8)) p w)
      (fun j hj x hx ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall ..) hwat (hcompact hx) hj)
    have hpow : (1 + cNorm D.carrier p (densityFootpoint T Y)) ^ p ≤ (1 + |H p|) ^ p :=
      pow_le_pow_left₀ (by linarith [cNorm_nonneg D.carrier p (densityFootpoint T Y)])
        (add_le_add le_rfl ((hH p).trans (le_abs_self _))) p
    have hb := mul_le_mul
      (mul_le_mul_of_nonneg_left (hwnorm p) (hmult p)) hpow
      (pow_nonneg (by linarith [cNorm_nonneg D.carrier p (densityFootpoint T Y)]) _)
      (mul_nonneg (hmult p) (mul_nonneg (hA p).le
        (by linarith [cNorm_nonneg (closedBall p₀ (R / 8)) p v])))
    apply hcomp.trans (hb.trans _)
    dsimp only [B]
    nlinarith [cNorm_nonneg (closedBall p₀ (R / 8)) p v]
  refine ⟨hw.comp hY hmap, hhigh, ?_⟩
  intro hvlow
  have hvp : cNorm (closedBall p₀ (R / 8)) (2 * (n + 1) + 1) v ≤ 1 :=
    (cNorm_mono_order (by omega : 2 * (n + 1) + 1 ≤ 2 * (n + 1) + 14)).trans hvlow
  exact (hhigh (2 * (n + 1) + 1)).trans (by nlinarith [hB (2 * (n + 1) + 1)])

end JanetCartan.ContinuumRow.NormalizedCarrierProfiles
