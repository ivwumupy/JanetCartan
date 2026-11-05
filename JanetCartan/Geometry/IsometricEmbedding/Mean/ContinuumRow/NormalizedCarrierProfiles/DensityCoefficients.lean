module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.DensityMultipliers
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# The original density class in the primitive coefficient budgets

The fixed normalized unit carrier has all-order bounds before source scale.
Multiplying its initial scalar by `sqrt (1+v)` changes exactly its normal
coefficient, evaluated at the same ODE inverse label. The derivative product
estimate retains one high density norm. The low `μ+1` reserve is bounded by
the original `q=μ+14` class without asking for `C^(μ+15)` control.

Consumer: the density version of the supported reflected amplitude producer,
`app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedCarrierProfiles
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier NullTransport
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ContinuumNormalReduction.TransportSymbol

private theorem cNorm_smul_on_primitiveChart_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : PrimitiveNormChart E) {f : E → ℝ} {g : E → F}
    (hf : ContDiffOn ℝ ∞ f D.region) (hg : ContDiffOn ℝ ∞ g D.region) (p : ℕ) :
    cNorm D.carrier p (fun x ↦ f x • g x) ≤
      (2 : ℝ) ^ p * cNorm D.carrier p f * cNorm D.carrier p g := by
  obtain ⟨f', hf', _, _, hef⟩ := ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall
    D.center D.radius_pos D.isOpen_region D.ball_subset hf
  obtain ⟨g', hg', _, _, heg⟩ := ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall
    D.center D.radius_pos D.isOpen_region D.ball_subset hg
  have he : ∀ x ∈ closedBall D.center D.radius,
      (fun y ↦ f' y • g' y) =ᶠ[𝓝 x] (fun y ↦ f y • g y) := by
    intro x hx
    filter_upwards [hef x hx, heg x hx] with y hy hz
    rw [hy, hz]
  have h := cNorm_smul_le (isCompact_closedBall D.center D.radius)
    (hf'.of_le (by simp : (p : ℕ∞ω) ≤ ∞)) (hg'.of_le (by simp : (p : ℕ∞ω) ≤ ∞))
  simpa only [GeometricProfile.cNorm_eq_of_eventuallyEq hef p,
    GeometricProfile.cNorm_eq_of_eventuallyEq heg p,
    GeometricProfile.cNorm_eq_of_eventuallyEq he p, PrimitiveNormChart.carrier] using h

/-- Literal coefficient identification for a changed initial scalar. All
three masks and the actual detector are preserved. The only changed field is
the normal multiplied at the retained ODE inverse label. In particular this
applies to `initial = σ` and `weight = sqrt (1+v)`, without replacing the
measure, introducing a frequency cutoff or altering the physical scale.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem coefficientsOfCarrier_initial_mul
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    let d := TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y (fun q ↦ initial q * weight q) hr hcell angular high)
      (FixedCutoffs.physical hr 1) =
        {d with normal := fun p ↦ weight (densityFootpoint T Y p) • d.normal p} := by
  dsimp only
  rw [coefficientsOfCarrier_data, coefficientsOfCarrier_data]
  congr 1
  funext p
  exact normalField_initial_mul T Q F row col Φ Y initial weight p.1 p.2

/-- Existing primitive controls for the normalized unit carrier and the
actual inverse-ODE budgets give the original variable-density coefficient
class. The unit controls are supplied by
`exists_normalizedCarrierData_all_order_controls`; the footpoint budgets are
the `both-normalized-flow-profiles` output. Every new constant precedes the
coefficient, flow and density. No weighted-normal or final-amplitude estimate
is a premise. The high norm of `v` occurs once and the low estimate keeps
exactly the original `q=μ+14` hypothesis
(`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_density_weighted_coefficient_controls
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (D : CoefficientNormCharts n)
    (p₀ : Euclidean (n - 1) × Euclidean 3) {R : ℝ} (hR : 0 < R)
    (H : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) (B : ℕ → ℝ) (hB : ∀ p, 1 ≤ B p) :
    ∃ M' > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ p, 1 ≤ C p) ∧
      ∀ d : Coefficients n N, (∀ p, D.Controls p M (B p) 1 d) →
      ∀ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        ContDiffOn ℝ ∞ (densityFootpoint T Y) D.field.region →
        MapsTo (densityFootpoint T Y) D.field.region (ball p₀ (R / 4)) →
        MapsTo (densityFootpoint T Y) D.field.carrier (closedBall p₀ (R / 8)) →
        (∀ p, cNorm D.field.carrier p (densityFootpoint T Y) ≤ H p) →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
        ContDiffOn ℝ ∞ v (ball p₀ (R / 4)) →
        (∀ q ∈ ball p₀ (R / 4), 0 < 1 + v q) →
        (∀ q ∈ closedBall p₀ (R / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        cNorm (closedBall p₀ (R / 8)) (2 * (n + 1) + 14) v ≤ 1 →
        let weighted := {d with normal := fun p ↦ Real.sqrt (1 + v (densityFootpoint T Y p)) • d.normal p}
        (∀ p, D.Controls p M' (C p) (1 + cNorm (closedBall p₀ (R / 8)) p v) weighted) ∧
        D.Controls (2 * (n + 1) + 1) M' (2 * C (2 * (n + 1) + 1)) 1 weighted := by
  obtain ⟨A, hA, hweight⟩ := exists_densityFootpoint_sqrt_one_high_bounds T D.field p₀ hR H
  let M' := M + 4 * A 1 * M + 1
  let C := fun p ↦ (2 : ℝ) ^ p * A p * B p + B p + 1
  have hC (p) : 1 ≤ C p := by
    have hpow := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p
    have hAB := mul_nonneg (mul_nonneg hpow (hA p).le) (zero_le_one.trans (hB p))
    dsimp only [C]
    linarith [hB p]
  have hMM : M ≤ M' := by
    dsimp only [M']
    nlinarith [hA 1]
  refine ⟨M', by dsimp only [M']; have := hA 1; positivity, C, hC, ?_⟩
  intro d hd Y hY hmap hcompact hH v hv hpos hinterval hvlow
  obtain ⟨hw, hwbound, _⟩ := hweight Y hY hmap hcompact hH v hv hpos hinterval
  let w := fun p ↦ Real.sqrt (1 + v (densityFootpoint T Y p))
  have hνsm := (hd 0).normal.smooth
  have hvone : cNorm (closedBall p₀ (R / 8)) 1 v ≤ 1 :=
    (cNorm_mono_order (by omega : 1 ≤ 2 * (n + 1) + 14)).trans hvlow
  have hwlow : cNorm D.field.carrier 1 w ≤ 2 * A 1 :=
    (hwbound 1).trans (by nlinarith [hA 1])
  have hnormalLow : cNorm D.field.carrier 1 (fun p ↦ w p • d.normal p) ≤ M' := by
    have hp := cNorm_smul_on_primitiveChart_le D.field hw hνsm 1
    have hb := mul_le_mul
      (mul_le_mul_of_nonneg_left hwlow (by norm_num : (0 : ℝ) ≤ 2 ^ 1))
      (hd 1).normal.low (cNorm_nonneg ..)
      (by have := hA 1; positivity : 0 ≤ (2 : ℝ) ^ 1 * (2 * A 1))
    apply hp.trans (hb.trans _)
    dsimp only [M']
    nlinarith
  have hhigh (p) : 1 + cNorm D.field.carrier p (fun q ↦ w q • d.normal q) ≤
      C p * (1 + cNorm (closedBall p₀ (R / 8)) p v) := by
    have hν : cNorm D.field.carrier p d.normal ≤ B p := by
      have h := (hd p).normal.high
      simp only [mul_one] at h
      linarith
    have hp := cNorm_smul_on_primitiveChart_le D.field hw hνsm p
    have hb := mul_le_mul
      (mul_le_mul_of_nonneg_left (hwbound p) (by positivity : 0 ≤ (2 : ℝ) ^ p)) hν
      (cNorm_nonneg ..)
      (mul_nonneg (by positivity) (mul_nonneg (hA p).le
        (by linarith [cNorm_nonneg (closedBall p₀ (R / 8)) p v])))
    have h := hp.trans hb
    dsimp only [C]
    nlinarith [cNorm_nonneg (closedBall p₀ (R / 8)) p v, hB p]
  have hunchanged {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      (D₀ : PrimitiveNormChart E) {f : E → F} (p) (hf : D₀.Controls p M (B p) 1 f) :
      D₀.Controls p M' (C p) (1 + cNorm (closedBall p₀ (R / 8)) p v) f := by
    refine ⟨hf.smooth, hf.low.trans hMM, hf.high.trans ?_⟩
    have hBC : B p ≤ C p := by
      dsimp only [C]
      have := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
        (hA p).le) (zero_le_one.trans (hB p))
      linarith
    exact mul_le_mul hBC
      (by linarith [cNorm_nonneg (closedBall p₀ (R / 8)) p v]) zero_le_one (zero_le_one.trans (hC p))
  have hall (p) : D.Controls p M' (C p) (1 + cNorm (closedBall p₀ (R / 8)) p v)
      {d with normal := fun q ↦ w q • d.normal q} :=
    ⟨hunchanged _ p (hd p).measurement, hunchanged _ p (hd p).angular,
      hunchanged _ p (hd p).high, ⟨hw.smul hνsm, hnormalLow, hhigh p⟩,
      hunchanged _ p (hd p).reduced⟩
  refine ⟨hall, ?_⟩
  have hvp : cNorm (closedBall p₀ (R / 8)) (2 * (n + 1) + 1) v ≤ 1 :=
    (cNorm_mono_order (by omega : 2 * (n + 1) + 1 ≤ 2 * (n + 1) + 14)).trans hvlow
  have hbudget : C (2 * (n + 1) + 1) *
      (1 + cNorm (closedBall p₀ (R / 8)) (2 * (n + 1) + 1) v) ≤
        (2 * C (2 * (n + 1) + 1)) * 1 := by
    nlinarith [hC (2 * (n + 1) + 1)]
  have h := hall (2 * (n + 1) + 1)
  exact ⟨⟨h.measurement.smooth, h.measurement.low, h.measurement.high.trans hbudget⟩,
    ⟨h.angular.smooth, h.angular.low, h.angular.high.trans hbudget⟩,
    ⟨h.high.smooth, h.high.low, h.high.high.trans hbudget⟩,
    ⟨h.normal.smooth, h.normal.low, h.normal.high.trans hbudget⟩,
    ⟨h.reduced.smooth, h.reduced.low, h.reduced.high.trans hbudget⟩⟩

end JanetCartan.ContinuumRow.NormalizedCarrierProfiles
