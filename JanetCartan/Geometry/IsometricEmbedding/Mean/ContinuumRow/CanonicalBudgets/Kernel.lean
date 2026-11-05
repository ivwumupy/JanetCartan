module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Masks

/-!
# Finite-kernel premises for the literal canonical carrier

The support of the actual measurement and angular masks restricts every
nonzero amplitude to a fixed compact primitive domain. Zero extension of
local continuous primitives proves measurability without any global
regularity assumption outside the construction buffers. The frequency
weight stays exactly `sqrt ‖η‖`, and the carrier measure is unchanged.
Consumer: `exists_carrierL2Extension_globalNormal_of_primitiveNorms`;
source: `app:ch_background:eq:bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase
open AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)

/-- Local continuity on the actual support buffers implies strong
measurability of the literal zero-extended kernel. These regularity inputs
are supplied by the canonical phase, normal reconstruction and projected
quadratic theorems; no carrier operator bound is used.
Source: `app:ch_background:eq:bg-T`. -/
theorem stronglyMeasurable_carrierKernel_of_local_primitives
    {O : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O)
    (hpos : ContinuousOn (transportPosition T Q) O)
    (hν : ContinuousOn (Function.uncurry (normalField T Q F row col Φ Y initial)) O)
    (hq : ContinuousOn (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))) O)
    (hang : Continuous (Function.uncurry angular))
    {Zp : Set CarrierParameter} (hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ O) :
    StronglyMeasurable (Function.uncurry (carrierKernel
      (data T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency))) := by
  classical
  let ν := Function.uncurry (normalField T Q F row col Φ Y initial)
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))
  let ψ := fun p : Torus n × CarrierVariable n ↦ (centeredTorusRepresentative p.1, p.2.1)
  have hψ : Measurable ψ :=
    (measurable_centeredTorusRepresentative.comp measurable_fst).prodMk measurable_snd.fst
  have hp0 : Measurable (O.indicator (transportPosition T Q)) :=
    hpos.measurable_piecewise continuousOn_const hO.measurableSet
  have hn0 : Measurable (O.indicator ν) :=
    hν.measurable_piecewise continuousOn_const hO.measurableSet
  have hq0 : Measurable (O.indicator q) :=
    hq.measurable_piecewise continuousOn_const hO.measurableSet
  let v := fun p : Torus n × CarrierVariable n ↦
    ((FixedCutoffs.periodic hr hcell 1 p.1 *
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) * FixedCutoffs.highFrequency ‖p.2.2‖ *
      Real.sqrt ‖p.2.2‖ * ‖O.indicator ν (ψ p)‖ ^ 2) • O.indicator q (ψ p))
  have hη : Measurable (fun p : Torus n × CarrierVariable n ↦ p.2.2) := measurable_snd.snd
  have hang' : Measurable (fun p : Torus n × CarrierVariable n ↦
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2)) :=
    hang.measurable.comp (measurable_snd.fst.prodMk (hη.norm.inv.smul hη))
  have hv : Measurable v :=
    (((((FixedCutoffs.periodic hr hcell 1).continuous.measurable.comp measurable_fst).mul hang').mul
      (FixedCutoffs.highFrequency_smooth.continuous.measurable.comp hη.norm)).mul
        (Real.continuous_sqrt.measurable.comp hη.norm)).mul
          ((hn0.comp hψ).norm.pow_const 2) |>.smul (hq0.comp hψ)
  let k := fun p : Torus n × CarrierVariable n ↦
    Complex.exp (Complex.I * (inner ℝ (O.indicator (transportPosition T Q) (ψ p)) p.2.2 : ℂ)) •
      euclideanComplexInclusion (v p)
  have hk : Measurable k := by
    dsimp only [k]
    apply Measurable.smul (M := ℂ) (X := EuclideanSpace ℂ (Fin n))
    · exact Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          ((continuous_fst.inner continuous_snd).measurable.comp ((hp0.comp hψ).prodMk hη))))
    · exact euclideanComplexInclusion.continuous.measurable.comp hv
  have hchart : MeasurableSet (torusChart (closedBall (0 : Euclidean n) (4 * r))) :=
    measurableSet_torusChart isClosed_closedBall.measurableSet
  have he : Function.uncurry (carrierKernel
      (data T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency)) =
      ((torusChart (closedBall (0 : Euclidean n) (4 * r))) ×ˢ univ).indicator k := by
    funext p
    simp only [Function.uncurry]
    by_cases hx : p.1 ∈ torusChart (closedBall (0 : Euclidean n) (4 * r))
    · by_cases hm : FixedCutoffs.physical hr 1 (centeredTorusRepresentative p.1) = 0
      · simp [carrierKernel, carrierAmplitude, data, hx, k, v, hm]
      · by_cases ha : angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) = 0
        · simp [carrierKernel, carrierAmplitude, data, hx, k, v, ha]
        · have hz : p.2.1 ∈ Zp := by
            by_contra hh
            exact ha (hangular _ hh _)
          have hp : ψ p ∈ O := hsupport ⟨subset_tsupport _ hm, hz⟩
          simp only [carrierKernel, carrierPhase, carrierAmplitude, reducedCovector_data]
          simp [data, hx, k, v, hp, ψ, ν, q]
    · simp [carrierKernel, data, hx]
  rw [he]
  exact (hk.indicator (hchart.prod MeasurableSet.univ)).stronglyMeasurable


/-- The literal half-order amplitude bound from compact primitive norms.
The normal and detector inputs are the low conclusions of
`exists_projected_normalField_bounds` and
`exists_projected_canonical_quadratic_bounds`; the angular contribution is
its actual fixed compact norm. The original square-root weight is preserved.
Source: `app:ch_background:eq:bg-T`. -/
theorem norm_carrierAmplitude_le_of_primitive_norms
    (D : ContinuumNormalReduction.TransportSymbol.PrimitiveNormChart
      (Euclidean n × CarrierParameter))
    {Zp : Set CarrierParameter} (hZp : IsCompact Zp)
    (hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
    (hang : ContDiff ℝ ∞ (Function.uncurry angular))
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ D.carrier)
    (hν : ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col Φ Y initial)) D.region)
    (hq : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))) D.region)
    {Mν Mq : ℝ} (hMν : 0 ≤ Mν) (hMq : 0 ≤ Mq)
    (hνM : cNorm D.carrier 1 (Function.uncurry (normalField T Q F row col Φ Y initial)) ≤ Mν)
    (hqM : cNorm D.carrier 1 (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))) ≤ Mq)
    (x : Torus n) (u : CarrierVariable n) :
    ‖carrierAmplitude (data T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency)
      x u‖ ≤
      (cNorm (Zp ×ˢ closedBall (0 : Euclidean (n - 1)) 1) 0 (Function.uncurry angular) *
        Mν ^ 2 * Mq) * Real.sqrt ‖u.2‖ := by
  let Cang := cNorm (Zp ×ˢ closedBall (0 : Euclidean (n - 1)) 1) 0 (Function.uncurry angular)
  have hCa : 0 ≤ Cang := cNorm_nonneg ..
  have hRHS : 0 ≤ Cang * Mν ^ 2 * Mq * Real.sqrt ‖u.2‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hCa (sq_nonneg _)) hMq) (Real.sqrt_nonneg _)
  by_cases hm : FixedCutoffs.physical hr 1 (centeredTorusRepresentative x) = 0
  · simpa [carrierAmplitude, data, hm] using hRHS
  by_cases ha : angular u.1 (‖u.2‖⁻¹ • u.2) = 0
  · simpa [carrierAmplitude, data, ha] using hRHS
  have hz : u.1 ∈ Zp := by
    by_contra hh
    exact ha (hangular _ hh _)
  have hp : (centeredTorusRepresentative x, u.1) ∈ D.carrier :=
    hsupport ⟨subset_tsupport _ hm, hz⟩
  have hn : ‖normalField T Q F row col Φ Y initial (centeredTorusRepresentative x) u.1‖ ≤ Mν := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall D.center D.radius)
      (fun p hp ↦ (hν.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hp))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hp (Nat.zero_le 1)
    apply le_trans _ hνM
    simpa only [norm_iteratedFDeriv_zero, Function.uncurry,
      ContinuumNormalReduction.TransportSymbol.PrimitiveNormChart.carrier] using hh
  have hq' : ‖quadratic (Q.1 (centeredTorusRepresentative x))
      (T.carrierGradient Q (centeredTorusRepresentative x) (parameter u.1))‖ ≤ Mq := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall D.center D.radius)
      (fun p hp ↦ (hq.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hp))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hp (Nat.zero_le 1)
    apply le_trans _ hqM
    simpa only [norm_iteratedFDeriv_zero,
      ContinuumNormalReduction.TransportSymbol.PrimitiveNormChart.carrier] using hh
  have hdir : ‖u.2‖⁻¹ • u.2 ∈ closedBall (0 : Euclidean (n - 1)) 1 := by
    rw [mem_closedBall_zero_iff]
    by_cases h : u.2 = 0
    · simp [h]
    · exact (norm_smul_inv_norm h).le
  have hangM : ‖angular u.1 (‖u.2‖⁻¹ • u.2)‖ ≤ Cang := by
    simpa only [norm_iteratedFDeriv_zero, Function.uncurry] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (hZp.prod (isCompact_closedBall (0 : Euclidean (n - 1)) 1))
        (fun p _ ↦ hang.contDiffAt.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
        (show (u.1, ‖u.2‖⁻¹ • u.2) ∈ Zp ×ˢ closedBall 0 1 from ⟨hz, hdir⟩) (le_refl 0)
  have hmeas : ‖FixedCutoffs.periodic hr hcell 1 x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (FixedCutoffs.periodic_mem_Icc hr hcell 1 x).1]
    exact (FixedCutoffs.periodic_mem_Icc hr hcell 1 x).2
  have hhigh : ‖FixedCutoffs.highFrequency ‖u.2‖‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc _).1]
    exact (FixedCutoffs.highFrequency_mem_Icc _).2
  rw [carrierAmplitude, reducedCovector_data, norm_smul]
  change ‖FixedCutoffs.periodic hr hcell 1 x * angular u.1 (‖u.2‖⁻¹ • u.2) *
    FixedCutoffs.highFrequency ‖u.2‖ * Real.sqrt ‖u.2‖ *
    ‖normalField T Q F row col Φ Y initial (centeredTorusRepresentative x) u.1‖ ^ 2‖ * _ ≤ _
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Real.norm_eq_abs (Real.sqrt _),
    abs_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs (_ ^ 2), abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (1 * Cang * 1 * Real.sqrt ‖u.2‖ * Mν ^ 2) * Mq := by
      apply mul_le_mul _ hq' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ (sq_le_sq₀ (norm_nonneg _) hMν |>.mpr hn) (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hmeas hangM (norm_nonneg _) zero_le_one) hhigh
          (norm_nonneg _) (by positivity)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end JanetCartan.ContinuumRow.CanonicalCarrier
