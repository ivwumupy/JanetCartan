module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel.Coefficients

/-!
# Finite-kernel and torus-extension inputs with refined masks

The original compact carrier support is inside the outer seed buffer even
when the angular width and physical mask use different smaller radii. These
proofs discharge the finite-kernel and extension premises of
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms` for the
literal unit-initial normalized carrier. Sources: `new:lem:scaling`,
`app:ch_background:eq:bg-T`, and `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

section Kernel
variable {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)

private theorem stronglyMeasurable_refinedFrozenKernel_of_local_primitives
    {O : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O)
    (hpos : ContinuousOn (normalizedTransportPosition T Q 0) O)
    (hν : ContinuousOn (fun p : Euclidean n × CarrierParameter ↦ normalField T Q F row col Φ Y initial 0 p.2) O)
    (hq : ContinuousOn (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2))) O)
    (hang : Continuous (Function.uncurry angular))
    {Zp : Set CarrierParameter} (hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ O) :
    StronglyMeasurable (Function.uncurry (carrierKernel
      (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency 0))) := by
  classical
  let ν := (fun p : Euclidean n × CarrierParameter ↦ normalField T Q F row col Φ Y initial 0 p.2)
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2))
  let ψ := fun p : Torus n × CarrierVariable n ↦ (centeredTorusRepresentative p.1, p.2.1)
  have hψ : Measurable ψ :=
    (measurable_centeredTorusRepresentative.comp measurable_fst).prodMk measurable_snd.fst
  have hp0 : Measurable (O.indicator (normalizedTransportPosition T Q 0)) :=
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
    Complex.exp (Complex.I * (inner ℝ (O.indicator (normalizedTransportPosition T Q 0) (ψ p)) p.2.2 : ℂ)) •
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
      (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency 0)) =
      ((torusChart (closedBall (0 : Euclidean n) (4 * r))) ×ˢ univ).indicator k := by
    funext p
    simp only [Function.uncurry]
    by_cases hx : p.1 ∈ torusChart (closedBall (0 : Euclidean n) (4 * r))
    · by_cases hm : FixedCutoffs.physical hr 1 (centeredTorusRepresentative p.1) = 0
      · simp [carrierKernel, carrierAmplitude, normalizedCarrierData, data, hx, k, v, hm]
      · by_cases ha : angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) = 0
        · simp [carrierKernel, carrierAmplitude, normalizedCarrierData, data, hx, k, v, ha]
        · have hz : p.2.1 ∈ Zp := by
            by_contra hh
            exact ha (hangular _ hh _)
          have hp : ψ p ∈ O := hsupport ⟨subset_tsupport _ hm, hz⟩
          simp only [carrierKernel, ContinuumRow.carrierPhase, carrierAmplitude,
            normalizedCarrierData_reduced_zero, normalizedCarrierData_covector_zero]
          simp [normalizedCarrierData, data, hx, k, v, hp, ψ, ν, q, normalizedNormal_zero]
    · simp [carrierKernel, normalizedCarrierData, data, hx]
  rw [he]
  exact (hk.indicator (hchart.prod MeasurableSet.univ)).stronglyMeasurable

end Kernel

/-- The finite-kernel premises for the smaller masks follow from the outer
carrier buffer and the actual unit seed fields. No normal, detector, flow
regularity, or operator bound is assumed (`new:lem:scaling`, `bg-T`). -/
theorem frozenRefinedCarrier_finite_kernel_inputs
    {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (_hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (haa : a' ≤ a) (hcell' : 4 * a' < 1 / 2) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell' angular
      FixedCutoffs.highFrequency 0
    StronglyMeasurable (Function.uncurry (carrierKernel e)) ∧
      ∃ Cmask ≥ (0 : ℝ), ∀ x u, ‖carrierAmplitude e x u‖ ≤ Cmask * Real.sqrt ‖u.2‖ := by
  dsimp only
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  let Z := ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)
  let O := (univ : Set (Euclidean n)) ×ˢ Z
  let Zp := carrierSupport z₀ (r := a')
  let ν := fun z : CarrierParameter ↦ normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z
  let q := fun z : CarrierParameter ↦ quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter z))
  have hZ : Z ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2) := by
    intro z hz
    exact hcarrier ⟨(ball_subset_closedBall.trans (closedBall_subset_closedBall har)) hz.2,
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hz.1⟩
  have hZ' : Z ⊆ parameter ⁻¹' parameterInterior (2 * P.radius) :=
    fun z hz i ↦ (hZ hz i).trans_le (by linarith [hP.1])
  have hS : Zp ⊆ Z := by
    intro z hz
    exact ⟨closedBall_subset_ball (by linarith) hz.1,
      closedBall_subset_ball (by linarith) hz.2⟩
  have hν : ContDiffOn ℝ ∞ ν Z :=
    (frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).mono hZ'
  have hq : ContDiffOn ℝ ∞ q Z := (frozenSeedDetector_smooth T Q hP).mono hZ'
  have hpos : ContinuousOn (normalizedTransportPosition T Q 0) O :=
    ((normalizedTransportPosition_zero_smooth T Q hP).mono
      (fun p hp ↦ ⟨hp.1, hZ hp.2⟩)).continuousOn
  constructor
  · exact stronglyMeasurable_refinedFrozenKernel_of_local_primitives T Q F row col Φ Y (fun _ ↦ 1)
      ha' hcell' angular (isOpen_univ.prod (isOpen_ball.prod isOpen_ball)) hpos
      (hν.continuousOn.comp continuousOn_snd (fun _ hp ↦ hp.2))
      (hq.continuousOn.comp continuousOn_snd (fun _ hp ↦ hp.2))
      (angularMask_smooth z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1).continuous
      (fun z hz θ ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
        (angularWidth_spec hηb hr').1 hz θ) (fun p hp ↦ ⟨mem_univ _, hS hp.2⟩)
  obtain ⟨Bn, hn⟩ := (carrierSupport_compact z₀ (r := a')).exists_bound_of_continuousOn
    (hν.continuousOn.mono hS)
  obtain ⟨Bq, hqbound⟩ := (carrierSupport_compact z₀ (r := a')).exists_bound_of_continuousOn
    (hq.continuousOn.mono hS)
  let Mn := max 0 Bn
  let Mq := max 0 Bq
  have hMn : 0 ≤ Mn := le_max_left _ _
  have hMq : 0 ≤ Mq := le_max_left _ _
  refine ⟨Mn ^ 2 * Mq, mul_nonneg (sq_nonneg _) hMq, ?_⟩
  intro x u
  rw [carrierAmplitude_normalizedCarrierData_zero]
  have hRHS : 0 ≤ Mn ^ 2 * Mq * Real.sqrt ‖u.2‖ := by positivity
  by_cases hang : angular u.1 (‖u.2‖⁻¹ • u.2) = 0
  · dsimp only [angular] at hang
    simpa only [hang, mul_zero, zero_mul, zero_smul, norm_zero] using hRHS
  have hz : u.1 ∈ Zp := by
    by_contra hz
    exact hang (angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz _)
  have hn' : ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 u.1‖ ≤ Mn :=
    (hn u.1 hz).trans (le_max_right _ _)
  have hq' : ‖quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter u.1))‖ ≤ Mq :=
    (hqbound u.1 hz).trans (le_max_right _ _)
  have hang' : ‖angular u.1 (‖u.2‖⁻¹ • u.2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (angularMask_mem_Icc z₀
      (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 _ _).1]
    exact (angularMask_mem_Icc z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 _ _).2
  have hm : ‖FixedCutoffs.periodic ha' hcell' 1 x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (FixedCutoffs.periodic_mem_Icc ha' hcell' 1 x).1]
    exact (FixedCutoffs.periodic_mem_Icc ha' hcell' 1 x).2
  have hh : ‖FixedCutoffs.highFrequency ‖u.2‖‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc _).1]
    exact (FixedCutoffs.highFrequency_mem_Icc _).2
  rw [norm_smul, norm_mul, norm_mul, norm_mul, norm_mul,
    Real.norm_eq_abs (Real.sqrt _), abs_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_eq_abs (_ ^ 2), abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (1 * 1 * 1 * Real.sqrt ‖u.2‖ * Mn ^ 2) * Mq := by
      apply mul_le_mul _ hq' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ (sq_le_sq₀ (norm_nonneg _) hMn |>.mpr hn')
        (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hm hang' (norm_nonneg _) zero_le_one) hh
          (norm_nonneg _) (by norm_num)) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The original compact carrier-parameter support and the torus chart
supply the supported constructor's literal support and measurement-extension
premises. The extension is the existing source cutoff, equal to one on the
measurement support (`app:ch_background:defn:bg-row`, `bg-T`). -/
theorem frozenRefinedCarrier_support_extension_inputs
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} {r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a') (hcell' : 4 * a' < 1 / 2) :
    let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell' angular
      FixedCutoffs.highFrequency 0
    let Zp := carrierSupport z₀ (r := a')
    let Kout := closedBall (0 : Euclidean n) (4 * a')
    let χ : Euclidean n → ℝ := FixedCutoffs.physical ha' 2
    IsCompact Zp ∧ (∀ z ∉ Zp, ∀ η, e.angularCutoff z η = 0) ∧
      Kout ⊆ halfOpenCell n ∧ e.outputChart = torusChart Kout ∧
      (∀ z ∈ e.outputChart, e.chartPoint z = centeredTorusRepresentative z) ∧
      (∀ y ∉ Kout, χ y = 0) ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, FixedCutoffs.physical ha' 1 y ≠ 0 → χ y = 1) := by
  dsimp only
  exact ⟨carrierSupport_compact z₀,
    fun z hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η,
    FixedCutoffs.closedBall_four_subset_cell hcell', rfl, fun _ _ ↦ rfl,
    fun _ hy ↦ FixedCutoffs.physical_eq_zero_outside_four ha' 2 hy,
    (FixedCutoffs.physical ha' 2).contDiff, (FixedCutoffs.physical ha' 2).hasCompactSupport,
    fun _ hy ↦ FixedCutoffs.source_one_on_measurement ha' hy⟩

end JanetCartan.ContinuumNormal.FrozenModel
