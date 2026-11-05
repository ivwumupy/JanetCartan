module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceCoefficientBounds

/-!
# All-order coefficient budgets on one normalized scale interval

The coefficients are extracted from the literal `normalizedCarrierData`, with
the same seed, scalar flow, carrier relabeling and masks. Source contraction
keeps their entire compact range in the seed smoothness domain. Consequently
one interval works at every order; it is not obtained by intersecting the
order-dependent intervals of the finite convergence estimate.

Consumer: the full reflected amplitude budgets for
`ContinuumCommutator.exists_normalized_row_elliptic_estimates`.
Sources: `app:ch_background:eq:bg-Nsigma`,
`app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:prop:bg-normalized`.

The initial scalar is fixed before these constants. Uniformity over variable
densities requires the separate one-high estimates, not this compactness step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedCarrierProfiles
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier NullTransport
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open NormalizedBackground NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol LeadingWave AmbientResponse

private theorem exists_cNorm_contracted_seed_bounds
    {E Z H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E × Z → H} {R : ℝ} (hR : 0 < R)
    {V : Set Z} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (ball 0 R ×ˢ V))
    {K : Set (E × Z)} (hK : IsCompact K) (hKV : K ⊆ ball 0 R ×ˢ V) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧ ∀ σ ∈ Icc (0 : ℝ) 1, ∀ m,
      cNorm K m (fun p ↦ f (σ • p.1, p.2)) ≤ B m := by
  let L := (fun q : ℝ × (E × Z) ↦ (q.1 • q.2.1, q.2.2)) '' (Icc (0 : ℝ) 1 ×ˢ K)
  have hL : IsCompact L := (isCompact_Icc.prod hK).image
    ((continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd)
  have hLU : L ⊆ ball 0 R ×ˢ V := by
    rintro _ ⟨⟨σ, p⟩, ⟨hσ, hp⟩, rfl⟩
    exact ⟨(convex_ball (0 : E) R).smul_mem_of_zero_mem
      (mem_ball_self hR) (hKV hp).1 hσ, (hKV hp).2⟩
  refine ⟨fun m ↦ (m + 1 : ℝ) * cNorm L m f + 1,
    fun m ↦ by have := cNorm_nonneg L m f; positivity, ?_⟩
  intro σ hσ m
  let A : E × Z →L[ℝ] E × Z :=
    (σ • ContinuousLinearMap.fst ℝ E Z).prod (ContinuousLinearMap.snd ℝ E Z)
  have hA : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound zero_le_one
    intro p
    change max ‖σ • p.1‖ ‖p.2‖ ≤ 1 * ‖p‖
    rw [one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
    exact max_le ((mul_le_of_le_one_left (norm_nonneg _) hσ.2).trans
      (norm_fst_le p)) (norm_snd_le p)
  have hU : IsOpen (ball (0 : E) R ×ˢ V) := isOpen_ball.prod hV
  have hb : cNorm K m (f ∘ A) ≤ (m + 1 : ℝ) * cNorm L m f := by
    have hb := cNorm_le_sum_of_bounds (s := K) (r := m) (f := f ∘ A)
      (C := fun _ ↦ cNorm L m f) (fun _ _ ↦ cNorm_nonneg ..) (by
        intro j hj p hp
        have hpL : A p ∈ L := ⟨(σ, p), ⟨hσ, hp⟩, rfl⟩
        have hpU := hLU hpL
        have he := A.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
          (hU.preimage A.continuous).uniqueDiffOn hpU (i := j) (by simp)
        rw [iteratedFDerivWithin_of_isOpen _ (hU.preimage A.continuous) hpU,
          iteratedFDerivWithin_of_isOpen _ hU hpU] at he
        rw [he]
        apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        have hprod : (∏ _ : Fin j, ‖A‖) ≤ 1 :=
          Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hA)
        apply (mul_le_of_le_one_right (norm_nonneg _) hprod).trans
        exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
          (fun x hx ↦ (hf.contDiffAt (hU.mem_nhds (hLU hx))).of_le (by simp)) hpL hj)
    simpa using hb
  exact hb.trans (by linarith)

/-- The actual normalized carrier has one fixed low coefficient budget and
all high coefficient budgets on the whole supplied contraction interval.
The constants precede both the order and scale; no amplitude bound, normal
bound or inverse-regularity estimate is assumed. The seed null smoothness is
the output of the retained positive scalar transport. This is the coefficient
input to the full reflected normal in
`app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:prop:bg-normalized`. The seed scalar is fixed here. -/
theorem exists_normalizedCarrierData_all_order_controls
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (measurement : Euclidean n → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y initial (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hm : ContDiffOn ℝ ∞ measurement D.measurement.region)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region) :
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ) measurement
    ∃ M > (0 : ℝ), ∃ B : ℕ → ℝ, (∀ p, 1 ≤ B p) ∧
      ∀ σ ∈ Icc (0 : ℝ) 1, ∀ p, D.Controls p M (B p) 1 (a σ) := by
  let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ) measurement
  have hVP' : ∀ z ∈ V, parameter z ∈ parameterInterior (2 * P.radius) :=
    fun z hz i ↦ (hVP hz i).trans (by linarith only [hP.1])
  have hξ : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      T.carrierGradient Q₀ q.1 (parameter q.2)) (ball 0 R ×ˢ V) := by
    have harg : ContDiffOn ℝ ∞
        (fun q : Euclidean n × CarrierParameter ↦ (q.1, parameter q.2)) (ball 0 R ×ˢ V) :=
      contDiffOn_fst.prodMk (parameter.contDiff.comp_contDiffOn contDiffOn_snd)
    simpa only [Function.comp_def] using (T.carrierGradient_smooth hP Q₀).comp harg
      (fun q hq ↦ ⟨ball_subset_ball hRT hq.1, hVP' q.2 hq.2⟩)
  have hν := contDiffOn_canonicalPrincipalNormal isOpen_ball (hF.mono hRU)
    (fun x hx ↦ hi x (hRU hx)) (fun x hx ↦ hrank x (hRU hx))
    (U := ball 0 R ×ˢ V) (fun _ hp ↦ hp.1) hξ hb
  have hstress : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      ProjectedStressFrame.projectedStress F p.1) (ball 0 R ×ˢ V) :=
    (contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress isOpen_ball
      (hF.mono hRU) (fun x hx ↦ hi x (hRU hx)) (fun x hx ↦ hrank x (hRU hx)))).comp
        contDiffOn_fst (fun _ hp ↦ hp.1)
  have hq := PiLp.contDiff_ofLp.comp_contDiffOn
    (ActualCarriers.contDiff_quadratic.comp_contDiffOn (hstress.prodMk hξ))
  obtain ⟨Bn, hBn, hn⟩ := exists_cNorm_contracted_seed_bounds hR hV hν
    (isCompact_closedBall D.field.center D.field.radius) (D.field.ball_subset.trans hD)
  obtain ⟨Bq, hBq, hqbound⟩ := exists_cNorm_contracted_seed_bounds hR hV hq
    (isCompact_closedBall D.field.center D.field.radius) (D.field.ball_subset.trans hD)
  have hfields (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
      ContDiffOn ℝ ∞ (a σ).normal D.field.region ∧
      ContDiffOn ℝ ∞ (a σ).reduced D.field.region ∧
      ∀ p, cNorm D.field.carrier p (a σ).normal ≤ Bn p ∧
        cNorm D.field.carrier p (a σ).reduced ≤ Bq p := by
    have hmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (σ • p.1, p.2))
        D.field.region (ball 0 R ×ˢ V) := fun p hp ↦
      ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
        (mem_ball_self hR) (hD hp).1 hσ, (hD hp).2⟩
    have heq (p) (hp : p ∈ D.field.region) :=
      coefficientsOfCarrier_normalizedCarrierData_eq_source T Q₀ F row col Φ Y initial
        hr hcell angular high measurement hP hseed
        (ball_subset_ball hRT (hmaps hp).1) (hVP' p.2 (hmaps hp).2)
    refine ⟨(hν.comp ((contDiffOn_fst.const_smul σ).prodMk contDiffOn_snd) hmaps).congr
        (fun p hp ↦ (heq p hp).1),
      (hq.comp ((contDiffOn_fst.const_smul σ).prodMk contDiffOn_snd) hmaps).congr
        (fun p hp ↦ (heq p hp).2), ?_⟩
    intro p
    constructor
    · exact (GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦
        Filter.eventuallyEq_of_mem (D.field.isOpen_region.mem_nhds (D.field.ball_subset hx))
          (fun y hy ↦ (heq y hy).1)) p).trans_le (hn σ hσ p)
    · exact (GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦
        Filter.eventuallyEq_of_mem (D.field.isOpen_region.mem_nhds (D.field.ball_subset hx))
          (fun y hy ↦ (heq y hy).2)) p).trans_le (hqbound σ hσ p)
  let B := fun p ↦ cNorm D.measurement.carrier p measurement +
    cNorm D.angular.carrier p (fun q ↦ angular q.1 q.2) +
    cNorm D.high.carrier p high + Bn p + Bq p + 1
  have hparts (p) :
      cNorm D.measurement.carrier p measurement ≤ B p - 1 ∧
      cNorm D.angular.carrier p (fun q ↦ angular q.1 q.2) ≤ B p - 1 ∧
      cNorm D.high.carrier p high ≤ B p - 1 ∧ Bn p ≤ B p - 1 ∧ Bq p ≤ B p - 1 := by
    have h₁ := cNorm_nonneg D.measurement.carrier p measurement
    have h₂ := cNorm_nonneg D.angular.carrier p (fun q ↦ angular q.1 q.2)
    have h₃ := cNorm_nonneg D.high.carrier p high
    have h₄ := (hBn p).le
    have h₅ := (hBq p).le
    dsimp only [B]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hB (p) : 1 ≤ B p := by linarith [(hparts p).2.2.2.1, hBn p]
  refine ⟨B 1, lt_of_lt_of_le zero_lt_one (hB 1), B, hB, ?_⟩
  intro σ hσ p
  obtain ⟨hnsm, hqsm, hnb⟩ := hfields σ hσ
  refine ⟨⟨hm, ?_, ?_⟩, ⟨ha, ?_, ?_⟩, ⟨hh, ?_, ?_⟩,
    ⟨hnsm, ?_, ?_⟩, ⟨hqsm, ?_, ?_⟩⟩
  all_goals dsimp only [a, TransportKernel.coefficientsOfCarrier,
    normalizedCarrierData, data] at *
  · linarith [(hparts 1).1]
  · simpa only [mul_one] using (show 1 + cNorm D.measurement.carrier p measurement ≤ B p by
      linarith [(hparts p).1])
  · linarith [(hparts 1).2.1]
  · simpa only [mul_one] using (show 1 + cNorm D.angular.carrier p
      (fun q ↦ angular q.1 q.2) ≤ B p by linarith [(hparts p).2.1])
  · linarith [(hparts 1).2.2.1]
  · simpa only [mul_one] using (show 1 + cNorm D.high.carrier p high ≤ B p by
      linarith [(hparts p).2.2.1])
  · exact (hnb 1).1.trans ((hparts 1).2.2.2.1.trans (by linarith))
  · simpa only [mul_one] using (show 1 + cNorm D.field.carrier p _ ≤ B p by
      linarith [(hnb p).1, (hparts p).2.2.2.1])
  · exact (hnb 1).2.trans ((hparts 1).2.2.2.2.trans (by linarith))
  · simpa only [mul_one] using (show 1 + cNorm D.field.carrier p _ ≤ B p by
      linarith [(hnb p).2, (hparts p).2.2.2.2])

end JanetCartan.ContinuumRow.NormalizedCarrierProfiles
