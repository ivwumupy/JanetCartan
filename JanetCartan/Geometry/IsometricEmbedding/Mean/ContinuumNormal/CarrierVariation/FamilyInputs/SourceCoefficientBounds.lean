module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficients

/-!
# Common finite bounds for the actual normalized coefficients

The coefficient comparison needs absolute primitive norms as well as their
already proved differences. These bounds are derived from the literal seed
fields, on the same coefficient charts, before the density is chosen.
Consumer: `SeedAssembly` and `WideDensity.CanonicalComparison`, for
`app:ch_background:prop:bg-normalized` and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NormalizedBackground NormalizedBackground.SourceGeometry NullTransport
open ContinuumNormalReduction.TransportSymbol LeadingWave AmbientResponse

private theorem controls_of_bound {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : PrimitiveNormChart E) {f : E → H} {m : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f D.region) (hm : cNorm D.carrier (m + 1) f ≤ M) :
    D.Controls m M (M + 1) 1 f := by
  refine ⟨hf, (cNorm_mono_order (by omega : 1 ≤ m + 1)).trans hm, ?_⟩
  have h := (cNorm_mono_order (Nat.le_succ m)).trans hm
  simpa only [mul_one, add_comm] using add_le_add_left h 1

private theorem cNorm_le_reference_add_one {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : Set E} (hK : IsCompact K) {f f₀ : E → H} (m : ℕ)
    (hf : ∀ p ∈ K, ContDiffAt ℝ ∞ f p) (hf₀ : ∀ p ∈ K, ContDiffAt ℝ ∞ f₀ p)
    (hd : cNorm K m (f - f₀) < 1) : cNorm K m f ≤ cNorm K m f₀ + 1 := by
  have h := cNorm_add_le_of_contDiffAt (r := m) hK
    (fun p hp ↦ ((hf p hp).sub (hf₀ p hp)).of_le (by simp))
    (fun p hp ↦ (hf₀ p hp).of_le (by simp))
  simp only [Pi.add_def, sub_add_cancel] at h
  change cNorm K m f ≤ cNorm K m (f - f₀) + cNorm K m f₀ at h
  linarith

/-- Absolute finite primitive bounds for `normalizedCarrierData`, including
its zero slice and one additional reference derivative. The normal is derived
from the actual seed null scalar and canonical completion; the reduced field
is derived from the same stress and phase covector. Fixed masks use their
actual finite norms. No coefficient or amplitude continuity is a premise.
Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`.
The seed smoothness premise is produced by `exists_retained_seed_matched_unit_transport`.
-/
theorem exists_normalizedCarrierData_coefficient_controls
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
    (hh : ContDiffOn ℝ ∞ high D.high.region) (m : ℕ) :
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ) measurement
    ∃ M > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ 1 ∧
      D.Controls (m + 1) M (M + 1) 1 (a 0) ∧
      ∀ σ ∈ Icc (0 : ℝ) s, D.Controls m M (M + 1) 1 (a σ) := by
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
  have hmaps (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
      MapsTo (fun x ↦ σ • x) (ball (0 : Euclidean n) R) (ball 0 R) :=
    fun _ hx ↦ (convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem (mem_ball_self hR) hx hσ
  have hsmooth (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
      ContDiffOn ℝ ∞ (a σ).normal D.field.region ∧
      ContDiffOn ℝ ∞ (a σ).reduced D.field.region := by
    have harg : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ (σ • p.1, p.2))
        D.field.region := (contDiffOn_fst.const_smul σ).prodMk contDiffOn_snd
    have hmap : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (σ • p.1, p.2))
        D.field.region (ball 0 R ×ˢ V) := fun p hp ↦ ⟨hmaps σ hσ (hD hp).1, (hD hp).2⟩
    have heq (p) (hp : p ∈ D.field.region) :=
      coefficientsOfCarrier_normalizedCarrierData_eq_source T Q₀ F row col Φ Y initial
        hr hcell angular high measurement hP hseed
        (ball_subset_ball hRT (hmaps σ hσ (hD hp).1)) (hVP' p.2 (hD hp).2)
    exact ⟨(hν.comp harg hmap).congr (fun p hp ↦ (heq p hp).1),
      (hq.comp harg hmap).congr (fun p hp ↦ (heq p hp).2)⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hbase := hsmooth 0 hzero
  obtain ⟨hnlim, hqlim⟩ := tendsto_normalizedCarrierData_coefficients_sub_cNorm
    T Q₀ F row col Φ Y initial hr hcell angular high measurement hP hseed hF hi hrank
    hR hRT hRU hV hVP hb D (fun p hp ↦ (hD (D.field.ball_subset hp)).2) (m + 1)
  obtain ⟨s₀, hs₀, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((hnlim.eventually (gt_mem_nhds zero_lt_one)).and (hqlim.eventually (gt_mem_nhds zero_lt_one)))
  let M := cNorm D.measurement.carrier (m + 2) measurement +
    cNorm D.angular.carrier (m + 2) (fun p ↦ angular p.1 p.2) +
    cNorm D.high.carrier (m + 2) high + cNorm D.field.carrier (m + 2) (a 0).normal +
    cNorm D.field.carrier (m + 2) (a 0).reduced + 1
  have hbounds : cNorm D.measurement.carrier (m + 2) measurement ≤ M ∧
      cNorm D.angular.carrier (m + 2) (fun p ↦ angular p.1 p.2) ≤ M ∧
      cNorm D.high.carrier (m + 2) high ≤ M ∧
      cNorm D.field.carrier (m + 2) (a 0).normal + 1 ≤ M ∧
      cNorm D.field.carrier (m + 2) (a 0).reduced + 1 ≤ M := by
    have h₁ := cNorm_nonneg D.measurement.carrier (m + 2) measurement
    have h₂ := cNorm_nonneg D.angular.carrier (m + 2) (fun p ↦ angular p.1 p.2)
    have h₃ := cNorm_nonneg D.high.carrier (m + 2) high
    have h₄ := cNorm_nonneg D.field.carrier (m + 2) (a 0).normal
    have h₅ := cNorm_nonneg D.field.carrier (m + 2) (a 0).reduced
    dsimp only [M]; constructor <;> (try constructor) <;> (try constructor) <;> (try constructor) <;> linarith only [h₁, h₂, h₃, h₄, h₅]
  have hM : 0 < M :=
    (add_pos_of_nonneg_of_pos (cNorm_nonneg ..) zero_lt_one).trans_le hbounds.2.2.2.1
  refine ⟨M, hM, min (s₀ / 2) 1, lt_min (half_pos hs₀) zero_lt_one, min_le_right _ _, ?_, ?_⟩
  · exact ⟨controls_of_bound D.measurement hm hbounds.1,
      controls_of_bound D.angular ha hbounds.2.1,
      controls_of_bound D.high hh hbounds.2.2.1,
      controls_of_bound D.field hbase.1 (by linarith only [hbounds.2.2.2.1]),
      controls_of_bound D.field hbase.2 (by linarith only [hbounds.2.2.2.2])⟩
  · intro σ hσ
    have hσ1 : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
    have hd := hsmall (show σ ∈ ball (0 : ℝ) s₀ from by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hσ.1]
      exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self hs₀))
    have hsm := hsmooth σ hσ1
    have hn := cNorm_le_reference_add_one (isCompact_closedBall _ _) (m + 1)
      (fun p hp ↦ hsm.1.contDiffAt (D.field.isOpen_region.mem_nhds (D.field.ball_subset hp)))
      (fun p hp ↦ hbase.1.contDiffAt (D.field.isOpen_region.mem_nhds (D.field.ball_subset hp))) hd.1
    have hq' := cNorm_le_reference_add_one (isCompact_closedBall _ _) (m + 1)
      (fun p hp ↦ hsm.2.contDiffAt (D.field.isOpen_region.mem_nhds (D.field.ball_subset hp)))
      (fun p hp ↦ hbase.2.contDiffAt (D.field.isOpen_region.mem_nhds (D.field.ball_subset hp))) hd.2
    have hn₀ := cNorm_mono_order (f := (a 0).normal) (s := D.field.carrier) (by omega : m + 1 ≤ m + 2)
    have hq₀ := cNorm_mono_order (f := (a 0).reduced) (s := D.field.carrier) (by omega : m + 1 ≤ m + 2)
    exact ⟨controls_of_bound D.measurement hm ((cNorm_mono_order (by omega : m + 1 ≤ m + 2)).trans hbounds.1),
      controls_of_bound D.angular ha ((cNorm_mono_order (by omega : m + 1 ≤ m + 2)).trans hbounds.2.1),
      controls_of_bound D.high hh ((cNorm_mono_order (by omega : m + 1 ≤ m + 2)).trans hbounds.2.2.1),
      controls_of_bound D.field hsm.1 (hn.trans ((add_le_add hn₀ (le_refl (1 : ℝ))).trans hbounds.2.2.2.1)),
      controls_of_bound D.field hsm.2 (hq'.trans ((add_le_add hq₀ (le_refl (1 : ℝ))).trans hbounds.2.2.2.2))⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
