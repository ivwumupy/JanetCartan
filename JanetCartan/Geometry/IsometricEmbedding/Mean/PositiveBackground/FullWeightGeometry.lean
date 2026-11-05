module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationPeriodization
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Supported

/-!
# Periodic geometry on the entire original external-weight support

The physical cancellation and preparation consumers require the same footpoint
and principal matrix on the full weight support, including its collar beyond
the detector. A cutoff supported in the retained product cell extends these
actual fields. It is chosen before the immersion, chart and positive scalar;
the original external weight and all row masks remain fixed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow CanonicalCarrier CurrentMean AmplitudeBound
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedChartMean

/-- A supported cutoff extends the actual local fields, without assuming
global smoothness (`app:ch_background:eq:bg-current-identity`). -/
private theorem contDiff_supported_smul
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set X} (hO : IsOpen O) {κ : X → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ O) {f : X → E} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun p ↦ κ p • f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport κ
  · exact hκ.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds (hs hp)))
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport κ).isOpen_compl.mem_nhds hp] with q hq
    simp only [image_eq_zero_of_notMem_tsupport hq, zero_smul]

/-- Joint periodization of the retained footpoint, with a physical support
gap uniform in the carrier label (`app:ch_background:prop:bg-adjoint`). -/
private theorem fullWeight_vectorPeriodization_regular {n m : ℕ}
    (f : Euclidean n × CarrierParameter → Euclidean m)
    {b : ℝ} (hb : b < 1 / 2)
    (hs : ∀ x z, f (x, z) ≠ 0 → ∀ i, |x i| ≤ b)
    (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : Torus n × CarrierParameter ↦
      f (centeredTorusRepresentative p.1, p.2)) ∧
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      f (centeredTorusRepresentative (torusQuotient p.1), p.2)) := by
  let g := fun p : Torus n × CarrierParameter ↦ f (centeredTorusRepresentative p.1, p.2)
  have heq (x : Euclidean n) (z : CarrierParameter) (hx : ∀ i, |x i| < 1 - b) :
      g (torusQuotient x, z) = f (x, z) := by
    ext j
    apply Complex.ofReal_injective
    apply periodicLift_amplitudePeriodization_eq_of_lt hb (f := fun y ↦ (f (y, z) j : ℂ)) _ hx
    intro y hy
    apply hs y z
    intro h
    exact hy (by simp [h])
  have hlocal {x : Euclidean n} (hx : x ∈ fundamentalCell n) (z : CarrierParameter) :
      (fun p : Euclidean n × CarrierParameter ↦ g (torusQuotient p.1, p.2)) =ᶠ[𝓝 (x, z)] f := by
    have hmem : ∀ᶠ p : Euclidean n × CarrierParameter in 𝓝 (x, z),
        ∀ i, |p.1 i| < 1 - b := by
      apply eventually_all.mpr
      intro i
      apply (isOpen_lt (((EuclideanSpace.proj i).continuous.comp continuous_fst).abs)
        continuous_const).mem_nhds
      exact (abs_le.mpr (hx i)).trans_lt (by linarith)
    exact hmem.mono fun p hp ↦ heq p.1 p.2 hp
  have hd : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      g (torusQuotient p.1, p.2)) := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨x, z⟩
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hl := hf.contDiffAt.congr_of_eventuallyEq (hlocal hy z)
    have he : ((y + integerTranslation k) - integerTranslation k, z) = (y, z) := by simp
    have hl' := he.symm ▸ hl
    have hcomp := hl'.comp (y + integerTranslation k, z)
      ((contDiffAt_fst.sub (contDiffAt_const (c := integerTranslation k))).prodMk contDiffAt_snd)
    convert hcomp using 1
    funext p
    exact (periodicLift_periodic (fun x ↦ g (x, p.2)) k).sub_eq p.1 |>.symm
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨(hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

/-- Construct the full-weight footpoint and principal-matrix extensions for
the SAME retained chart. The auxiliary cutoff is chosen before the immersion,
chart and initial scalar. It equals one on the entire closed output chart
times the original weight support, so the returned `hfoot` and `hbase` are
literal identities. Local normal/covector smoothness is derived from the
chart's characteristic formula and canonical normal completion.

Consumers are `physicalDensityMean_uncorrected_core_cancellation_of_supplied_masks`
and `PreparedHistory.PositiveTransport`; no smooth extension or inverse estimate
is an input (`app:ch_background:eq:bg-current-identity`,
`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem exists_retained_full_weight_transport_extensions
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc M τ : ℝ} {row col : Fin n}
    {cP CP : ℝ} (hP : P.IsValid cP CP) (hτ : 0 < τ)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2) (hfive : 5 * r < 1 / 2)
    (hphysical : 5 * r ≤ T.physicalRadius)
    (χ : CarrierParameter → ℝ) (hχc : HasCompactSupport χ)
    {V : Set CarrierParameter} (hV : IsOpen V) (hχV : tsupport χ ⊆ V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ κ : Euclidean n × CarrierParameter → ℝ,
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ ball (0 : Euclidean n) (5 * r) ×ˢ V ∧
      closedBall (0 : Euclidean n) (4 * r) ×ˢ tsupport χ ⊆ interior {p | κ p = 1} ∧
      ∀ (F : Euclidean n → Euclidean N),
        ContDiffOn ℝ ∞ F (ball 0 (5 * r)) →
        IsImmersionOn F (ball 0 (5 * r)) → HasFullNormalRankOn F (ball 0 (5 * r)) →
        ∀ c : Chart T Ω K p₀ Rc M τ row col F,
          MapsTo (densityCoordinates T) (ball (0 : Euclidean n) (5 * r) ×ˢ V) c.D →
        ∀ σ : ℝ, 0 < σ →
        ∀ (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ),
        let d := data T c.Q F row col c.forward c.inverse (fun _ ↦ σ) hr hcell angular high
        let Y := fun p : Torus n × CarrierParameter ↦
          κ (centeredTorusRepresentative p.1, p.2) •
            transportPosition T c.Q (centeredTorusRepresentative p.1, p.2)
        let A := preparationMatrixPeriodization (fun p ↦ κ p •
          (LeadingWave.principalMatrix (c.normal (fun _ ↦ σ) p) (covector c p)).map Complex.ofReal)
        Continuous Y ∧ Continuous A ∧
        ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ Y (torusQuotient p.1, p.2)) ∧
        ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ A (torusQuotient p.1, p.2)) ∧
        (∀ x ∈ d.outputChart, ∀ z, χ z ≠ 0 →
          Y (x, z) = d.transportedPosition (d.chartPoint x) z) ∧
        (∀ x ∈ d.outputChart, ∀ z, χ z ≠ 0 → A (x, z) = densityTransportMatrix d 0 x z) ∧
        ContDiffOn ℝ ∞ (fun p ↦ d.transportedPosition p.1 p.2) (ball 0 (5 * r) ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun p ↦ d.normalField p.1 p.2) (ball 0 (5 * r) ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun p ↦ d.covector p.1 p.2) (ball 0 (5 * r) ×ˢ V) := by
  obtain ⟨κ, hκ, _, hκc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
    ((isCompact_closedBall (0 : Euclidean n) (4 * r)).prod hχc) (isOpen_ball.prod hV)
    (prod_mono (closedBall_subset_ball (by linarith : 4 * r < 5 * r)) hχV)
  refine ⟨κ, hκ, hκc, hs, hp, ?_⟩
  intro F hF himm hrank c hflow σ hσ angular high d Y A
  have hYlocal : ContDiffOn ℝ ∞ (transportPosition T c.Q) (ball 0 (5 * r) ×ˢ V) :=
    (ContinuumAdjoint.Canonical.PhaseExtension.transportPosition_contDiffOn_extensionDomain
      T hP c.Q).mono (prod_mono (ball_subset_ball hphysical) hVP)
  obtain ⟨hν, hξ⟩ := retained_chart_normal_contDiffOn c hP hτ hpatch isOpen_ball
    hF himm hrank hflow hσ
  have hmatrix : ContDiffOn ℝ ∞ (fun p ↦
      (LeadingWave.principalMatrix (c.normal (fun _ ↦ σ) p) (covector c p)).map Complex.ofReal)
      (ball 0 (5 * r) ×ˢ V) := by
    let L : (Fin N → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ := LinearMap.id
    let C : (Fin N → Fin n → ℂ) →L[ℝ] Matrix (Fin N) (Fin n) ℂ :=
      ⟨L, L.continuous_of_finiteDimensional⟩
    apply C.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro a
    apply contDiffOn_pi.mpr
    intro i
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((((contDiffOn_piLp 2).mp hν a).mul ((contDiffOn_piLp 2).mp hξ i)).neg)
  have hbox {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : Euclidean n × CarrierParameter → E) (x : Euclidean n) (z : CarrierParameter)
      (hx : κ (x, z) • f (x, z) ≠ 0) (i : Fin n) : |x i| ≤ 5 * r := by
    have hκx : κ (x, z) ≠ 0 := fun h ↦ hx (by rw [h, zero_smul])
    exact (PiLp.norm_apply_le x i).trans (mem_ball_zero_iff.mp (hs (subset_tsupport κ hκx)).1).le
  have hY' := fullWeight_vectorPeriodization_regular
    (fun p ↦ κ p • transportPosition T c.Q p) hfive (hbox (transportPosition T c.Q))
    (contDiff_supported_smul (isOpen_ball.prod hV) hκ hs hYlocal)
  have hA' := preparationMatrixPeriodization_regular _ hfive
    (hbox (fun p ↦
      (LeadingWave.principalMatrix (c.normal (fun _ ↦ σ) p) (covector c p)).map Complex.ofReal))
    (contDiff_supported_smul (isOpen_ball.prod hV) hκ hs hmatrix)
  refine ⟨hY'.1, hA'.1, hY'.2, hA'.2, ?_, ?_, hYlocal, hν, hξ⟩
  · intro x hx z hz
    have hκone : κ (centeredTorusRepresentative x, z) = 1 :=
      (show (centeredTorusRepresentative x, z) ∈ {p | κ p = 1} from
        interior_subset (hp ⟨hx, subset_tsupport χ hz⟩))
    change κ _ • transportPosition T c.Q _ = transportPosition T c.Q _
    rw [hκone, one_smul]
    rfl
  · intro x hx z hz
    have hκone : κ (centeredTorusRepresentative x, z) = 1 :=
      (show (centeredTorusRepresentative x, z) ∈ {p | κ p = 1} from
        interior_subset (hp ⟨hx, subset_tsupport χ hz⟩))
    simp only [A, preparationMatrixPeriodization, hκone, one_smul,
      densityTransportMatrix, Pi.zero_apply, add_zero, Real.sqrt_one]
    rfl

end JanetCartan.PositiveBackground
