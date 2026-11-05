module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.FullWeightGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.CanonicalMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMeanCancellation

/-!
# Physical cancellation on the same retained chart family

Apply the synthesis and covector-raising cancellation to the actual canonical
data of the supplied retained charts. Full-weight periodic geometry,
measurement regularity and kernel measurability are derived here. The same
uncorrected inverse and its smooth density representative are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow CanonicalCarrier CanonicalConic CurrentMean UncutDensity AmplitudeBound CarrierSobolev
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedChartMean
open ProjectedStressFrame

/-- The uncorrected principal matrix realizes the same measured stress
(`app:ch_background:eq:bg-affine-mean`). -/
private theorem measuredStress_eq_fullWeight_matrix {n N : ℕ}
    (d : CarrierData n N) (A : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    {x : Torus n} {z : CarrierParameter}
    (hA : A (x, z) = densityTransportMatrix d 0 x z) :
    preparationStressMeasurement d x (hermitianTensor (A (x, z))) = measuredStress d x z := by
  rw [hA]
  simpa only [Pi.zero_apply, add_zero, one_smul] using
    measurement_densityTransportMatrix d 0 x z (by simp)

/-- Measurability of the literal kernel follows from the full-weight
extensions and the original masks; no operator realization is assumed
(`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-density-four`). -/
private theorem measurable_carrierKernel_of_fullWeight_extensions {n N : ℕ}
    (d : CarrierData n N) (χ : CarrierParameter → ℝ)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (A : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hY : Continuous Y) (hA : Continuous A)
    (hfoot : ∀ x ∈ d.outputChart, ∀ z, χ z ≠ 0 →
      Y (x, z) = d.transportedPosition (d.chartPoint x) z)
    (hbase : ∀ x ∈ d.outputChart, ∀ z, χ z ≠ 0 → A (x, z) = densityTransportMatrix d 0 x z)
    (hangular : Measurable (fun p : CarrierVariable n ↦ d.angularCutoff p.1 p.2))
    (hhigh : Measurable d.highCutoff)
    (hmask : ∀ z η, d.angularCutoff z η ≠ 0 → χ z ≠ 0) (x : Torus n) :
    Measurable (carrierKernel d x) := by
  by_cases hx : x ∈ d.outputChart
  · let S := fun z ↦ preparationStressMeasurement d x (hermitianTensor (A (x, z)))
    have hAx : Continuous (fun z ↦ A (x, z)) := hA.comp (continuous_const.prodMk continuous_id)
    have hherm := (hermitianContinuousBilinear.continuous.comp hAx).clm_apply hAx
    simp only [Function.comp_apply, hermitianContinuousBilinear_apply,
      mixedHermitianTensor_self] at hherm
    have hS : Continuous S := (preparationStressMeasurement d x).continuous_of_finiteDimensional.comp hherm
    have hYx : Continuous (fun u : CarrierVariable n ↦ Y (x, u.1)) :=
      hY.comp (continuous_const.prodMk continuous_fst)
    have hphase : Continuous (fun u : CarrierVariable n ↦
        Complex.exp (Complex.I * (inner ℝ (Y (x, u.1)) u.2 : ℂ))) := by
      fun_prop
    have hnorm : Measurable (fun u : CarrierVariable n ↦ ‖u.2‖) := measurable_snd.norm
    have hangular' := hangular.comp (measurable_fst.prodMk (hnorm.inv.smul measurable_snd))
    have hscalar := (hangular'.mul (hhigh.comp hnorm)).mul
      (Real.continuous_sqrt.measurable.comp hnorm)
    have hkernel := hphase.measurable.smul
      (euclideanComplexInclusion.continuous.measurable.comp
        (hscalar.smul (hS.measurable.comp measurable_fst)))
    have heq : carrierKernel d x = fun u : CarrierVariable n ↦
        Complex.exp (Complex.I * (inner ℝ (Y (x, u.1)) u.2 : ℂ)) •
          euclideanComplexInclusion
            ((d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) * d.highCutoff ‖u.2‖ * Real.sqrt ‖u.2‖) • S u.1) := by
      funext u
      by_cases hρ : d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) = 0
      · simp [carrierKernel, carrierAmplitude, hx, hρ]
      · have hχ := hmask u.1 (‖u.2‖⁻¹ • u.2) hρ
        have hy := hfoot x hx u.1 hχ
        have hm : S u.1 = measuredStress d x u.1 :=
          measuredStress_eq_fullWeight_matrix d A (hbase x hx u.1 hχ)
        have ha : carrierAmplitude d x u =
            (d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) * d.highCutoff ‖u.2‖ * Real.sqrt ‖u.2‖) •
              measuredStress d x u.1 := by
          unfold carrierAmplitude measuredStress
          rw [smul_smul]
          congr 1
          ring
        simp only [carrierKernel, indicator_of_mem hx, ContinuumRow.carrierPhase, ha, ← hy, ← hm]
    rw [heq]
    exact hkernel
  · have heq : carrierKernel d x = fun _ ↦ 0 := funext fun u ↦ carrierKernel_eq_zero_outside d hx u
    rw [heq]
    exact measurable_const

/-- The original uncorrected inverse cancels the literal physical mean of
the SAME retained chart data. Full-weight extension, measurement smoothness,
kernel measurability and core chart identities are constructed from the
original chart geometry. The source sign `-1/2`, uncut synthesis factor `4`
and tangent-strain factor `2` are inherited from synthesis and covector
raising, with the supplied exterior kept distinct from the source cutoff.

The bounded carrier action, uniform gap and raw Sobolev membership remain the
precise same-row analytic inputs supplied by the normalized adjoint, normal and
inverse producers. Consumers are `PreparedHistory`, `CanonicalChange` and
`Current` (`app:ch_background:prop:bg-positive`,
`app:ch_background:eq:bg-current-identity`). -/
theorem retained_physicalDensityMean_uncorrected_core_cancellation
    {n N : ℕ} {ι : Type} [Fintype ι]
    {P : ι → Patch n} {U₀ : Set (Euclidean n)} {hU₀ : IsOpen U₀}
    (T : (a : ι) → PatchQuantitativeFamily (P a) U₀ hU₀)
    {Ω K : ι → Set (Euclidean n × Euclidean 3)}
    {p₀ : ι → Euclidean (n - 1) × Euclidean 3} {Rc M τ : ι → ℝ} {row col : ι → Fin n}
    {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP) (hτ : ∀ a, 0 < τ a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2) (hfive : 5 * r < 1 / 2)
    (hphysical : ∀ a, 5 * r ≤ (T a).physicalRadius)
    (hball : closedBall (0 : Euclidean n) (4 * r) ⊆ U₀)
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hVP : ∀ a, V a ⊆ parameter ⁻¹' parameterInterior (3 * (P a).radius / 2))
    (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F (ball 0 (5 * r)))
    (himm : IsImmersionOn F (ball 0 (5 * r))) (hrank : HasFullNormalRankOn F (ball 0 (5 * r)))
    (chart : (a : ι) → Chart (T a) (Ω a) (K a) (p₀ a) (Rc a) (M a) (τ a) (row a) (col a) F)
    (hflow : ∀ a, MapsTo (densityCoordinates (T a)) (ball (0 : Euclidean n) (5 * r) ×ˢ V a)
      (chart a).D)
    {σ : ℝ} (hσ : 0 < σ)
    (zRoot : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    (am width : ι → ℝ) (ham : ∀ a, 0 < am a) (hwidth : ∀ a, 0 < width a)
    (hplateau : ∀ a, carrierSupport (zRoot a) (r := am a) ⊆ interior {z | χ a z = 1})
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hcoeff : ∀ j, IsSmoothPeriodic (coeff j))
    (hcoeff_core : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      coeff j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (B : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ w, gap * ‖w‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel coeff (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)) B ψ).adjoint w‖ ^ 2)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r))) :
    let d := fun a ↦ data (T a) (chart a).Q F (row a) (col a)
      (chart a).forward (chart a).inverse (fun _ ↦ σ) hr hcell
      (angularMask (zRoot a) (θ₀ a) (ham a) (hwidth a)) FixedCutoffs.highFrequency
    let H := physicalDensityMean d χ 0
    let hF₄ : ContDiffOn ℝ ∞ F (ball 0 (4 * r)) := hF.mono (ball_subset_ball (by linarith))
    let hi₄ : IsImmersionOn F (ball 0 (4 * r)) :=
      fun x hx ↦ himm x (ball_subset_ball (by linarith : 4 * r ≤ 5 * r) hx)
    let hr₄ : HasFullNormalRankOn F (ball 0 (4 * r)) :=
      fun x hx ↦ hrank x (ball_subset_ball (by linarith : 4 * r ≤ 5 * r) hx)
    ∃ hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r)),
    let image := imageChannel coeff (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    let θ := FixedCutoffs.periodic hr hcell 0
    let residual := physicalBackgroundResidualToL2 hr hcell F X₀ H hF₄ hX₀ hH hi₄ hr₄
    let raw := uncorrectedRawCorrection image B ψ θ residual
    (∀ a (u : carrierInitialTestSpace n), B a (carrierInitialTestToLp u) =ᵐ[volume]
      carrierTestIntegral (d a) u.val) →
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
    ∀ v : ι → CarrierVariable n → ℝ, (∀ a, ContDiff ℝ ∞ (v a)) →
      (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image B ψ θ residual a) →
      ContDiffOn ℝ ∞ (uncorrectedBaseVariation coeff (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2) ψ θ B residual F X₀) (ball 0 (4 * r)) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) r,
        torusQuotient x ∈ interior {z | ψ z = 1} → ∀ i,
        tensorPairing (projectedStress F x i)
          (linearizedMetric F (uncorrectedBaseVariation coeff (FixedCutoffs.periodic hr hcell 1)
            (FixedCutoffs.periodic hr hcell 2) ψ θ B residual F X₀) x +
              physicalDensityMean d χ v x) = 0 := by
  classical
  intro d H hF₄ hi₄ hr₄
  choose κ hκ hκc hκsupport hκplateau hext using fun a ↦
    exists_retained_full_weight_transport_extensions (N := N) (T a) (hP a) (hτ a) (hpatch a)
      hr hcell hfive (hphysical a) (χ a) (hχc a) (hV a) (hχV a) (hVP a)
  let Y := fun a (p : Torus n × CarrierParameter) ↦
    κ a (centeredTorusRepresentative p.1, p.2) •
      transportPosition (T a) (chart a).Q (centeredTorusRepresentative p.1, p.2)
  let A := fun a ↦ preparationMatrixPeriodization (fun p ↦ κ a p •
    (LeadingWave.principalMatrix ((chart a).normal (fun _ ↦ σ) p) (covector (chart a) p)).map Complex.ofReal)
  have hgeometry a := hext a F hF himm hrank (chart a) (hflow a) σ hσ
    (angularMask (zRoot a) (θ₀ a) (ham a) (hwidth a)) FixedCutoffs.highFrequency
  have hYc a : Continuous (Y a) := (hgeometry a).1
  have hAc a : Continuous (A a) := (hgeometry a).2.1
  have hY a : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y a (torusQuotient p.1, p.2)) := (hgeometry a).2.2.1
  have hA a : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      A a (torusQuotient p.1, p.2)) := (hgeometry a).2.2.2.1
  have hfoot a := (hgeometry a).2.2.2.2.1
  have hbase a := (hgeometry a).2.2.2.2.2.1
  have hfields a := (hgeometry a).2.2.2.2.2.2
  have h45 : ball (0 : Euclidean n) (4 * r) ⊆ ball 0 (5 * r) := ball_subset_ball (by linarith)
  have hYlocal a := (hfields a).1.mono (prod_mono h45 Subset.rfl)
  have hνlocal a := (hfields a).2.1.mono (prod_mono h45 Subset.rfl)
  have hξlocal a := (hfields a).2.2.mono (prod_mono h45 Subset.rfl)
  let hH := contDiffOn_physicalDensityMean_zero d χ hχ hχc isOpen_ball V hV hχV hνlocal hξlocal
  refine ⟨hH, ?_⟩
  intro image θ residual raw hB hraw v hv heq
  have hmask (a : ι) (z : CarrierParameter) (η : Euclidean (n - 1))
      (hz : (d a).angularCutoff z η ≠ 0) : χ a z ≠ 0 := by
    obtain ⟨hs, hv, _⟩ := angularMask_nonzero (zRoot a) (θ₀ a) (ham a) (hwidth a) hz
    have hχone : χ a z = 1 := (show z ∈ {q | χ a q = 1} from
      interior_subset (hplateau a ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩))
    rw [hχone]
    exact one_ne_zero
  have hk (a : ι) (x : Torus n) : AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n) :=
    (measurable_carrierKernel_of_fullWeight_extensions (d a) (χ a) (Y a) (A a) (hYc a) (hAc a)
      (hfoot a) (hbase a) (angularMask_smooth (zRoot a) (θ₀ a) (ham a) (hwidth a)).continuous.measurable
      FixedCutoffs.highFrequency_smooth.continuous.measurable (hmask a) x).aestronglyMeasurable
  have hst (a : ι) (x : Torus n) : ContinuousOn (measuredStress (d a) x)
      (carrierSupport (zRoot a) (r := am a)) := by
    by_cases hx : x ∈ (d a).outputChart
    · have hAx : Continuous (fun z : CarrierParameter ↦ A a (x, z)) :=
        (hAc a).comp (continuous_const.prodMk continuous_id)
      have hh := (hermitianContinuousBilinear.continuous.comp hAx).clm_apply hAx
      simp only [Function.comp_apply, hermitianContinuousBilinear_apply, mixedHermitianTensor_self] at hh
      apply ((preparationStressMeasurement (d a) x).continuous_of_finiteDimensional.comp hh).continuousOn.congr
      intro z hz
      have hχone : χ a z = 1 := (show z ∈ {q | χ a q = 1} from interior_subset (hplateau a hz))
      exact (measuredStress_eq_fullWeight_matrix (d a) (A a)
        (hbase a x hx z (by rw [hχone]; exact one_ne_zero))).symm
    · have hm : (d a).measurementCutoff x = 0 := by
        by_contra hh
        exact hx (CommonMeasurement.fixed_measurement_mem_chart hr hcell hh)
      have hz : measuredStress (d a) x = fun _ ↦ 0 := by
        funext z
        simp only [measuredStress, hm, zero_mul, zero_smul]
      rw [hz]
      exact continuousOn_const
  have hC a : IsSmoothPeriodic (preparationMeasurement (d a)) :=
    isSmoothPeriodic_preparationMeasurement_canonical (T a) (chart a).Q F (row a) (col a)
      (chart a).forward (chart a).inverse (fun _ ↦ σ) hr hcell hball
      (angularMask (zRoot a) (θ₀ a) (ham a) (hwidth a)) FixedCutoffs.highFrequency
  have hpoint (x : Euclidean n) (hx : x ∈ closedBall 0 r) :
      centeredTorusRepresentative (torusQuotient x) = x :=
    PeriodicLocalL2.centeredTorusRepresentative_quotient
      (FixedCutoffs.closedBall_four_subset_cell hcell
        (closedBall_subset_closedBall (by linarith : r ≤ 4 * r) hx))
  apply physicalDensityMean_uncorrected_core_cancellation_of_supplied_masks
    d zRoot θ₀ am width ham hwidth (fun _ ↦ rfl) (fun _ ↦ rfl) hst χ hχ hχc hplateau
    hC Y A hYc hAc hY hA hfoot hbase coeff hcoeff hr hcell B hB hk ψ hgap_pos hgap
    F X₀ hF₄ hX₀ hi₄ hr₄ hcoeff_core V hV hχV hYlocal hνlocal hξlocal
    ?_ ?_ ?_ ?_ hraw v hv heq
  · intro x hx a
    change centeredTorusRepresentative (torusQuotient x) ∈ closedBall 0 (4 * r)
    rw [hpoint x hx]
    exact closedBall_subset_closedBall (by linarith) hx
  · intro x hx a
    exact hpoint x hx
  · intro x hx a
    change FixedCutoffs.physical hr 1 (centeredTorusRepresentative (torusQuotient x)) = 1
    rw [hpoint x hx]
    exact (show x ∈ {p | FixedCutoffs.physical hr 1 p = 1} from
      interior_subset (FixedCutoffs.physical_plateau hr 1
        (closedBall_subset_closedBall (by norm_num; linarith) hx)))
  · intro x _ a i
    exact congrFun (congrFun (chart a).frame_eq x) i

end JanetCartan.PositiveBackground
