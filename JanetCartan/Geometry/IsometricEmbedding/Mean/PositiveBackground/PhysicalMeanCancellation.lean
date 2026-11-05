module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalCancellation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights.Cutoffs
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Density

/-!
# Physical cancellation for the same smooth uncorrected density

The density chosen for the inverse-derived smallness estimate is retained.
Uniqueness of continuous representatives of that SAME raw synthesis connects
it to the geometric cancellation theorem. The uncorrected mean is the literal
physical carrier integral, and its smoothness follows from the original fields.
The supplied exterior cutoff remains independent of the measurement radius;
cancellation holds on the intersection with its open plateau. The old
fixed-radius theorem is recovered without any new hypothesis.

This is the physical assembly step in `app:ch_background:eq:bg-current-identity`.
It retains the primitive same-row gap and raw regularity obligations; it neither
constructs those estimates nor fixes the later corrected-positive inverse.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PositiveBackground
open ContinuumRow CarrierSobolev UncutDensity CurrentMean CanonicalConic
open ProjectedStressFrame
open RetainedAssembly.ExternalWeights
variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The literal physical mean cancels for the actual supplied canonical
angular masks, with their own positive widths and unchanged carrier supports.
This accepts the masks constructed by the normalized raw-adjoint producer;
no equality with an independently selected conic width is needed. The full
external-weight plateau, same uncorrected density representative and supplied
exterior are retained. Synthesis and covector raising give the source sign
`-1/2`, density factor `4` and tangent-strain factor `2`
(`app:ch_background:eq:bg-current-raising`, `app:ch_background:eq:bg-current-identity`).

Consumers: the normalized source density from `CorrectedSourceInverse` and
`Current`. The geometric realization, same-row gap and raw regularity remain
the existing producer inputs. The original conic-selection statement below is
its specialization using the exact detector-projection identity. -/
theorem physicalDensityMean_uncorrected_core_cancellation_of_supplied_masks
    (d : ι → CarrierData n N)
    (zRoot : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    (am width : ι → ℝ) (ham : ∀ a, 0 < am a) (hwidth : ∀ a, 0 < width a)
    (hangular : ∀ a, (d a).angularCutoff = angularMask (zRoot a)
      (θ₀ a) (ham a) (hwidth a))
    (hhigh : ∀ a, (d a).highCutoff = FixedCutoffs.highFrequency)
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x)
      (carrierSupport (zRoot a) (r := am a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (hplateau : ∀ a, carrierSupport (zRoot a) (r := am a) ⊆
      interior {z | χ a z = 1})
    (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (Y : ι → Torus n × CarrierParameter → Euclidean (n - 1))
    (T : ι → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : ∀ a, Continuous (Y a)) (hTc : ∀ a, Continuous (T a))
    (hY : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y a (torusQuotient p.1, p.2)))
    (hT : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T a (torusQuotient p.1, p.2)))
    (hfoot : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      Y a (x, z) = (d a).transportedPosition ((d a).chartPoint x) z)
    (hbase : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      T a (x, z) = densityTransportMatrix (d a) 0 x z)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a (u : carrierInitialTestSpace n),
      U a (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d a) u.val)
    (hk : ∀ a x, AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n))
    (ψ : C(Torus n, ℝ))
    {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ w, gap * ‖w‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)) U ψ).adjoint w‖ ^ 2)
    (G : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n)
    (hG : ContDiffOn ℝ ∞ G (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (himm : IsImmersionOn G (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn G (ball 0 (4 * r)))
    (hcoeff : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j)
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hYphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).transportedPosition p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hνphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).normalField p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hξphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).covector p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hchart : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      torusQuotient x ∈ (d a).outputChart)
    (hpoint : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      (d a).chartPoint (torusQuotient x) = x)
    (hmeas : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      (d a).measurementCutoff (torusQuotient x) = 1)
    (hstress : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a i,
      (d a).stressFrame x i = projectedStress G x i) :
    let H := physicalDensityMean d χ 0
    let hH := contDiffOn_physicalDensityMean_zero d χ hχ hχc isOpen_ball
      V hV hχV hνphysical hξphysical
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
      (FixedCutoffs.periodic hr hcell 2)
    let θ := FixedCutoffs.periodic hr hcell 0
    let residual := physicalBackgroundResidualToL2 hr hcell G X₀ H hG hX₀ hH himm hrank
    let raw := uncorrectedRawCorrection image U ψ θ residual
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∀ v : ι → CarrierVariable n → ℝ, (∀ a, ContDiff ℝ ∞ (v a)) →
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U ψ θ residual a) →
        ContDiffOn ℝ ∞ (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
          (FixedCutoffs.periodic hr hcell 2) ψ θ U residual G X₀) (ball 0 (4 * r)) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) r,
          torusQuotient x ∈ interior {z | ψ z = 1} → ∀ i,
          tensorPairing (projectedStress G x i)
            (linearizedMetric G (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) ψ θ U residual G X₀) x +
                physicalDensityMean d χ v x) = 0 := by
  intro H hH image θ residual raw hreg v hv he
  have hρsmooth (a : ι) : ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)) := by
    rw [hangular a]
    exact ContinuumAdjoint.Canonical.densityAngular_smooth _ _ _ _
  have hcρ (a : ι) : HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)) := by
    rw [hangular a]
    exact ContinuumAdjoint.Canonical.densityAngular_compact _ _ _ _
  have hχsmooth (a : ι) : ContDiff ℝ ∞ (d a).highCutoff := by
    rw [hhigh a]
    exact FixedCutoffs.highFrequency_smooth
  have hlow (a : ι) (t : ℝ) (ht : t ≤ 1) : (d a).highCutoff t = 0 := by
    rw [hhigh a]
    exact FixedCutoffs.highFrequency_zero ht
  have hhi (a : ι) (t : ℝ) : |(d a).highCutoff t| ≤ 1 := by
    rw [hhigh a]
    exact ContinuumAdjoint.Canonical.densityHigh_abs_le t
  have hρ (a : ι) (z : CarrierParameter) (η : Euclidean (n - 1)) :
      |(d a).angularCutoff z η| ≤ 1 := by
    rw [hangular a]
    have hh := angularMask_mem_Icc (zRoot a) (θ₀ a) (ham a) (hwidth a) z η
    rw [abs_of_nonneg hh.1]
    exact hh.2
  let K := fun a ↦ carrierSupport (zRoot a) (r := am a)
  have hK (a : ι) : IsCompact (K a) := carrierSupport_compact (zRoot a)
  have hsupp (a : ι) (z : CarrierParameter) (hz : z ∉ K a) (η : Euclidean (n - 1)) :
      (d a).angularCutoff z η = 0 := by
    rw [hangular a]
    exact angularMask_zero_outside (zRoot a) (θ₀ a) (ham a) (hwidth a) hz η
  have hp (a : ι) (z : CarrierParameter) (η : Euclidean (n - 1))
      (hn : (d a).angularCutoff z η ≠ 0) : χ a z = 1 := by
    rw [hangular a] at hn
    obtain ⟨hs, hv, _⟩ := angularMask_nonzero (zRoot a) (θ₀ a) (ham a) (hwidth a) hn
    exact (show z ∈ {q : CarrierParameter | χ a q = 1} from
      interior_subset (hplateau a ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩))
  obtain ⟨w, hw, hew, _hweight, hsmooth, hcancel⟩ :=
    exists_smooth_physical_background_cancellation_with_exterior d hρsmooth hcρ hχsmooth hlow hhi
      (fun _ ↦ 1) (fun _ ↦ zero_le_one) hρ
      K hK hsupp hst χ hχ hχc hp hC Y T hYc hTc hY hT hfoot hbase
      c hc hr hcell U hU hk ψ hgap_pos hgap G X₀ H hG hX₀ hH himm hrank hcoeff hreg
  let : (carrierMeasure n).IsOpenPosMeasure := by
    unfold carrierMeasure
    infer_instance
  have hwv : w = v := funext fun a ↦ Measure.eq_of_ae_eq
    ((hew a).trans (he a).symm) (hw a).continuous (hv a).continuous
  rw [hwv] at hcancel
  refine ⟨hsmooth, ?_⟩
  intro x hx hψ i
  have hx4 : x ∈ ball (0 : Euclidean n) (4 * r) :=
    closedBall_subset_ball (by linarith) hx
  have hYx (a : ι) : ContinuousOn ((d a).transportedPosition x) (tsupport (χ a)) :=
    (hYphysical a).continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hz ↦ ⟨hx4, hχV a hz⟩)
  have hνx (a : ι) : ContinuousOn ((d a).normalField x) (tsupport (χ a)) :=
    (hνphysical a).continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hz ↦ ⟨hx4, hχV a hz⟩)
  have hξx (a : ι) : ContinuousOn ((d a).covector x) (tsupport (χ a)) :=
    (hξphysical a).continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hz ↦ ⟨hx4, hχV a hz⟩)
  have hm := measuredIncrement_eq_physicalDensityMean_sub d χ
    (fun a ↦ (hχ a).continuous) hχc v (fun a ↦ (hv a).continuous)
    x (projectedStress G x) hYx hνx hξx (hchart x hx) (hpoint x hx)
    (hmeas x hx) (hstress x hx) i
  have hc := hcancel x hx hψ i
  rw [hm] at hc
  change tensorPairing (projectedStress G x i) (_ + physicalDensityMean d χ 0 x) +
    tensorPairing (projectedStress G x i)
      (physicalDensityMean d χ v x - physicalDensityMean d χ 0 x) = 0 at hc
  simp only [tensorPairing, Matrix.add_apply, Matrix.sub_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at hc ⊢
  linarith only [hc]


/-- The original inverse cancels the literal physical transported tensor mean
on the source/exterior plateau intersection. The supplied exterior cutoff
is retained independently of the measurement radius. Any smooth representative of its SAME factor-four density
can be used, including the one whose smallness was proved by `SourceInverse`.
Smoothness of the uncorrected mean is derived from its original fields; the
physical cancellation is derived from synthesis and covector raising, with
source sign `-1/2`, synthesis factor `4`, and full tangent strain factor `2`.
The supplied external cutoff covers the entire original detector projection;
its absorption and all canonical-mask hypotheses are proved here
(`app:ch_background:eq:bg-current-raising`, `app:ch_background:eq:bg-current-identity`). -/
theorem physicalDensityMean_uncorrected_core_cancellation_with_exterior
    (d : ι → CarrierData n N)
    (zRoot : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1))
    (rm am : ι → ℝ) (hηb : ∀ a, ηb a ≠ 0)
    (hrm : ∀ a, 0 < rm a) (ham : ∀ a, 0 < am a)
    (hangular : ∀ a, (d a).angularCutoff = angularMask (zRoot a)
      (NormedSpace.normalize (ηb a)) (ham a) (angularWidth_spec (hηb a) (hrm a)).1)
    (hhigh : ∀ a, (d a).highCutoff = FixedCutoffs.highFrequency)
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x)
      (maskCarrierProjection (zRoot a) (ηb a) (rm a) (am a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (hplateau : ∀ a, maskCarrierProjection (zRoot a) (ηb a) (rm a) (am a) ⊆
      interior {z | χ a z = 1})
    (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (Y : ι → Torus n × CarrierParameter → Euclidean (n - 1))
    (T : ι → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : ∀ a, Continuous (Y a)) (hTc : ∀ a, Continuous (T a))
    (hY : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y a (torusQuotient p.1, p.2)))
    (hT : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T a (torusQuotient p.1, p.2)))
    (hfoot : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      Y a (x, z) = (d a).transportedPosition ((d a).chartPoint x) z)
    (hbase : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      T a (x, z) = densityTransportMatrix (d a) 0 x z)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a (u : carrierInitialTestSpace n),
      U a (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d a) u.val)
    (hk : ∀ a x, AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n))
    (ψ : C(Torus n, ℝ))
    {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ w, gap * ‖w‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)) U ψ).adjoint w‖ ^ 2)
    (G : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n)
    (hG : ContDiffOn ℝ ∞ G (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (himm : IsImmersionOn G (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn G (ball 0 (4 * r)))
    (hcoeff : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j)
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hYphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).transportedPosition p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hνphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).normalField p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hξphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).covector p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hchart : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      torusQuotient x ∈ (d a).outputChart)
    (hpoint : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      (d a).chartPoint (torusQuotient x) = x)
    (hmeas : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      (d a).measurementCutoff (torusQuotient x) = 1)
    (hstress : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a i,
      (d a).stressFrame x i = projectedStress G x i) :
    let H := physicalDensityMean d χ 0
    let hH := contDiffOn_physicalDensityMean_zero d χ hχ hχc isOpen_ball
      V hV hχV hνphysical hξphysical
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
      (FixedCutoffs.periodic hr hcell 2)
    let θ := FixedCutoffs.periodic hr hcell 0
    let residual := physicalBackgroundResidualToL2 hr hcell G X₀ H hG hX₀ hH himm hrank
    let raw := uncorrectedRawCorrection image U ψ θ residual
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∀ v : ι → CarrierVariable n → ℝ, (∀ a, ContDiff ℝ ∞ (v a)) →
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U ψ θ residual a) →
        ContDiffOn ℝ ∞ (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
          (FixedCutoffs.periodic hr hcell 2) ψ θ U residual G X₀) (ball 0 (4 * r)) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) r,
          torusQuotient x ∈ interior {z | ψ z = 1} → ∀ i,
          tensorPairing (projectedStress G x i)
            (linearizedMetric G (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) ψ θ U residual G X₀) x +
                physicalDensityMean d χ v x) = 0 := by
  have hst' (a : ι) (x) : ContinuousOn (measuredStress (d a) x)
      (carrierSupport (zRoot a) (r := am a)) := by
    rw [← maskCarrierProjection_eq (hηb a) (hrm a) (ham a)]
    exact hst a x
  have hplateau' (a : ι) : carrierSupport (zRoot a) (r := am a) ⊆
      interior {z | χ a z = 1} := by
    rw [← maskCarrierProjection_eq (hηb a) (hrm a) (ham a)]
    exact hplateau a
  exact physicalDensityMean_uncorrected_core_cancellation_of_supplied_masks
    d zRoot (fun a ↦ NormedSpace.normalize (ηb a)) am
    (fun a ↦ angularWidth (ηb a) (rm a)) ham
    (fun a ↦ (angularWidth_spec (hηb a) (hrm a)).1)
    hangular hhigh hst' χ hχ hχc hplateau' hC Y T hYc hTc hY hT hfoot hbase
    c hc hr hcell U hU hk ψ hgap_pos hgap G X₀ hG hX₀ himm hrank hcoeff
    V hV hχV hYphysical hνphysical hξphysical hchart hpoint hmeas hstress

/-- The original fixed-radius physical-mean cancellation theorem. It is the
specialization of the supplied-exterior theorem to the original source cutoff;
its smooth inverse representative and full physical mean are unchanged
(`app:ch_background:eq:bg-current-identity`). -/
theorem physicalDensityMean_uncorrected_core_cancellation
    (d : ι → CarrierData n N)
    (zRoot : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1))
    (rm am : ι → ℝ) (hηb : ∀ a, ηb a ≠ 0)
    (hrm : ∀ a, 0 < rm a) (ham : ∀ a, 0 < am a)
    (hangular : ∀ a, (d a).angularCutoff = angularMask (zRoot a)
      (NormedSpace.normalize (ηb a)) (ham a) (angularWidth_spec (hηb a) (hrm a)).1)
    (hhigh : ∀ a, (d a).highCutoff = FixedCutoffs.highFrequency)
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x)
      (maskCarrierProjection (zRoot a) (ηb a) (rm a) (am a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (hplateau : ∀ a, maskCarrierProjection (zRoot a) (ηb a) (rm a) (am a) ⊆
      interior {z | χ a z = 1})
    (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (Y : ι → Torus n × CarrierParameter → Euclidean (n - 1))
    (T : ι → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : ∀ a, Continuous (Y a)) (hTc : ∀ a, Continuous (T a))
    (hY : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y a (torusQuotient p.1, p.2)))
    (hT : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T a (torusQuotient p.1, p.2)))
    (hfoot : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      Y a (x, z) = (d a).transportedPosition ((d a).chartPoint x) z)
    (hbase : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      T a (x, z) = densityTransportMatrix (d a) 0 x z)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a (u : carrierInitialTestSpace n),
      U a (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d a) u.val)
    (hk : ∀ a x, AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n))
    {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ w, gap * ‖w‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)) U (FixedCutoffs.periodic hr hcell 0)).adjoint w‖ ^ 2)
    (G : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n)
    (hG : ContDiffOn ℝ ∞ G (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (himm : IsImmersionOn G (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn G (ball 0 (4 * r)))
    (hcoeff : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j)
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hYphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).transportedPosition p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hνphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).normalField p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hξphysical : ∀ a, ContDiffOn ℝ ∞
      (fun p ↦ (d a).covector p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V a))
    (hchart : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      torusQuotient x ∈ (d a).outputChart)
    (hpoint : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      (d a).chartPoint (torusQuotient x) = x)
    (hmeas : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a,
      (d a).measurementCutoff (torusQuotient x) = 1)
    (hstress : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a i,
      (d a).stressFrame x i = projectedStress G x i) :
    let H := physicalDensityMean d χ 0
    let hH := contDiffOn_physicalDensityMean_zero d χ hχ hχc isOpen_ball
      V hV hχV hνphysical hξphysical
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
      (FixedCutoffs.periodic hr hcell 2)
    let θ := FixedCutoffs.periodic hr hcell 0
    let residual := physicalBackgroundResidualToL2 hr hcell G X₀ H hG hX₀ hH himm hrank
    let raw := uncorrectedRawCorrection image U θ θ residual
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∀ v : ι → CarrierVariable n → ℝ, (∀ a, ContDiff ℝ ∞ (v a)) →
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U θ θ residual a) →
        ContDiffOn ℝ ∞ (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
          (FixedCutoffs.periodic hr hcell 2) θ θ U residual G X₀) (ball 0 (4 * r)) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ i,
          tensorPairing (projectedStress G x i)
            (linearizedMetric G (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) θ θ U residual G X₀) x +
                physicalDensityMean d χ v x) = 0 := by
  intro H hH image θ residual raw hreg v hv he
  obtain ⟨hsmooth, hcancel⟩ := physicalDensityMean_uncorrected_core_cancellation_with_exterior
    d zRoot ηb rm am hηb hrm ham hangular hhigh hst χ hχ hχc hplateau hC
    Y T hYc hTc hY hT hfoot hbase c hc hr hcell U hU hk
    (FixedCutoffs.periodic hr hcell 0) hgap_pos hgap G X₀ hG hX₀ himm hrank hcoeff
    V hV hχV hYphysical hνphysical hξphysical hchart hpoint hmeas hstress hreg v hv he
  exact ⟨hsmooth, fun x hx i ↦
    hcancel x hx (torusQuotient_mem_fixedSourcePlateau hr hcell hx) i⟩

end JanetCartan.PositiveBackground
