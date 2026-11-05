module

public import JanetCartan.Iteration.PhysicalBackground.Density
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationTransport

/-!
# The v2 density row identity for the same current inverse

The factor-two uncut density realizes exactly one carrier row. With the literal
measured source this cancels the residual plus one image output on the original
exterior plateau. This is the algebraic part of
`app:ch_background:eq:bg-current-identity`, not a new cancellation premise.
The original-data current row and its raw regularity are still task22 inputs.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev UncutDensity PositiveBackground CurrentMean

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Factor two, not four: the literal v2 density of the SAME raw current input
is exactly the real carrier row (`app:ch_background:eq:bg-density-row`). -/
theorem measuredIncrement_rawCorrection
    (d : ι → CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ i z η, (d i).angularCutoff z η ≠ 0 → χ i z = 1)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ i (u : carrierInitialTestSpace n),
      U i (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d i) u.val)
    (hk : ∀ i x, AEStronglyMeasurable (carrierKernel (d i) x) (carrierMeasure n))
    {K : ι → Set CarrierParameter} (hK : ∀ i, IsCompact (K i))
    (hsupp : ∀ i z, z ∉ K i → ∀ η, (d i).angularCutoff z η = 0)
    (hst : ∀ i x, ContinuousOn (measuredStress (d i) x) (K i))
    (hρ : ∀ i z η, |(d i).angularCutoff z η| ≤ 1)
    (hhi : ∀ i t, |(d i).highCutoff t| ≤ 1)
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ)) (e : OutputL2 n)
    (hreg : rawCorrection image U ψ e ∈ augmentedInputLevel n ι (s + 1)) :
    (fun x ↦ ∑ i, measuredIncrement (d i) (fun z ↦ χ i z ^ 2)
      (uncutDensity d image U ψ e i) x) =ᵐ[volume]
      (carrierRow U (rawCorrection image U ψ e).fst.snd : OutputL2 n) := by
  simpa only [uncutDensity, show (2 : ℝ) / 2 = 1 by norm_num, one_smul] using
    UncutDensity.measuredIncrement_sum d s hs χ hχ U hU hk hK hsupp hst
      (fun _ ↦ zero_le_one) (fun _ ↦ zero_le_one) hρ hhi 2
      (rawCorrection image U ψ e).fst.snd
      (fun i ↦ augmentedInput_carrierWeightedMem hreg i)

/-- The v2 source and original augmented inverse cancel with coefficient ONE
on the image and carrier outputs. The supplied exterior is removed only on
its own plateau, never identified with physical strain globally. -/
theorem measuredSource_core_cancellation_ae
    (d : ι → CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ i z η, (d i).angularCutoff z η ≠ 0 → χ i z = 1)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ i (u : carrierInitialTestSpace n),
      U i (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d i) u.val)
    (hk : ∀ i x, AEStronglyMeasurable (carrierKernel (d i) x) (carrierMeasure n))
    {K : ι → Set CarrierParameter} (hK : ∀ i, IsCompact (K i))
    (hsupp : ∀ i z, z ∉ K i → ∀ η, (d i).angularCutoff z η = 0)
    (hst : ∀ i x, ContinuousOn (measuredStress (d i) x) (K i))
    (hρ : ∀ i z η, |(d i).angularCutoff z η| ≤ 1)
    (hhi : ∀ i t, |(d i).highCutoff t| ≤ 1)
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ)) (residual : OutputL2 n)
    {gap : ℝ} (hgap : 0 < gap)
    (hcoercive : ∀ w, gap * ‖w‖ ^ 2 ≤ ‖(augmentedRow image U ψ).adjoint w‖ ^ 2)
    (hreg : rawCorrection image U ψ (-residual) ∈ augmentedInputLevel n ι (s + 1)) :
    ∀ᵐ x ∂volume, ψ x = 1 →
      residual x + image (rawCorrection image U ψ (-residual)).fst.fst x +
        ∑ i, measuredIncrement (d i) (fun z ↦ χ i z ^ 2)
          (uncutDensity d image U ψ (-residual) i) x = 0 := by
  let h := rawCorrection image U ψ (-residual)
  have hden := measuredIncrement_rawCorrection d s hs χ hχ U hU hk hK hsupp hst
    hρ hhi image ψ (-residual) hreg
  have heq : image h.fst.fst + carrierRow U h.fst.snd + exteriorChannel ψ h.snd =
      -residual := by
    simpa only [augmentedRow_apply, physicalRow_apply] using
      row_rawCorrection image U ψ (-residual) hgap hcoercive
  have heqae : (image h.fst.fst + carrierRow U h.fst.snd + exteriorChannel ψ h.snd :
      OutputL2 n) =ᵐ[volume] (-residual : OutputL2 n) := by rw [heq]
  filter_upwards [hden, heqae,
    Lp.coeFn_add (image h.fst.fst + carrierRow U h.fst.snd) (exteriorChannel ψ h.snd),
    Lp.coeFn_add (image h.fst.fst) (carrierRow U h.fst.snd),
    exteriorChannel_coeFn ψ h.snd, Lp.coeFn_neg residual] with x hd he ha hb hx hn
  intro hψ
  simp only [Pi.add_apply] at ha hb
  simp only [Pi.neg_apply] at hn
  change _ = (1 - ψ x) • h.snd x at hx
  rw [ha, hb, hx, hψ, sub_self, zero_smul, add_zero, hn] at he
  rw [hd, add_assoc, he, add_neg_cancel]

/-- Promote the exact v2 identity to every point on the same open exterior
plateau, for ANY smooth representative of the constructed factor-two density.
There is no additional source cutoff or density-selection mismatch. -/
theorem measuredSource_core_cancellation
    (d : ι → CarrierData n N)
    (hρsmooth : ∀ i, ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d i).angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ∀ i, ContDiff ℝ ∞ (d i).highCutoff)
    (hρ : ∀ i z η, |(d i).angularCutoff z η| ≤ 1)
    (hhi : ∀ i t, |(d i).highCutoff t| ≤ 1)
    (K : ι → Set CarrierParameter) (hK : ∀ i, IsCompact (K i))
    (hsupp : ∀ i z, z ∉ K i → ∀ η, (d i).angularCutoff z η = 0)
    (hst : ∀ i x, ContinuousOn (measuredStress (d i) x) (K i))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i))
    (hplateau : ∀ i z η, (d i).angularCutoff z η ≠ 0 → χ i z = 1)
    (hC : ∀ i, IsSmoothPeriodic (preparationMeasurement (d i)))
    (Y : ι → Torus n × CarrierParameter → Euclidean (n - 1))
    (T : ι → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : ∀ i, Continuous (Y i)) (hTc : ∀ i, Continuous (T i))
    (hY : ∀ i, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y i (torusQuotient p.1, p.2)))
    (hT : ∀ i, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T i (torusQuotient p.1, p.2)))
    (hfoot : ∀ i x, x ∈ (d i).outputChart → ∀ z, χ i z ≠ 0 →
      Y i (x, z) = (d i).transportedPosition ((d i).chartPoint x) z)
    (hbase : ∀ i x, x ∈ (d i).outputChart → ∀ z, χ i z ≠ 0 →
      T i (x, z) = densityTransportMatrix (d i) 0 x z)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ i (u : carrierInitialTestSpace n),
      U i (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d i) u.val)
    (hk : ∀ i x, AEStronglyMeasurable (carrierKernel (d i) x) (carrierMeasure n))
    (ψ : C(Torus n, ℝ)) {gap : ℝ} (hgap : 0 < gap)
    (hcoercive : ∀ w, gap * ‖w‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)) U ψ).adjoint w‖ ^ 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (Metric.ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 (4 * r))) :
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    let e := measuredSourceToL2 hr hcell Q R hQ hR
    let raw := rawCorrection image U ψ e
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
    ∀ v : ι → CarrierVariable n → ℝ, (∀ i, ContDiff ℝ ∞ (v i)) →
      (∀ i, v i =ᵐ[carrierMeasure n] uncutDensity d image U ψ e i) →
      ∀ x ∈ Metric.closedBall (0 : Euclidean n) r,
        torusQuotient x ∈ interior {z | ψ z = 1} →
        WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x)) +
          uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
            (FixedCutoffs.periodic hr hcell 2) raw.fst.fst (torusQuotient x) +
          ∑ i, measuredIncrement (d i) (fun z ↦ χ i z ^ 2) (v i) (torusQuotient x) = 0 := by
  intro image e raw hreg v hv he
  have hraw (i : ι) (s : ℕ) : MemRawSobolev s (raw.fst.snd i) :=
    ((mem_augmentedInputLevel_iff s raw).mp (hreg s)).2.1 i
  have him (s : ℕ) : raw.fst.fst ∈ periodicSobolevLevel n (Euclidean n) s :=
    ((mem_augmentedInputLevel_iff s raw).mp (hreg s)).1
  have hmean (i : ι) : measuredIncrement (d i) (fun z ↦ χ i z ^ 2) (v i) =
      measuredIncrement (d i) (fun z ↦ χ i z ^ 2) (uncutDensity d image U ψ e i) := by
    apply CurrentMean.measuredIncrement_eq_of_ae_all_positions
    exact CurrentMean.initialDensity_ae_all_positions (d i) (n + 1) (by omega)
      (hρsmooth i).continuous.measurable (hχsmooth i).continuous.measurable
      zero_le_one zero_le_one (hρ i) (hhi i) 2 _ (hraw i _) _ (hv i).continuous (he i)
  have hcancel := measuredSource_core_cancellation_ae d (n + 1) (by omega) χ hplateau U hU hk
    hK hsupp hst hρ hhi image ψ (fixedResidualToL2 hr hcell Q R hQ hR)
    hgap hcoercive (hreg _)
  have hm (i : ι) := isSmoothPeriodic_measuredIncrement_of_extensions
    (d i) (hC i) (χ i) (hχ i) (hχc i) (Y i) (T i)
    (hYc i) (hTc i) (hY i) (hT i) (hfoot i) (hbase i) (v i) (hv i)
  have hi := isSmoothPeriodic_uncutImageRepresentative c hc
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    (FixedCutoffs.periodic_smooth hr hcell 1) (FixedCutoffs.periodic_smooth hr hcell 2)
    raw.fst.fst him
  have hae : (fun x ↦ fixedResidualRepresentative hr Q R x +
      uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2) raw.fst.fst x +
      ∑ i, measuredIncrement (d i) (fun z ↦ χ i z ^ 2) (v i) x) =ᵐ[
      volume.restrict (interior {x | ψ x = 1})] fun _ ↦ 0 := by
    apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
    filter_upwards [hcancel, fixedResidualRepresentative_ae hr hcell Q R hQ hR,
      uncutImageRepresentative_ae c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2) (FixedCutoffs.periodic_smooth hr hcell 2)
        raw.fst.fst him] with x hx hres himg
    intro hcore
    rw [← hres, ← himg]
    simp only [hmean]
    have hp : x ∈ {z | ψ z = 1} := interior_subset hcore
    exact hx hp
  have hpoint := Measure.eqOn_open_of_ae_eq hae isOpen_interior
    (((isSmoothPeriodic_fixedResidualRepresentative hr hcell hQ hR).1.add hi.1).add
      (continuous_finsetSum Finset.univ (fun i _ ↦ (hm i).1))).continuousOn continuousOn_const
  intro x hx hψ
  have h := hpoint hψ
  dsimp only at h
  rw [fixedResidualRepresentative_on_core hr hcell Q R hx] at h
  exact h

end JanetCartan.PhysicalBackground
