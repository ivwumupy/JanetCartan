module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalCorrection
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.FixedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.DensityRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationTransport

/-!
# Smooth factor-four synthesis for the actual compact source

The source, residual representative, raw correction and image representative
below are the concrete constructions already published for
`app:ch_background:eq:bg-current-raising`. Apply the uncut density construction
to that SAME raw correction, then derive pointwise cancellation on an open
source/exterior plateau from the original inverse equation. The constants in
the density estimate precede the source. No cancellation or smooth output is
assumed. Primitive carrier realization, matching geometric extensions, the
uncorrected gap and its all-order raw regularity remain producer obligations.
This does not assert density smallness or the corrected-positive row gap.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PositiveBackground
open ContinuumRow CarrierSobolev UncutDensity CurrentMean

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The smooth factor-four density of the SAME uncorrected inverse cancels
the constructed compact source pointwise on the open core. The exterior slot
is retained with its own supplied cutoff, independently of the measurement
radius, and removed only on its original open plateau
(`app:ch_background:eq:bg-density-four`, `app:ch_background:eq:bg-current-identity`). -/
theorem exists_smooth_fixedSource_density_cancellation_with_exterior
    (d : ι → CarrierData n N)
    (hρsmooth : ∀ a, ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)))
    (hcρ : ∀ a, HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ∀ a, ContDiff ℝ ∞ (d a).highCutoff)
    (hlow : ∀ a r, r ≤ 1 → (d a).highCutoff r = 0)
    (hhi : ∀ a r, |(d a).highCutoff r| ≤ 1)
    (A : ι → ℝ) (hA : ∀ a, 0 ≤ A a)
    (hρ : ∀ a z η, |(d a).angularCutoff z η| ≤ A a)
    (K : ι → Set CarrierParameter) (hK : ∀ a, IsCompact (K a))
    (hsupp : ∀ a z, z ∉ K a → ∀ η, (d a).angularCutoff z η = 0)
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x) (K a))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (hplateau : ∀ a z η, (d a).angularCutoff z η ≠ 0 → χ a z = 1)
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
        (FixedCutoffs.periodic hr hcell 2)) U ψ).adjoint w‖ ^ 2) :
    ∃ C : ι → ℕ → ℝ, (∀ a s, 0 ≤ C a s) ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
        (hQ : ContDiffOn ℝ ∞ Q (Metric.ball 0 (4 * r)))
        (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 (4 * r))),
      let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)
      let θ := FixedCutoffs.periodic hr hcell 0
      let residual := fixedResidualToL2 hr hcell Q R hQ hR
      let raw := uncorrectedRawCorrection image U ψ θ residual
      (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∃ v : ι → CarrierVariable n → ℝ,
        (∀ a, ContDiff ℝ ∞ (v a)) ∧
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U ψ θ residual a) ∧
        (∀ a s, cNorm univ s (v a) ≤
          C a s * rawSobolevNorm (s + (3 + (n - 1) + 1) + 1) (raw.fst.snd a)) ∧
        (∀ a p, χ a p.1 ^ 2 * v a p = v a p) ∧
        ∀ x ∈ Metric.closedBall (0 : Euclidean n) r,
          torusQuotient x ∈ interior {z | ψ z = 1} →
          WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x)) +
            (2 : ℝ) • uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) raw.fst.fst (torusQuotient x) +
            ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x) = 0 := by
  classical
  choose C hCpos hconstruct using fun a ↦ exists_smooth_initialDensity_four (d a)
    (hρsmooth a) (hcρ a) (hχsmooth a) (hlow a) (hhi a) (hA a) (hρ a)
  refine ⟨C, hCpos, ?_⟩
  intro Q R hQ hR image θ residual raw hreg
  have hraw (a : ι) (s : ℕ) : MemRawSobolev s (raw.fst.snd a) :=
    ((mem_augmentedInputLevel_iff s raw).mp (hreg s)).2.1 a
  have him (s : ℕ) : raw.fst.fst ∈ periodicSobolevLevel n (Euclidean n) s :=
    ((mem_augmentedInputLevel_iff s raw).mp (hreg s)).1
  choose v hv he hb _hnorm _hpositions hmean hweight using
    fun a ↦ hconstruct a (raw.fst.snd a) (hraw a)
  refine ⟨v, hv, he, hb, fun a ↦ hweight a (χ a) (hχ a).continuous (hplateau a), ?_⟩
  have hcancel := uncorrectedDensity_core_cancellation d (n + 1) (by omega)
    χ hplateau U hU hk hK hsupp hst hA (fun _ ↦ zero_le_one) hρ hhi
    image ψ θ residual hgap_pos hgap (hreg (n + 1 + 1))
  have hmeanEq : (fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) x) =
      fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
        (uncorrectedDensity d image U ψ θ residual a) x := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    exact congrFun (hmean a (fun z ↦ χ a z ^ 2)) x
  have hmeanSmooth (a : ι) := isSmoothPeriodic_measuredIncrement_of_extensions
    (d a) (hC a) (χ a) (hχ a) (hχc a) (Y a) (T a)
    (hYc a) (hTc a) (hY a) (hT a) (hfoot a) (hbase a) (v a) (hv a)
  have himSmooth := isSmoothPeriodic_uncutImageRepresentative c hc
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    (FixedCutoffs.periodic_smooth hr hcell 1) (FixedCutoffs.periodic_smooth hr hcell 2)
    raw.fst.fst him
  have hae : (fun x ↦ fixedResidualRepresentative hr Q R x +
      (2 : ℝ) • uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2) raw.fst.fst x +
      ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) x) =ᵐ[
        volume.restrict (interior {x | θ x = 1} ∩ interior {x | ψ x = 1})] fun _ ↦ 0 := by
    apply (ae_restrict_iff' (isOpen_interior.inter isOpen_interior).measurableSet).mpr
    filter_upwards [hcancel, fixedResidualRepresentative_ae hr hcell Q R hQ hR,
      uncutImageRepresentative_ae c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2) (FixedCutoffs.periodic_smooth hr hcell 2)
        raw.fst.fst him] with x hx hres himg
    intro hcore
    have hθ : x ∈ {y | θ y = 1} := interior_subset hcore.1
    change θ x = 1 at hθ
    have hψ : x ∈ {y | ψ y = 1} := interior_subset hcore.2
    rw [← hres, ← himg, congrFun hmeanEq x]
    exact hx hψ hθ
  have hpoint := Measure.eqOn_open_of_ae_eq hae (isOpen_interior.inter isOpen_interior)
    (((isSmoothPeriodic_fixedResidualRepresentative hr hcell hQ hR).1.add
      (himSmooth.1.const_smul (2 : ℝ))).add
        (continuous_finsetSum Finset.univ (fun a _ ↦ (hmeanSmooth a).1))).continuousOn
    continuousOn_const
  intro x hx hψ
  have h := hpoint ⟨torusQuotient_mem_fixedSourcePlateau hr hcell hx, hψ⟩
  dsimp only at h
  rw [fixedResidualRepresentative_on_core hr hcell Q R hx] at h
  exact h

/-- The original core cancellation is the specialization where the supplied
exterior cutoff is the original fixed source cutoff. The statement and all
representatives are retained (`app:ch_background:eq:bg-current-identity`). -/
theorem exists_smooth_fixedSource_density_cancellation
    (d : ι → CarrierData n N)
    (hρsmooth : ∀ a, ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)))
    (hcρ : ∀ a, HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ∀ a, ContDiff ℝ ∞ (d a).highCutoff)
    (hlow : ∀ a r, r ≤ 1 → (d a).highCutoff r = 0)
    (hhi : ∀ a r, |(d a).highCutoff r| ≤ 1)
    (A : ι → ℝ) (hA : ∀ a, 0 ≤ A a)
    (hρ : ∀ a z η, |(d a).angularCutoff z η| ≤ A a)
    (K : ι → Set CarrierParameter) (hK : ∀ a, IsCompact (K a))
    (hsupp : ∀ a z, z ∉ K a → ∀ η, (d a).angularCutoff z η = 0)
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x) (K a))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (hplateau : ∀ a z η, (d a).angularCutoff z η ≠ 0 → χ a z = 1)
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
        (FixedCutoffs.periodic hr hcell 2)) U (FixedCutoffs.periodic hr hcell 0)).adjoint w‖ ^ 2) :
    ∃ C : ι → ℕ → ℝ, (∀ a s, 0 ≤ C a s) ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
        (hQ : ContDiffOn ℝ ∞ Q (Metric.ball 0 (4 * r)))
        (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 (4 * r))),
      let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
        (FixedCutoffs.periodic hr hcell 2)
      let θ := FixedCutoffs.periodic hr hcell 0
      let residual := fixedResidualToL2 hr hcell Q R hQ hR
      let raw := uncorrectedRawCorrection image U θ θ residual
      (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∃ v : ι → CarrierVariable n → ℝ,
        (∀ a, ContDiff ℝ ∞ (v a)) ∧
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U θ θ residual a) ∧
        (∀ a s, cNorm univ s (v a) ≤
          C a s * rawSobolevNorm (s + (3 + (n - 1) + 1) + 1) (raw.fst.snd a)) ∧
        (∀ a p, χ a p.1 ^ 2 * v a p = v a p) ∧
        ∀ x ∈ Metric.closedBall (0 : Euclidean n) r,
          WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x)) +
            (2 : ℝ) • uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) raw.fst.fst (torusQuotient x) +
            ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x) = 0 := by
  obtain ⟨C, hCpos, hconstruct⟩ := exists_smooth_fixedSource_density_cancellation_with_exterior
    d hρsmooth hcρ hχsmooth hlow hhi A hA hρ K hK hsupp hst χ hχ hχc hplateau
    hC Y T hYc hTc hY hT hfoot hbase c hc hr hcell U hU hk
    (FixedCutoffs.periodic hr hcell 0) hgap_pos hgap
  refine ⟨C, hCpos, ?_⟩
  intro Q R hQ hR image θ residual raw hreg
  obtain ⟨v, hv, he, hb, hw, hcancel⟩ := hconstruct Q R hQ hR hreg
  exact ⟨v, hv, he, hb, hw, fun x hx ↦
    hcancel x hx (torusQuotient_mem_fixedSourcePlateau hr hcell hx)⟩

end JanetCartan.PositiveBackground
