module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SmoothSynthesis
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.JetFormula
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.Regularity

/-!
# Physical reduced cancellation for the synthesized background

Specialize the compact source to the actual projected stress and residual
`Dγ_G(dG X₀) + H`. Smoothness of this source is derived from the immersion,
full normal rank and the uncorrected mean. The same original inverse and
factor-four synthesis then cancel the reduced strain of the constructed
FULL tangent base field on the closed physical core, restricted to the supplied
exterior cutoff's open plateau. The old fixed-radius API discharges that
plateau condition from its original geometric cutoff.

This closes the physical realization step of
`app:ch_background:eq:bg-current-identity`. The primitive row, carrier matching,
gap and all-order raw membership are explicit inputs; the actual normalized
producers still owe these for the same seed. Density smallness, positivity,
the corrected gap and the profile are not asserted here.
-/

@[expose] public noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PositiveBackground
open ContinuumRow CarrierSobolev UncutDensity CurrentMean ProjectedStressFrame

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The buffered L² residual constructed from the actual projected stress,
reference tangent field and uncorrected mean. Both local smoothness obligations
are proved from these geometric data (`app:ch_background:eq:bg-current-raising`). -/
def physicalBackgroundResidualToL2 {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (G : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n) (H : MetricField n)
    (hG : ContDiffOn ℝ ∞ G (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r)))
    (himm : IsImmersionOn G (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn G (ball 0 (4 * r))) : OutputL2 n :=
  fixedResidualToL2 hr hcell (projectedStress G)
    (linearizedMetric G (tangentVariation G X₀) + H)
    (contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hG himm hrank))
    ((AmbientResponse.contDiffOn_linearizedMetric isOpen_ball hG
      (contDiffOn_tangentVariation isOpen_ball hG hX₀)).add hH)

/-- Construct the source from the actual immersion and mean, synthesize its
smooth uncut density, and prove the physical reduced cancellation with the
correct positive sign and factor two. The original exterior cutoff is kept
independent of the measurement radius; cancellation is on their open plateau
intersection. No cancellation hypothesis is present
(`app:ch_background:eq:bg-current-raising`, `app:ch_background:eq:bg-current-identity`). -/
theorem exists_smooth_physical_background_cancellation_with_exterior
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
        (FixedCutoffs.periodic hr hcell 2)) U ψ).adjoint w‖ ^ 2)
    (G : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n)
    (H : MetricField n)
    (hG : ContDiffOn ℝ ∞ G (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r)))
    (himm : IsImmersionOn G (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn G (ball 0 (4 * r)))
    (hcoeff : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j) :
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
      (FixedCutoffs.periodic hr hcell 2)
    let θ := FixedCutoffs.periodic hr hcell 0
    let residual := physicalBackgroundResidualToL2 hr hcell G X₀ H hG hX₀ hH himm hrank
    let raw := uncorrectedRawCorrection image U ψ θ residual
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∃ v : ι → CarrierVariable n → ℝ,
        (∀ a, ContDiff ℝ ∞ (v a)) ∧
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U ψ θ residual a) ∧
        (∀ a p, χ a p.1 ^ 2 * v a p = v a p) ∧
        ContDiffOn ℝ ∞ (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
          (FixedCutoffs.periodic hr hcell 2) ψ θ U residual G X₀) (ball 0 (4 * r)) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) r,
          torusQuotient x ∈ interior {z | ψ z = 1} → ∀ i,
          tensorPairing (projectedStress G x i)
            (linearizedMetric G (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) ψ θ U residual G X₀) x + H x) +
            (∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x)) i = 0 := by
  classical
  intro image θ residual raw hreg
  have hQ : ContDiffOn ℝ ∞ (projectedStress G) (ball 0 (4 * r)) :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hG himm hrank)
  have hR : ContDiffOn ℝ ∞ (linearizedMetric G (tangentVariation G X₀) + H)
      (ball 0 (4 * r)) :=
    (AmbientResponse.contDiffOn_linearizedMetric isOpen_ball hG
      (contDiffOn_tangentVariation isOpen_ball hG hX₀)).add hH
  obtain ⟨C, _hC, hconstruct⟩ := exists_smooth_fixedSource_density_cancellation_with_exterior
    d hρsmooth hcρ hχsmooth hlow hhi A hA hρ K hK hsupp hst χ hχ hχc hplateau
    hC Y T hYc hTc hY hT hfoot hbase c hc hr hcell U hU hk ψ hgap_pos hgap
  obtain ⟨v, hv, he, _hb, hw, hcancel⟩ :=
    hconstruct (projectedStress G) (linearizedMetric G (tangentVariation G X₀) + H) hQ hR hreg
  refine ⟨v, hv, he, hw, ?_, ?_⟩
  · exact contDiffOn_uncorrectedBaseVariation c _ _ _ _ U _
      (FixedCutoffs.periodic_smooth hr hcell 2) hreg isOpen_ball hG hX₀ himm
  intro x hx hψ i
  have hx4 : x ∈ ball (0 : Euclidean n) (4 * r) :=
    closedBall_subset_ball (by linarith) hx
  have hstress := ImageGeometry.geometricCubeStress_val_eq_projectedStress
    ((hG.contDiffAt (isOpen_ball.mem_nhds hx4)).of_le (by simp)) (hrank x hx4) i
  have hmeas : FixedCutoffs.periodic hr hcell 1 (torusQuotient x) = 1 := by
    have hx2 : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * r) := by
      apply closedBall_subset_closedBall _ hx
      norm_num
      linarith
    have hp : x ∈ {y | FixedCutoffs.physical hr 1 y = 1} :=
      interior_subset (FixedCutoffs.physical_plateau hr 1 hx2)
    exact (FixedCutoffs.periodic_eventuallyEq hr hcell 1
      (closedBall_subset_closedBall (by linarith) hx)).eq_of_nhds.trans hp
  have hstrain := uncorrectedBaseVariation_reduced_strain c _ _ _ _ U _
    (FixedCutoffs.periodic_smooth hr hcell 2) hreg isOpen_ball hG hX₀ himm hx4
    (hcoeff x hx) hmeas i
  rw [hstress] at hstrain
  have hcancel' := congrArg (fun z : Euclidean n ↦ z i) (hcancel x hx hψ)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hcancel'
  change tensorPairing ((linearizedMetric G (tangentVariation G X₀) + H) x)
    (projectedStress G x i) +
    2 * _ + _ = 0 at hcancel'
  have hpair (A B : MetricTensor n) :
      tensorPairing (projectedStress G x i) (A + B) =
        tensorPairing (projectedStress G x i) A + tensorPairing (projectedStress G x i) B := by
    simp [tensorPairing, mul_add, Finset.sum_add_distrib]
  have hflip (A : MetricTensor n) : tensorPairing A (projectedStress G x i) =
      tensorPairing (projectedStress G x i) A := by
    simp only [tensorPairing, mul_comm]
  -- `tensorContraction` puts the tensor in the first Frobenius slot.
  simp only [Pi.add_apply, hflip, hpair] at hcancel'
  rw [hpair, hstrain]
  let a := tensorPairing (projectedStress G x i) (linearizedMetric G (tangentVariation G X₀) x)
  let b := tensorPairing (projectedStress G x i) (H x)
  let imageValue := uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
    (FixedCutoffs.periodic hr hcell 2) raw.fst.fst (torusQuotient x) i
  let increment := (∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x)) i
  change a + b + 2 * imageValue + increment = 0 at hcancel'
  change a + 2 * imageValue + b + increment = 0
  linarith only [hcancel']

/-- The original fixed-radius physical cancellation API, specialized from
cancellation on the source/exterior plateau intersection. The reference field,
source, density and tangent strain are unchanged
(`app:ch_background:eq:bg-current-identity`). -/
theorem exists_smooth_physical_background_cancellation
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
        (FixedCutoffs.periodic hr hcell 2)) U (FixedCutoffs.periodic hr hcell 0)).adjoint w‖ ^ 2)
    (G : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n)
    (H : MetricField n)
    (hG : ContDiffOn ℝ ∞ G (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r)))
    (himm : IsImmersionOn G (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn G (ball 0 (4 * r)))
    (hcoeff : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j) :
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1)
      (FixedCutoffs.periodic hr hcell 2)
    let θ := FixedCutoffs.periodic hr hcell 0
    let residual := physicalBackgroundResidualToL2 hr hcell G X₀ H hG hX₀ hH himm hrank
    let raw := uncorrectedRawCorrection image U θ θ residual
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∃ v : ι → CarrierVariable n → ℝ,
        (∀ a, ContDiff ℝ ∞ (v a)) ∧
        (∀ a, v a =ᵐ[carrierMeasure n] uncorrectedDensity d image U θ θ residual a) ∧
        (∀ a p, χ a p.1 ^ 2 * v a p = v a p) ∧
        ContDiffOn ℝ ∞ (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
          (FixedCutoffs.periodic hr hcell 2) θ θ U residual G X₀) (ball 0 (4 * r)) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ i,
          tensorPairing (projectedStress G x i)
            (linearizedMetric G (uncorrectedBaseVariation c (FixedCutoffs.periodic hr hcell 1)
              (FixedCutoffs.periodic hr hcell 2) θ θ U residual G X₀) x + H x) +
            (∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x)) i = 0 := by
  intro image θ residual raw hreg
  obtain ⟨v, hv, he, hw, hsmooth, hcancel⟩ :=
    exists_smooth_physical_background_cancellation_with_exterior
      d hρsmooth hcρ hχsmooth hlow hhi A hA hρ K hK hsupp hst χ hχ hχc hplateau
      hC Y T hYc hTc hY hT hfoot hbase c hc hr hcell U hU hk
      (FixedCutoffs.periodic hr hcell 0) hgap_pos hgap G X₀ H hG hX₀ hH himm hrank hcoeff hreg
  exact ⟨v, hv, he, hw, hsmooth, fun x hx i ↦
    hcancel x hx (torusQuotient_mem_fixedSourcePlateau hr hcell hx) i⟩

end JanetCartan.PositiveBackground
