module

public import JanetCartan.Iteration.PhysicalBackground.Synthesis
public import JanetCartan.Iteration.PhysicalBackground.Field
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMean

/-!
# Exact current physical background cancellation in v2 normalization

The SAME factor-two density constructed from the measured source cancels the
literal physical affine mean, using `Vbase=dF X₀+J_F h_image`. Smooth source and
field realization are proved from the actual geometric fields. The current
carrier actions, original exterior, and task22 raw membership are retained.
No cancellation hypothesis or independent density/row selection is introduced.
This downstream deduction does not close the original-data source smallness
and all-order current-profile obligations of task24.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev UncutDensity PositiveBackground CurrentMean ProjectedStressFrame

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The literal continuum mean of the SAME current carriers cancels the strain
of the v2 physical base on the original core/exterior plateau. In applications
`F` is exactly `RevisedGlobal.finiteMap Gref.map history`, and `X₀` is formed
from the original constant limiting mean, not a current adaptive mean.
The density premise identifies the ONE representative constructed in `Density`
and `Admission`; it is not a cancellation or positivity-success premise
(`app:ch_background:eq:bg-current-identity`, `new:lem:mean-source-identity`). -/
theorem physicalDensityMean_core_cancellation
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
    (F : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n)
    (hF : ContDiffOn ℝ ∞ F (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (himm : IsImmersionOn F (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn F (ball 0 (4 * r)))
    (hcoeff : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (V : ι → Set CarrierParameter) (hV : ∀ i, IsOpen (V i))
    (hχV : ∀ i, tsupport (χ i) ⊆ V i)
    (hYphysical : ∀ i, ContDiffOn ℝ ∞
      (fun p ↦ (d i).transportedPosition p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V i))
    (hνphysical : ∀ i, ContDiffOn ℝ ∞
      (fun p ↦ (d i).normalField p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V i))
    (hξphysical : ∀ i, ContDiffOn ℝ ∞
      (fun p ↦ (d i).covector p.1 p.2) (ball (0 : Euclidean n) (4 * r) ×ˢ V i))
    (hchart : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ i, torusQuotient x ∈ (d i).outputChart)
    (hpoint : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ i, (d i).chartPoint (torusQuotient x) = x)
    (hmeas : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ i, (d i).measurementCutoff (torusQuotient x) = 1)
    (hstress : ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ a i,
      (d a).stressFrame x i = projectedStress F x i) :
    let H := physicalDensityMean d χ 0
    let hH := contDiffOn_physicalDensityMean_zero d χ hχ hχc isOpen_ball
      V hV hχV hνphysical hξphysical
    let image := imageChannel c (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    let e := physicalSourceToL2 hr hcell F X₀ H hF hX₀ hH himm hrank
    let raw := rawCorrection image U ψ e
    (∀ s, raw ∈ augmentedInputLevel n ι s) →
    ∀ v : ι → CarrierVariable n → ℝ, (∀ i, ContDiff ℝ ∞ (v i)) →
      (∀ i, v i =ᵐ[carrierMeasure n] uncutDensity d image U ψ e i) →
      ContDiffOn ℝ ∞ (baseVariation (FixedCutoffs.periodic hr hcell 2) raw F X₀) (ball 0 (4 * r)) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) r,
        torusQuotient x ∈ interior {z | ψ z = 1} → ∀ i,
        tensorPairing (projectedStress F x i)
          (linearizedMetric F (baseVariation (FixedCutoffs.periodic hr hcell 2) raw F X₀) x +
            physicalDensityMean d χ v x) = 0 := by
  intro H hH image e raw hreg v hv he
  have hQ : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (4 * r)) :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF himm hrank)
  have hR : ContDiffOn ℝ ∞ (linearizedMetric F (tangentVariation F X₀) + H)
      (ball 0 (4 * r)) :=
    (AmbientResponse.contDiffOn_linearizedMetric isOpen_ball hF
      (contDiffOn_tangentVariation isOpen_ball hF hX₀)).add hH
  have hcancel := measuredSource_core_cancellation d hρsmooth hχsmooth hρ hhi
    K hK hsupp hst χ hχ hχc hplateau hC Y T hYc hTc hY hT hfoot hbase c hc hr hcell
    U hU hk ψ hgap hcoercive (projectedStress F)
    (linearizedMetric F (tangentVariation F X₀) + H) hQ hR hreg v hv he
  refine ⟨contDiffOn_baseVariation _ (FixedCutoffs.periodic_smooth hr hcell 2)
    raw hreg isOpen_ball hF hX₀ himm, ?_⟩
  intro x hx hψ i
  have hx4 : x ∈ ball (0 : Euclidean n) (4 * r) := closedBall_subset_ball (by linarith) hx
  have hstress' := ImageGeometry.geometricCubeStress_val_eq_projectedStress
    ((hF.contDiffAt (isOpen_ball.mem_nhds hx4)).of_le (by simp)) (hrank x hx4) i
  have hmeas' : FixedCutoffs.periodic hr hcell 1 (torusQuotient x) = 1 := by
    have hx2 : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * r) := by
      apply closedBall_subset_closedBall _ hx
      norm_num
      linarith
    have hp : x ∈ {y | FixedCutoffs.physical hr 1 y = 1} :=
      interior_subset (FixedCutoffs.physical_plateau hr 1 hx2)
    exact (FixedCutoffs.periodic_eventuallyEq hr hcell 1
      (closedBall_subset_closedBall (by linarith) hx)).eq_of_nhds.trans hp
  have hstrain := baseVariation_reduced_strain c _ _
    (FixedCutoffs.periodic_smooth hr hcell 2) raw hreg isOpen_ball hF hX₀ himm hx4
    (hcoeff x hx) hmeas' i
  rw [hstress'] at hstrain
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
    x (projectedStress F x) hYx hνx hξx (hchart x hx) (hpoint x hx)
    (hmeas x hx) (hstress x hx) i
  have hb := congrArg (fun z : Euclidean n ↦ z i) (hcancel x hx hψ)
  simp only [PiLp.add_apply, PiLp.zero_apply] at hb
  change tensorPairing ((linearizedMetric F (tangentVariation F X₀) + H) x)
    (projectedStress F x i) + _ + _ = 0 at hb
  have hflip (A : MetricTensor n) : tensorPairing A (projectedStress F x i) =
      tensorPairing (projectedStress F x i) A := by simp only [tensorPairing, mul_comm]
  have hpair (A B : MetricTensor n) : tensorPairing (projectedStress F x i) (A + B) =
      tensorPairing (projectedStress F x i) A + tensorPairing (projectedStress F x i) B := by
    simp [tensorPairing, mul_add, Finset.sum_add_distrib]
  have hsub (A B : MetricTensor n) : tensorPairing (projectedStress F x i) (A - B) =
      tensorPairing (projectedStress F x i) A - tensorPairing (projectedStress F x i) B := by
    simp [tensorPairing, mul_sub, Finset.sum_sub_distrib]
  rw [hm] at hb
  simp only [Pi.add_apply, hflip, hpair, hsub] at hb
  rw [hpair, hstrain]
  let a := tensorPairing (projectedStress F x i) (linearizedMetric F (tangentVariation F X₀) x)
  let b := tensorPairing (projectedStress F x i) (physicalDensityMean d χ 0 x)
  let p := tensorPairing (projectedStress F x i) (physicalDensityMean d χ v x)
  let imageValue := uncutImageRepresentative c (FixedCutoffs.periodic hr hcell 1)
    (FixedCutoffs.periodic hr hcell 2) raw.fst.fst (torusQuotient x) i
  change a + b + imageValue + (p - b) = 0 at hb
  change a + imageValue + p = 0
  linarith only [hb]

end JanetCartan.PhysicalBackground
