module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.FullNormal

/-!
# One common measurement cutoff for the continuum row

Conditional deduction for `app:ch_background:defn:bg-row`, `bg-T`, and
`bg-realification`. The parent first uses `exists_common_radius` on the finitely
many positive local radii. It then applies `fixed_common_restriction` to each
SAME operator returned by
`CarrierNormalRealization.exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
The test, adjoint and global-normal premises below are conclusions of that
producer, not additional geometric hypotheses. Actual conic and leading-wave
instantiation remains with `jc-continuum-row`.

The common cutoff, image/source cutoff and exterior cutoff are all the original
`FixedCutoffs` functions. The transfer uses normalized torus Haar measure and
retains the original carrier measure. `physicalSandwich_ae_matrixFullAmplitudeOperator`
and `fullReflectedMatrixAmplitude_restrictCoefficients` identify the restricted
physical normal with the full two-position amplitude multiplied at both
positions. Its reflection already contains the quadrature factor four.
-/

@[expose] public noncomputable section
open MeasureTheory Set Metric
namespace JanetCartan.ContinuumRow.CommonMeasurement
open PeriodicLocalL2 ContinuumNormal AmplitudeBound
variable {n N : ℕ}

/-- Restrict one constructed local carrier to the fixed common measurement
cutoff, with its literal common-chart action, adjoint, support, bound and global
normal. All realization premises refer to the SAME `U`; the supported producer
supplies them (`app:ch_background:defn:bg-row`, `bg-T`, `bg-realification`). -/
theorem fixed_common_restriction (d : CarrierData n N)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hrcell : 4 * r < 1 / 2) (hacell : 4 * a < 1 / 2) (hra : 6 * r < a)
    (hchart : d.outputChart = torusChart (closedBall 0 (4 * a)))
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hmeas : d.measurementCutoff = FixedCutoffs.periodic ha hacell 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hUtest : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val)
    (hUadj : ∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
      U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w)
    (A : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hUnormal : carrierChannel U ∘L (carrierChannel U).adjoint =
      realOutputCompression (transferOperator A)) :
    let χ := FixedCutoffs.periodic (n := n) hr hrcell 1
    let e := commonChartData d (closedBall 0 (4 * r)) χ
    let V := restrictCarrier χ U
    ‖V‖ ≤ ‖U‖ ∧
    (∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
    (∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
    (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → V f x = 0) ∧
    carrierChannel V ∘L (carrierChannel V).adjoint =
      realOutputCompression (transferOperator
        (freezingVectorPhysicalMultiplier (FixedCutoffs.physical hr 1)
            (FixedCutoffs.physical hr 1).continuous (FixedCutoffs.physical hr 1).hasCompactSupport ∘L
          A ∘L freezingVectorPhysicalMultiplier (FixedCutoffs.physical hr 1)
            (FixedCutoffs.physical hr 1).continuous (FixedCutoffs.physical hr 1).hasCompactSupport)) := by
  dsimp only
  let χ := FixedCutoffs.periodic (n := n) hr hrcell 1
  have hs : ∀ x, χ x ≠ 0 → x ∈ torusChart (closedBall 0 (4 * r)) :=
    fun _ hx ↦ fixed_measurement_mem_chart hr hrcell hx
  have hK : torusChart (closedBall 0 (4 * r)) ⊆ d.outputChart := by
    rw [hchart]
    exact fun _ hx ↦ closedBall_subset_closedBall (by linarith : 4 * r ≤ 4 * a) hx
  have hp : ∀ x, χ x ≠ 0 → d.measurementCutoff x = 1 := by
    intro x hx
    rw [hmeas]
    exact (mul_eq_left₀ hx).mp
      (physical_measurement_mul hr ha (by linarith : 3 * r ≤ 2 * a)
        (centeredTorusRepresentative x))
  have ht := restrictCarrier_test_common_chart d χ (closedBall 0 (4 * r)) hs hK hpoint hp U hUtest
  refine ⟨?_, ht, restrictCarrier_adjoint_common_chart d χ _ hs hK hpoint hp U hUadj,
    carrierRealization_eq_zero_outside _ _ ht, ?_⟩
  · exact (restrictCarrier_norm_le χ U).trans
      ((mul_le_mul_of_nonneg_right (FixedCutoffs.periodic_norm_le_one hr hrcell 1)
        (norm_nonneg U)).trans_eq (one_mul _))
  · exact restrictCarrier_global_normal χ (FixedCutoffs.physical hr 1)
      (FixedCutoffs.physical hr 1).continuous (FixedCutoffs.physical hr 1).hasCompactSupport
      (fun _ ↦ rfl) U A hUnormal

/-- Finite carrier normals assemble with ONE shared measurement cutoff.
The original reflected operators `A i` already contain factor four; this sum
introduces none (`app:ch_background:defn:bg-row`, `bg-realification`). -/
theorem finite_carrierRow_global_normal {ι : Type*} [Fintype ι]
    (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : Continuous β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z))
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (A : ι → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hU : ∀ i, carrierChannel (U i) ∘L (carrierChannel (U i)).adjoint =
      realOutputCompression (transferOperator (A i))) :
    carrierRow (fun i ↦ restrictCarrier χ (U i)) ∘L
      (carrierRow (fun i ↦ restrictCarrier χ (U i))).adjoint =
        ∑ i, realOutputCompression (transferOperator
          (freezingVectorPhysicalMultiplier β hβ hβs ∘L A i ∘L
            freezingVectorPhysicalMultiplier β hβ hβs)) := by
  rw [carrierRow_normal]
  exact Finset.sum_congr rfl fun i _ ↦
    restrictCarrier_global_normal χ β hβ hβs hχ (U i) (A i) (hU i)

end JanetCartan.ContinuumRow.CommonMeasurement
