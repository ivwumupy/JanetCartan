module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationSmooth

/-!
# Smooth transported densities on the original preparation space

The transport operator in `app:ch_mean_pairs:eq:mean-density-recursion`
is the literal uncut measured increment. Its regularity follows from joint
extensions of the original footpoint and base transport matrix on the fixed
measurement plateau. Compactness is imposed only on the external carrier
weight; no cutoff is inserted in the initial position.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.CurrentMean
open ContinuumRow UncutDensity

variable {n N : ℕ}

/-- Joint geometric extensions make the literal transported density smooth
on the torus (`app:ch_mean_pairs:eq:mean-density-recursion`). No positivity
of the density is needed for this linear operator. -/
theorem isSmoothPeriodic_measuredIncrement_of_extensions
    (d : CarrierData n N) (hC : IsSmoothPeriodic (preparationMeasurement d))
    (χ : CarrierParameter → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : Continuous Y) (hTc : Continuous T)
    (hY : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y (torusQuotient p.1,p.2)))
    (hT : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T (torusQuotient p.1,p.2)))
    (hfoot : ∀ x ∈ d.outputChart, ∀ z, χ z ≠ 0 →
      Y (x,z) = d.transportedPosition (d.chartPoint x) z)
    (hbase : ∀ x ∈ d.outputChart, ∀ z, χ z ≠ 0 →
      T (x,z) = densityTransportMatrix d 0 x z)
    (v : CarrierVariable n → ℝ) (hv : ContDiff ℝ ∞ v) :
    IsSmoothPeriodic (measuredIncrement d (fun z ↦ χ z ^ 2) v) := by
  let f := fun p : Torus n × CarrierParameter ↦
    v (p.2,Y p) • (χ p.2 ^ 2 • preparationMeasurement d p.1 (hermitianTensor (T p)))
  have hb := preparationHermitianIntegrand_regular (preparationMeasurement d) hC χ hχ
    T 0 hTc continuous_const hT contDiff_const
  have hz : hermitianTensor (0 : Matrix (Fin N) (Fin n) ℂ) = 0 := by
    ext i j
    simp [hermitianTensor]
  simp only [Pi.zero_apply, hz, sub_zero] at hb
  have hfc : Continuous f :=
    (hv.continuous.comp (continuous_snd.prodMk hYc)).smul hb.1
  have hfd : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      f (torusQuotient p.1,p.2)) :=
    (hv.comp (contDiff_snd.prodMk hY)).smul hb.2
  have hsm := isSmoothPeriodic_preparationMaskedIntegral (fun _ ↦ 1) measurable_const
    (by simp) (by simp) f hfc hfd hχc (by
      intro x z hz
      simp [f, image_eq_zero_of_notMem_tsupport hz])
  have heq : measuredIncrement d (fun z ↦ χ z ^ 2) v =
      fun x ↦ ∫ z, (1 : ℝ) • f (x,z) ∂(volume.prod volume) := by
    funext x
    classical
    by_cases hx : x ∈ d.outputChart
    · simp only [measuredIncrement, Set.indicator_of_mem hx, one_smul]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : χ z = 0
      · simp [f, hz]
      · have ht := measurement_densityTransportMatrix d 0 x z (by simp)
        simp only [Pi.zero_apply, add_zero, one_smul] at ht
        simp only [f, hfoot x hx z hz, hbase x hx z hz,
          preparationMeasurement, Set.indicator_of_mem hx,
          LinearMap.coe_toContinuousLinearMap', ht, smul_smul]
        rw [mul_comm]
    · simp [measuredIncrement, preparationMeasurement, f, hx]
  rw [heq]
  exact hsm

section FiniteFamily

variable {ι : Type*} [Fintype ι]
    (d : ι → CarrierData n N) (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (hY₀ : ∀ a x, ContinuousOn ((d a).transportedPosition ((d a).chartPoint x))
      (tsupport (χ a)))
    (hS₀ : ∀ a x, ContinuousOn (measuredStress (d a) x) (tsupport (χ a)))
    (K : ι → Set CarrierParameter)
    (Y : ι → Torus n × CarrierParameter → Euclidean (n - 1))
    (T : ι → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : ∀ a, Continuous (Y a)) (hTc : ∀ a, Continuous (T a))
    (hY : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y a (torusQuotient p.1,p.2)))
    (hT : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T a (torusQuotient p.1,p.2)))
    (hfoot : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      Y a (x,z) = (d a).transportedPosition ((d a).chartPoint x) z)
    (hbase : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      T a (x,z) = densityTransportMatrix (d a) 0 x z)

/-- The original finite transport map takes smooth supported densities to
smooth complete-output sources (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def smoothPreparationTransport : smoothSupportedDensity n ι K →ₗ[ℝ] SmoothResidual n where
  toFun v := ⟨fun x _ ↦ finitePreparationTransport d χ
    (fun a ↦ (hχ a).continuous) hχc hY₀ hS₀ K v x, fun _ ↦ by
      have h (a : ι) := isSmoothPeriodic_measuredIncrement_of_extensions
        (d a) (hC a) (χ a) (hχ a) (hχc a) (Y a) (T a)
        (hYc a) (hTc a) (hY a) (hT a) (hfoot a) (hbase a) (v.val a) (v.property a).1
      refine ⟨?_, ?_⟩
      · simpa only [finitePreparationTransport, LinearMap.sum_apply,
          preparationTransportLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
          using continuous_finsetSum Finset.univ (fun a _ ↦ (h a).1)
      · simpa only [periodicLift, Function.comp_def, finitePreparationTransport,
          LinearMap.sum_apply, preparationTransportLinear, LinearMap.coe_mk,
          AddHom.coe_mk, Finset.sum_apply] using
          ContDiff.sum (s := Finset.univ) (fun a _ ↦ (h a).2)⟩
  map_add' v w := by
    apply Subtype.ext
    funext x u
    exact congrFun (map_add (finitePreparationTransport d χ
      (fun a ↦ (hχ a).continuous) hχc hY₀ hS₀ K) v w) x
  map_smul' b v := by
    apply Subtype.ext
    funext x u
    exact congrFun (map_smul (finitePreparationTransport d χ
      (fun a ↦ (hχ a).continuous) hχc hY₀ hS₀ K) b v) x

/-- Pointwise identification with the original transported density, before
passing to L² (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem smoothPreparationTransport_apply (v : smoothSupportedDensity n ι K) (x : Torus n) :
    (smoothPreparationTransport d hC χ hχ hχc hY₀ hS₀ K Y T hYc hTc hY hT
      hfoot hbase v).val x () =
        ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v.val a) x := by
  simp only [smoothPreparationTransport, finitePreparationTransport, LinearMap.sum_apply,
    preparationTransportLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]

/-- The smooth transport retains the original measurement-chart support
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem smoothPreparationTransport_supported (v : smoothSupportedDensity n ι K) :
    smoothPreparationTransport d hC χ hχ hχc hY₀ hS₀ K Y T hYc hTc hY hT hfoot hbase v ∈
      supportedSmoothResidual n (⋃ a, (d a).outputChart) := by
  intro x hx
  rw [smoothPreparationTransport_apply]
  apply Finset.sum_eq_zero
  intro a _
  have ha : x ∉ (d a).outputChart := fun ha ↦ hx (mem_iUnion.mpr ⟨a,ha⟩)
  simp [measuredIncrement, ha]

end FiniteFamily
end JanetCartan.CurrentMean
