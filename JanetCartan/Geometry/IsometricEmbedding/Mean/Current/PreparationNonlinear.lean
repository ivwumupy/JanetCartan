module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationTransport

/-!
# The literal nonlinear preparation map on smooth densities

For `app:ch_mean_pairs:eq:mean-density-lipschitz`, apply the original linear
current atoms to `r_F sqrt(1+v)` and use the same scalar in transport. The map
is extended by zero outside the positive class solely to use the existing
finite recurrence on a vector space. Every identification with the paper's
integrals is restricted to the positive class; its invariance must still be
proved by the quantitative backward-reserve induction.
-/

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow

variable {n N : ℕ}

/-- Modulating the SAME extended base transport matrix, before any sample
is chosen (`app:ch_mean_pairs:prop:mean-coarse`). -/
def preparedTransportExtension
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (v : CarrierVariable n → ℝ) (p : Torus n × CarrierParameter) :
    Matrix (Fin N) (Fin n) ℂ := Real.sqrt (1 + v (p.2,Y p)) • T p

/-- Exact agreement of the extended modulation with the original transport
matrix; the base normal already contains `r_F`
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparedTransportExtension_eq
    (d : CarrierData n N)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (v : CarrierVariable n → ℝ) (x : Torus n) (z : CarrierParameter)
    (hY : Y (x,z) = d.transportedPosition (d.chartPoint x) z)
    (hT : T (x,z) = densityTransportMatrix d 0 x z) :
    preparedTransportExtension Y T v (x,z) = densityTransportMatrix d v x z := by
  ext i j
  simp [preparedTransportExtension, hY, hT, densityTransportMatrix,
    LeadingWave.principalMatrix, mul_assoc]

/-- Joint regularity of the actual modulated transport matrix follows
from positivity and the primitive base/footpoint extensions
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparedTransportExtension_regular
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hYc : Continuous Y) (hTc : Continuous T)
    (hY : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      Y (torusQuotient p.1,p.2)))
    (hT : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T (torusQuotient p.1,p.2)))
    (v : CarrierVariable n → ℝ) (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ p, 0 < 1 + v p) :
    Continuous (preparedTransportExtension Y T v) ∧
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      preparedTransportExtension Y T v (torusQuotient p.1,p.2)) :=
  ⟨(continuous_const.add (hv.continuous.comp (continuous_snd.prodMk hYc))).sqrt.smul hTc,
    ((contDiff_const.add (hv.comp (contDiff_snd.prodMk hY))).sqrt
      (fun _ ↦ (hpos _).ne')).smul hT⟩

section FiniteFamily
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → CarrierData n N) (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (mask : ι → κ → CarrierParameter → ℝ)
    (hm : ∀ a c, Measurable (mask a c)) (hm₀ : ∀ a c z, 0 ≤ mask a c z)
    (hmask : ∀ a z, ∑ c, mask a c z = 1)
    (current : ι → κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
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
    (U : ι → κ → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ))
    (hUc : ∀ a c u, ContDiff ℝ ∞ u → Continuous (U a c u))
    (hU : ∀ a c u, ContDiff ℝ ∞ u →
      ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
        U a c u (torusQuotient p.1,p.2)))
    (hcurrent : ∀ a c u x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      U a c u (x,z) = current a c z u x)
    (r : ι → CarrierVariable n → ℝ) (hr : ∀ a, ContDiff ℝ ∞ (r a))
    (K : ι → Set CarrierParameter)

include hC hχ hχc hm hm₀ hmask hYc hTc hY hT hfoot hbase hUc hU hcurrent hr in
/-- The SAME literal nonlinear discrepancy is smooth for every positive
smooth supported density. The input assumptions concern only the original
linear atom extensions and geometric transport data
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem isSmoothPeriodic_finitePreparationDiscrepancy_of_positive
    (v : smoothSupportedDensity n ι K) (hv : ∀ a p, 0 < 1 + v.val a p) :
    IsSmoothPeriodic (finitePreparationDiscrepancy d χ mask current r v.val) := by
  have hmod := contDiff_preparationAmplitude r v hr hv
  have htr (a : ι) := preparedTransportExtension_regular (Y a) (T a)
    (hYc a) (hTc a) (hY a) (hT a) (v.val a) (v.property a).1 (hv a)
  apply isSmoothPeriodic_finitePreparationDiscrepancy_of_extensions d hC χ hχ hχc
    mask hm hm₀ hmask current r v.val
    (fun a c ↦ U a c (preparationAmplitude r v.val a))
    (fun a ↦ preparedTransportExtension (Y a) (T a) (v.val a))
    (fun a c ↦ hUc a c _ (hmod a)) (fun a ↦ (htr a).1)
    (fun a c ↦ hU a c _ (hmod a)) (fun a ↦ (htr a).2)
  · intro a c x hx z hz
    exact hcurrent a c _ x hx z hz
  · intro a x hx z hz
    exact preparedTransportExtension_eq (d a) (Y a) (T a) (v.val a) x z
      (hfoot a x hx z hz) (hbase a x hx z hz)

/-- The nonlinear map used by the existing finite preparation run. On its
positive class it is literally the original colored discrepancy; elsewhere
zero is merely a total extension, never used to claim a prepared solution
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def smoothPreparationDiscrepancy (v : smoothSupportedDensity n ι K) : SmoothResidual n := by
  classical
  exact if hv : ∀ a p, 0 < 1 + v.val a p then
    ⟨fun x _ ↦ finitePreparationDiscrepancy d χ mask current r v.val x,
      fun _ ↦ isSmoothPeriodic_finitePreparationDiscrepancy_of_positive d hC χ hχ hχc
        mask hm hm₀ hmask current Y T hYc hTc hY hT hfoot hbase U hUc hU hcurrent
        r hr K v hv⟩
  else 0

/-- Pointwise equality with the literal colored discrepancy on the class
preserved by the finite-reserve bounds
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem smoothPreparationDiscrepancy_apply
    (v : smoothSupportedDensity n ι K) (hv : ∀ a p, 0 < 1 + v.val a p) (x : Torus n) :
    (smoothPreparationDiscrepancy d hC χ hχ hχc mask hm hm₀ hmask current Y T
      hYc hTc hY hT hfoot hbase U hUc hU hcurrent r hr K v).val x () =
        finitePreparationDiscrepancy d χ mask current r v.val x := by
  simp [smoothPreparationDiscrepancy, hv]

/-- No source cutoff is inserted by the nonlinear map: on its domain it
has precisely the original measurement-chart support
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem smoothPreparationDiscrepancy_supported (v : smoothSupportedDensity n ι K) :
    smoothPreparationDiscrepancy d hC χ hχ hχc mask hm hm₀ hmask current Y T
      hYc hTc hY hT hfoot hbase U hUc hU hcurrent r hr K v ∈
        supportedSmoothResidual n (⋃ a, (d a).outputChart) := by
  intro x hx
  by_cases hv : ∀ a p, 0 < 1 + v.val a p
  · rw [smoothPreparationDiscrepancy_apply d hC χ hχ hχc mask hm hm₀ hmask current
      Y T hYc hTc hY hT hfoot hbase U hUc hU hcurrent r hr K v hv]
    apply finitePreparationDiscrepancy_zero_off_chart
    intro a ha
    exact hx (mem_iUnion.mpr ⟨a,ha⟩)
  · simp only [smoothPreparationDiscrepancy, dite_eq_right hv]
    rfl


/-- The original current mean minus the original base transport is exactly
nonlinear discrepancy plus the linear density term. Joint extensions supply
all required integrability, even if the original current functions are only
specified on the measurement/carrier support
(`app:ch_mean_pairs:eq:mean-prepared-residual`). -/
theorem smoothPreparationDiscrepancy_add_transport
    (hY₀ : ∀ a x, ContinuousOn ((d a).transportedPosition ((d a).chartPoint x))
      (tsupport (χ a)))
    (hS₀ : ∀ a x, ContinuousOn (UncutDensity.measuredStress (d a) x) (tsupport (χ a)))
    (v : smoothSupportedDensity n ι K) (hv : ∀ a p, 0 < 1 + v.val a p) (x : Torus n) :
    (smoothPreparationDiscrepancy d hC χ hχ hχc mask hm hm₀ hmask current Y T
      hYc hTc hY hT hfoot hbase U hUc hU hcurrent r hr K v).val x () +
      (smoothPreparationTransport d hC χ hχ hχc hY₀ hS₀ K Y T hYc hTc hY hT
        hfoot hbase v).val x () =
      (∑ a, coloredPreparationCurrentMean (d a) (χ a) (mask a) (current a) (r a) (v.val a) x) -
        ∑ a, coloredTransportMean (d a) (χ a) (mask a) 0 x := by
  let current' := fun a c z ↦ LinearMap.pi fun x : Torus n ↦
    (LinearMap.proj (x,z)).comp (U a c)
  have heq (a : ι) :
      coloredPreparationDiscrepancy (d a) (χ a) (mask a) (current' a) (r a) (v.val a) =
        coloredPreparationDiscrepancy (d a) (χ a) (mask a) (current a) (r a) (v.val a) ∧
      coloredPreparationCurrentMean (d a) (χ a) (mask a) (current' a) (r a) (v.val a) =
        coloredPreparationCurrentMean (d a) (χ a) (mask a) (current a) (r a) (v.val a) := by
    constructor <;> funext x <;> classical
    all_goals
      by_cases hx : x ∈ (d a).outputChart
      · simp only [coloredPreparationDiscrepancy, coloredPreparationCurrentMean,
          Set.indicator_of_mem hx]
        apply integral_congr_ae
        filter_upwards [] with z
        apply Finset.sum_congr rfl
        intro c _
        by_cases hz : χ a z = 0
        · simp [hz]
        · simp only [current', LinearMap.pi_apply, LinearMap.comp_apply,
            LinearMap.proj_apply, hcurrent a c _ x hx z hz]
      · simp [coloredPreparationDiscrepancy, coloredPreparationCurrentMean, hx]
  have hcur (a : ι) (c : κ) (x : Torus n) :
      Continuous (fun z ↦ current' a c z (preparationAmplitude r v.val a) x) :=
    (hUc a c _ (contDiff_preparationAmplitude r v hr hv a)).comp
      (continuous_const.prodMk continuous_id)
  have hh := congrFun (finitePreparationDiscrepancy_add_transport d χ
    (fun a ↦ (hχ a).continuous) hχc hY₀ hS₀ mask hm hm₀ hmask current' r v
      (fun a p ↦ (hv a p).le) hcur) x
  simp only [finitePreparationDiscrepancy, (heq _).1, (heq _).2, Pi.add_apply,
    Pi.sub_apply, Finset.sum_apply] at hh
  rw [smoothPreparationDiscrepancy_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv]
  simpa only [finitePreparationDiscrepancy, Finset.sum_apply, smoothPreparationTransport,
    LinearMap.coe_mk, AddHom.coe_mk] using hh

end FiniteFamily
end JanetCartan.CurrentMean
