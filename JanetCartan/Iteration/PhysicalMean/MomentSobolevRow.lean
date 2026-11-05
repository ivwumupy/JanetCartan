module

public import JanetCartan.Iteration.PhysicalMean.MomentRows
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Kernel

/-!
# The sharp Sobolev amplitude test on the original active sampled mask

This is the `H^ell`, rather than `C^ell`, form needed for the source-dependent
modified row in `app:ch_mean_pairs:eq:mean-quadratic-low`. The original native
measure, phase, complete mask, and scalar common-event tester are unchanged.
No physical derivative of the inactive-input indicator is taken.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open Pseudodifferential AmplitudeBound AmplitudeBound.PaperEstimates
open ContinuumAdjoint.DerivativeKernels CompactCarrierKernel

variable {n : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- Apply the sharp original scalar amplitude theorem to the literal sampled
row, needing Fourier `H^ell` only on its ORIGINAL active input mask. The forward
coefficient is `star (a u)`, in agreement with `sampledMomentKernel`; for the
modified cross row it is the actual component of `complexCrossMeasurement`.
Its Sobolev budget is produced by `exists_crossAmplitude_component_fourierSobolev_bound`,
not by bounding the source-dependent field in `C^ell`. -/
theorem norm_sampledMomentOperator_le_scalarTest_of_sobolev_onMask
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : X → Euclidean n → ℝ) (m : X → ℝ) (a : X → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m)
    (ha : Continuous (Function.uncurry a)) (hms : HasCompactSupport m)
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ u, tsupport (a u) ⊆ K)
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1)
    (R : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ R)
    (A : ℝ) (hA : 0 ≤ A)
    (hSob : ∀ u, m u ≠ 0 → ∃ hf : MemLp (fun x ↦ star (a u x)) 2 volume,
      MemFourierSobolev (n / 2 + 1 : ℕ) (hf.toLp (fun x ↦ star (a u x))) ∧
        fourierSobolevNorm (n / 2 + 1 : ℕ) (hf.toLp (fun x ↦ star (a u x))) ≤ A)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ) :
    ‖sampledMomentOperator μ φ m a hφ hm ha hms hK has‖ ≤
      rowAmplitudeConstant n R * ‖T‖ * A := by
  classical
  let b := fun u x ↦ if m u = 0 then (0 : ℂ) else star (a u x)
  have hbm : StronglyMeasurable (Function.uncurry b) :=
    StronglyMeasurable.ite
      (measurableSet_eq_fun (hm.measurable.comp measurable_fst) measurable_const)
      stronglyMeasurable_const ha.star.stronglyMeasurable
  have hbc (u) : Continuous (b u) := by
    by_cases hu : m u = 0
    · simp only [b, ite_eq_left hu]
      exact continuous_const
    · simp only [b, ite_eq_right hu]
      exact (ha.comp (continuous_const.prodMk continuous_id)).star
  have hbb (u) : SupportedInCenteredBox R (b u) := by
    intro x hx
    by_cases hu : m u = 0
    · exact False.elim (hx (by simp only [b, ite_eq_left hu]))
    · apply hbox x
      apply has u
      apply subset_tsupport
      intro hz
      exact hx (by simp only [b, ite_eq_right hu, hz, star_zero])
  have hbLp (u) : MemLp (b u) 2 volume := by
    by_cases hu : m u = 0
    · simpa only [b, ite_eq_left hu, Pi.zero_def] using
        (MemLp.zero : MemLp (0 : Euclidean n → ℂ) 2 volume)
    · simpa only [b, ite_eq_right hu] using (hSob u hu).choose
  have hz : weightedL2Fourier (n / 2 + 1 : ℕ)
      (0 : Lp ℂ 2 (volume : Measure (Euclidean n))) =ᵐ[volume] 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean n))] with x hx
    simp only [weightedL2Fourier, FourierTransform.fourier_zero, hx, smul_zero, Pi.zero_apply]
  have hzmem : MemFourierSobolev (n / 2 + 1 : ℕ)
      (0 : Lp ℂ 2 (volume : Measure (Euclidean n))) :=
    (memLp_congr_ae hz).mpr MemLp.zero
  have hznorm : fourierSobolevNorm (n / 2 + 1 : ℕ)
      (0 : Lp ℂ 2 (volume : Measure (Euclidean n))) = 0 := by
    rw [fourierSobolevNorm, eLpNorm_congr_ae hz]
    simp
  have hbHs (u) : MemFourierSobolev (n / 2 + 1 : ℕ) ((hbLp u).toLp (b u)) := by
    by_cases hu : m u = 0
    · simpa only [b, ite_eq_left hu, ← Pi.zero_def, MemLp.toLp_zero] using hzmem
    · simpa only [b, ite_eq_right hu] using (hSob u hu).choose_spec.1
  have hbNorm (u) : fourierSobolevNorm (n / 2 + 1 : ℕ) ((hbLp u).toLp (b u)) ≤ A := by
    by_cases hu : m u = 0
    · simpa only [b, ite_eq_left hu, ← Pi.zero_def, MemLp.toLp_zero] using hznorm.le.trans hA
    · simpa only [b, ite_eq_right hu] using (hSob u hu).choose_spec.2
  apply norm_integralRowAmplitudeOperator_le R b hbm hbc hbb hbLp hbHs A hA hbNorm T
    (sampledMomentOperator μ φ m a hφ hm ha hms hK has)
    (sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)))
  · intro f
    exact Filter.Eventually.of_forall (fun x ↦ integrable_compactKernel_mul_L2
      (continuous_sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) hφ hm
        (Complex.continuous_ofReal.comp (hχ.comp continuous_snd)))
      (hasCompactSupport_sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) hms hχs
        (fun _ ↦ by
          apply closure_mono
          intro y hy
          exact fun hz ↦ hy (by change (χ y : ℂ) = 0; rw [hz, Complex.ofReal_zero]))) f x)
  · exact hT
  · intro f
    filter_upwards [sampledMomentOperator_ae_kernel μ φ m a hφ hm ha hms hK has f] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : m u = 0
    · simp only [b, ite_eq_left hu, sampledMomentKernel, hu, Complex.ofReal_zero, zero_mul]
    · by_cases ha₀ : a u x = 0
      · simp only [b, ite_eq_right hu, sampledMomentKernel, ha₀, star_zero, mul_zero, zero_mul]
      · have hcut : χ x = 1 := hχK x (has u (subset_tsupport (a u) ha₀))
        simp only [b, ite_eq_right hu, sampledMomentKernel, hcut, Complex.ofReal_one, star_one, mul_one]
        ring

end JanetCartan.PhysicalMean
