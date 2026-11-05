module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.Distribution

/-!
# Weak derivative identities for the literal full integral

For `app:ch_regular_base:eq:graph-derivative-transfer` and
`app:ch_regular_base:eq:fio-input`, primitive finite budgets identify the strong
L² limit with the source-first full integral. No output integrability is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology
open JanetCartan.AmplitudeBound
open LineDeriv

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:fio-input`: the literal output belongs to L² on
compact smooth data, solely from the finite primitive physical budget. -/
theorem memLp_fullAmplitudeOperator_of_physicalBudget
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    MemLp (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u) 2 :=
  (Lp.memLp _).ae_eq
    (twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget hd R b hb hs A hA
      u (hu.continuous.memLp_of_hasCompactSupport hus) (hu.of_le (by simp)) hus)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: frequency exhaustion
converges to the Schwartz pairing with the literal full integral. The requisite
source integrability is discharged by the primitive physical budget. -/
theorem tendsto_pairing_compactFrequencyAmplitudeKernel_fullAmplitudeOperator
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (φ : 𝓢(E, ℂ)) :
    Tendsto (fun ρ : ℝ ↦ ∫ x, φ x *
      (∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y)) atTop
      (𝓝 (∫ x, φ x * fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x)) := by
  let hu₂ : MemLp u 2 := hu.continuous.memLp_of_hasCompactSupport hus
  have he := twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget
    hd R b hb hs A hA u hu₂ (hu.of_le (by simp)) hus
  have hp : ((twoPositionL2Operator hd R b hb hs A hA (hu₂.toLp u) : 𝓢'(E, ℂ)) φ) =
      ∫ x, φ x * fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x :=
    (Lp.toTemperedDistribution_apply _ φ).trans
      (integral_congr_ae (he.mono (fun x hx ↦ congrArg (fun z ↦ φ x * z) hx)))
  rw [← hp]
  exact tendsto_pairing_compactFrequencyAmplitudeKernel hd R b hb hs A hA u hu₂ φ

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the single-coordinate
weak derivative identity for the actual source-first full operator. The
transferred operator and the differentiated datum retain all original masks.
The finite budget is on the original amplitude alone. -/
theorem fullAmplitudeOperator_weak_transfer
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) A)
    (i : Fin d) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : 𝓢(E, ℂ)) :
    (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) *
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x) =
      -(∫ x, φ x *
        (fullAmplitudeOperator (fun x y ξ ↦ transferAmplitude b i ξ (pairedPosition x y)) u x +
          fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
            (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x)) := by
  let hbase := amplitudeDerivativeBound_of_le hA (Nat.le_succ (2 * (d + 1)))
  let ht := hasAmplitudeDerivativeBound_transferAmplitude b
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i (2 * (d + 1)) A hA
  have hdu : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hdus := hus.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have ht₂ := memLp_fullAmplitudeOperator_of_physicalBudget hd R (transferAmplitude b i)
    (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A) ht u hu hus
  have hd₂ := memLp_fullAmplitudeOperator_of_physicalBudget hd R b hb hs A hbase _ hdu hdus
  simp_rw [mul_add]
  rw [integral_add (μ := (volume : Measure E))
    (f := fun x ↦ φ x * fullAmplitudeOperator
      (fun x y ξ ↦ transferAmplitude b i ξ (pairedPosition x y)) u x)
    (g := fun x ↦ φ x * fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
      (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x)
    ((φ.memLp 2).integrable_mul ht₂) ((φ.memLp 2).integrable_mul hd₂)]
  have hleft := tendsto_pairing_compactFrequencyAmplitudeKernel_fullAmplitudeOperator
    hd R b hb hs A hbase u hu hus (lineDerivOp (EuclideanSpace.single i 1 : E) φ)
  have hright := (tendsto_pairing_compactFrequencyAmplitudeKernel_fullAmplitudeOperator
    hd R (transferAmplitude b i) (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A) ht u hu hus φ).add
      (tendsto_pairing_compactFrequencyAmplitudeKernel_fullAmplitudeOperator
        hd R b hb hs A hbase _ hdu hdus φ)
  have heq := tendsto_nhds_unique hleft (hright.neg.congr (fun ρ ↦ by
    simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [compactFrequencyAmplitudeKernel_weak_transfer hb hs ρ i hu hus φ]
    simp_rw [mul_add]
    rw [integral_add
      (integrable_schwartz_mul_compactFrequencyAmplitudeKernel hd R (transferAmplitude b i)
        (contDiff_uncurry_transferAmplitude hb i)
        (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A) ht ρ u
        (hu.continuous.memLp_of_hasCompactSupport hus) φ)
      (integrable_schwartz_mul_compactFrequencyAmplitudeKernel hd R b hb hs A hbase
        ρ _ (hdu.continuous.memLp_of_hasCompactSupport hdus) φ)]))
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using heq

/-- `app:ch_regular_base:eq:fio-input`: for an order-minus-one amplitude,
the weak output derivative is the literal operator with output-derivative
amplitude. The weighted primitive budget proves its L² realization and source
integrability before the frequency limit is taken. -/
theorem fullAmplitudeOperator_weak_outputDerivativeAmplitude
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A)
    (i : Fin d) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : 𝓢(E, ℂ)) :
    (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) *
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x) =
      -(∫ x, φ x * fullAmplitudeOperator
        (fun x y ξ ↦ outputDerivativeAmplitude b i ξ (pairedPosition x y)) u x) := by
  let hbase := amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
    (Nat.le_succ (2 * (d + 1)))
  let ho := hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i (2 * (d + 1)) A hA
  have hleft := tendsto_pairing_compactFrequencyAmplitudeKernel_fullAmplitudeOperator
    hd R b hb hs A hbase u hu hus (lineDerivOp (EuclideanSpace.single i 1 : E) φ)
  have hright := tendsto_pairing_compactFrequencyAmplitudeKernel_fullAmplitudeOperator
    hd R (outputDerivativeAmplitude b i) (contDiff_uncurry_outputDerivativeAmplitude hb i)
    (supportedInCenteredBox_outputDerivativeAmplitude b R hs i) ((1 + 2 * Real.pi) * A)
    ho u hu hus φ
  have heq := tendsto_nhds_unique hleft (hright.neg.congr (fun ρ ↦ by
    simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact (compactFrequencyAmplitudeKernel_weak_outputDerivative hb hs ρ i hu.continuous φ).symm))
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using heq

end JanetCartan.Pseudodifferential
