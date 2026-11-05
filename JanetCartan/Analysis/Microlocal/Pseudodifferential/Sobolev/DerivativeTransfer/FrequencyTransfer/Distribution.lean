module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.Limits

/-!
# Distributional derivative transfer for the bounded realization

The compact-frequency identities for
`app:ch_regular_base:eq:graph-derivative-transfer` pass through the existing
strong frequency limit. Only primitive physical derivative budgets are used.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology
open JanetCartan.AmplitudeBound
open LineDeriv

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Restriction of the finite primitive budget in
`app:ch_regular_base:eq:graph-derivative-transfer` to fewer derivatives. -/
theorem amplitudeDerivativeBound_of_le
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {N M : ℕ} {A : ℝ}
    (h : HasAmplitudeDerivativeBound b N A) (hMN : M ≤ N) :
    HasAmplitudeDerivativeBound b M A :=
  fun ξ is his z ↦ h ξ is (his.trans hMN) z

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: one output coordinate
derivative of the actual bounded realization is the transferred full amplitude
plus the original full amplitude on the differentiated compact smooth datum. -/
theorem twoPositionL2Operator_lineDeriv_transfer
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) A)
    (i : Fin d) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let hu₂ : MemLp u 2 := hu.continuous.memLp_of_hasCompactSupport hus
    let hdu₂ : MemLp (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) 2 :=
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hus.fderiv_apply ℝ (EuclideanSpace.single i 1))
    lineDerivOp (EuclideanSpace.single i 1 : E)
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_succ _)) (hu₂.toLp u) : 𝓢'(E, ℂ)) =
      (twoPositionL2Operator hd R (transferAmplitude b i)
        (contDiff_uncurry_transferAmplitude hb i)
        (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A)
        (hasAmplitudeDerivativeBound_transferAmplitude b
          (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ A hA)
        (hu₂.toLp u) : 𝓢'(E, ℂ)) +
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_succ _))
        (hdu₂.toLp _) : 𝓢'(E, ℂ)) := by
  dsimp only
  let hu₂ : MemLp u 2 := hu.continuous.memLp_of_hasCompactSupport hus
  let hdu₂ : MemLp (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) 2 :=
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hus.fderiv_apply ℝ (EuclideanSpace.single i 1))
  let hbase := amplitudeDerivativeBound_of_le hA (Nat.le_succ (2 * (d + 1)))
  let ht := hasAmplitudeDerivativeBound_transferAmplitude b
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i (2 * (d + 1)) A hA
  ext φ
  have hleft := tendsto_pairing_compactFrequencyAmplitudeKernel hd R b hb hs A hbase
    u hu₂ (lineDerivOp (EuclideanSpace.single i 1 : E) φ)
  have hright := (tendsto_pairing_compactFrequencyAmplitudeKernel hd R (transferAmplitude b i)
    (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A) ht u hu₂ φ).add
      (tendsto_pairing_compactFrequencyAmplitudeKernel hd R b hb hs A hbase _ hdu₂ φ)
  have heq := tendsto_nhds_unique hleft (hright.neg.congr (fun ρ ↦ by
    simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [compactFrequencyAmplitudeKernel_weak_transfer hb hs ρ i hu hus φ]
    simp_rw [mul_add]
    rw [integral_add
      (integrable_schwartz_mul_compactFrequencyAmplitudeKernel hd R (transferAmplitude b i)
        (contDiff_uncurry_transferAmplitude hb i)
        (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A) ht ρ u hu₂ φ)
      (integrable_schwartz_mul_compactFrequencyAmplitudeKernel hd R b hb hs A hbase
        ρ _ hdu₂ φ)]))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  exact neg_eq_iff_eq_neg.mpr heq

/-- `app:ch_regular_base:eq:fio-input`: forgetting the order-minus-one weight
provides the unweighted primitive budget for the original amplitude. -/
theorem amplitudeDerivativeBound_of_weighted
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {N : ℕ} {A : ℝ}
    (hA : ∀ ξ is, is.length ≤ N → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A) :
    HasAmplitudeDerivativeBound b N A := by
  intro ξ is his z
  have h := hA ξ is his z
  nlinarith [norm_nonneg ξ, norm_nonneg (euclideanCoordinateDerivList is (b ξ) z)]

/-- `app:ch_regular_base:eq:fio-input`: the first distributional derivative
of the order-minus-one realization is the realization of its output-derivative
amplitude. Both L² budgets are derived from the original weighted primitive budget. -/
theorem twoPositionL2Operator_lineDeriv_outputDerivativeAmplitude
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A)
    (i : Fin d) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let hu₂ : MemLp u 2 := hu.continuous.memLp_of_hasCompactSupport hus
    lineDerivOp (EuclideanSpace.single i 1 : E)
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
          (Nat.le_succ _)) (hu₂.toLp u) : 𝓢'(E, ℂ)) =
      (twoPositionL2Operator hd R (outputDerivativeAmplitude b i)
        (contDiff_uncurry_outputDerivativeAmplitude hb i)
        (supportedInCenteredBox_outputDerivativeAmplitude b R hs i) ((1 + 2 * Real.pi) * A)
        (hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
          (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ A hA)
        (hu₂.toLp u) : 𝓢'(E, ℂ)) := by
  dsimp only
  let hu₂ : MemLp u 2 := hu.continuous.memLp_of_hasCompactSupport hus
  let hbase := amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
    (Nat.le_succ (2 * (d + 1)))
  let ho := hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i (2 * (d + 1)) A hA
  ext φ
  have hleft := tendsto_pairing_compactFrequencyAmplitudeKernel hd R b hb hs A hbase
    u hu₂ (lineDerivOp (EuclideanSpace.single i 1 : E) φ)
  have hright := tendsto_pairing_compactFrequencyAmplitudeKernel hd R (outputDerivativeAmplitude b i)
    (contDiff_uncurry_outputDerivativeAmplitude hb i)
    (supportedInCenteredBox_outputDerivativeAmplitude b R hs i) ((1 + 2 * Real.pi) * A)
    ho u hu₂ φ
  have heq := tendsto_nhds_unique hleft (hright.neg.congr (fun ρ ↦ by
    simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact (compactFrequencyAmplitudeKernel_weak_outputDerivative hb hs ρ i hu.continuous φ).symm))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  exact neg_eq_iff_eq_neg.mpr heq

end JanetCartan.Pseudodifferential
