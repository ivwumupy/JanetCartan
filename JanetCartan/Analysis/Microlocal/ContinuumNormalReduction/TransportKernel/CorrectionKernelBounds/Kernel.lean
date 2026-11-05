module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.CorrectionKernelBounds.Integration
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.CorrectionKernelBounds.Integrand

/-! # Literal compact frequency kernels
Quantitative bounds for the smoothing error after `app:ch_background:eq:bg-symbol`.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n : ℕ}

/-- The literal physical-frequency integrand, with both positions retained
(`app:ch_background:eq:bg-symbol`). -/
def correctionIntegrand
    (f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (p : (Euclidean n × Euclidean n) × Euclidean n) : ℂ :=
  NormalComparison.oscillatoryFactor 1 (inner ℝ (p.1.1 - p.1.2) p.2) *
    (f (p.1.1, p.1.2, p.2) i j : ℂ)

/-- Joint smoothness supplies compact-frequency domination for the correction
(`app:ch_background:eq:bg-symbol`). -/
theorem correctionIntegrand_contDiff
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) (i j : Fin n) : ContDiff ℝ ∞ (correctionIntegrand f i j) := by
  have hp : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (p.1.1 - p.1.2) p.2)) := by
    unfold NormalComparison.oscillatoryFactor
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd)))).cexp
  exact hp.mul (Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp hf).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))))

private theorem correctionIntegrand_jet_zero
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ} {R : ℝ}
    (hs : ∀ p, R < ‖p.2.2‖ → f p = 0)
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n) {k : Euclidean n}
    (hk : k ∉ Metric.closedBall 0 R) :
    iteratedFDeriv ℝ r (fun y ↦ correctionIntegrand f i j (y, k)) x = 0 := by
  have he : (fun y ↦ correctionIntegrand f i j (y, k)) = fun _ ↦ (0 : ℂ) := by
    funext y
    simp [correctionIntegrand, hs (y.1, y.2, k) (by simpa using hk)]
  rw [he]
  simp

/-- Every physical jet is absolutely integrable against the literal Lebesgue
frequency measure (`app:ch_background:eq:bg-symbol`). -/
theorem integrable_correctionIntegrand_jet
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hs : ∀ p, R < ‖p.2.2‖ → f p = 0)
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n) :
    Integrable (fun k ↦ iteratedFDeriv ℝ r (fun y ↦ correctionIntegrand f i j (y, k)) x) := by
  apply ((contDiff_frequencyJet r (correctionIntegrand_contDiff hf i j)).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun k hk ↦ correctionIntegrand_jet_zero hs i j r x hk)

/-- Differentiation under the full Lebesgue frequency integral, justified by
its fixed compact support (`app:ch_background:eq:bg-symbol`). -/
theorem iteratedFDeriv_correctionIntegral
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hs : ∀ p, R < ‖p.2.2‖ → f p = 0)
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n) :
    iteratedFDeriv ℝ r (fun y ↦ ∫ k, correctionIntegrand f i j (y, k)) x =
      ∫ k, iteratedFDeriv ℝ r (fun y ↦ correctionIntegrand f i j (y, k)) x := by
  have he (y : Euclidean n × Euclidean n) :
      (∫ k in Metric.closedBall 0 R, correctionIntegrand f i j (y, k)) =
      ∫ k, correctionIntegrand f i j (y, k) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro k hk
    simp [correctionIntegrand, hs (y.1, y.2, k) (by simpa using hk)]
  simp_rw [← he]
  rw [iteratedFDeriv_frequencyIntegral (isCompact_closedBall 0 R) r
    (correctionIntegrand_contDiff hf i j)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun k hk ↦ correctionIntegrand_jet_zero hs i j r x hk)

/-- Smoothness of the full frequency integral follows from compact support,
including at zero frequency (`app:ch_background:eq:bg-symbol`). -/
theorem correctionIntegral_contDiff
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hs : ∀ p, R < ‖p.2.2‖ → f p = 0)
    (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Euclidean n × Euclidean n ↦
      ∫ k, correctionIntegrand f i j (y, k)) := by
  have hK := isCompact_closedBall (0 : Euclidean n) R
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean n) R)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have h := contDiffOn_univ.mp (contDiffOn_compactParameterIntegral
    (μ := (volume : Measure (Euclidean n))) isOpen_univ isOpen_univ hK
    (subset_univ _) (correctionIntegrand_contDiff hf i j).contDiffOn)
  convert h using 1
  funext y
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro k hk
  simp [correctionIntegrand, hs (y.1, y.2, k) (by simpa using hk)]

/-- Exact differentiation of the normalized literal integral. Both the
Lebesgue measure and the PDO prefactor are retained
(`app:ch_background:eq:bg-symbol`). -/
theorem iteratedFDeriv_normalizedCorrectionIntegral
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hs : ∀ p, R < ‖p.2.2‖ → f p = 0)
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n) :
    iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k, correctionIntegrand f i j (y, k)) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ k, iteratedFDeriv ℝ r (fun y ↦ correctionIntegrand f i j (y, k)) x := by
  change iteratedFDeriv ℝ r (fun y ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ k, correctionIntegrand f i j (y, k)) x = _
  rw [iteratedFDeriv_const_smul_apply'
    ((correctionIntegral_contDiff hf hs i j).contDiffAt.of_le (by simp)),
    iteratedFDeriv_correctionIntegral hf hs]

/-- The normalized kernel constant depends only on dimension, finite order,
and the fixed frequency radius (`app:ch_background:eq:bg-symbol`). -/
def correctionKernelJetConstant (n r : ℕ) (R : ℝ) : ℝ :=
  ‖((2 * Real.pi) ^ n : ℂ)⁻¹‖ *
    (correctionIntegrandJetConstant r R * volume.real (Metric.closedBall (0 : Euclidean n) R))

/-- Quantitative physical jets of the normalized literal kernel. The amplitude
bound enters once, preserving the producer's single high norm and fixed shift
(`app:ch_background:eq:bg-symbol`). -/
theorem norm_iteratedFDeriv_compactCorrectionKernel_le
    {f : TransportSymbol.Variables n → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ ∞ f) {R A : ℝ} (hs : ∀ p, R < ‖p.2.2‖ → f p = 0)
    (i j : Fin n) (r : ℕ) (x : Euclidean n × Euclidean n)
    (hb : ∀ k, ‖k‖ ≤ R → ∀ l ≤ r, ‖iteratedFDeriv ℝ l f (x.1, x.2, k)‖ ≤ A) :
    ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k, correctionIntegrand f i j (y, k)) x‖ ≤
      correctionKernelJetConstant n r R * A := by
  have he (y : Euclidean n × Euclidean n) :
      (∫ k in Metric.closedBall 0 R, correctionIntegrand f i j (y, k)) =
      ∫ k, correctionIntegrand f i j (y, k) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro k hk
    simp [correctionIntegrand, hs (y.1, y.2, k) (by simpa using hk)]
  have hK := isCompact_closedBall (0 : Euclidean n) R
  have hc := correctionIntegral_contDiff hf hs i j
  change ‖iteratedFDeriv ℝ r (fun y ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ k, correctionIntegrand f i j (y, k)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hc.contDiffAt.of_le (by simp)), norm_smul]
  have hb' : ‖iteratedFDeriv ℝ r (fun y ↦ ∫ k, correctionIntegrand f i j (y, k)) x‖ ≤
      (correctionIntegrandJetConstant r R * A) * volume.real (Metric.closedBall (0 : Euclidean n) R) := by
    simp_rw [← he]
    rw [iteratedFDeriv_frequencyIntegral hK r (correctionIntegrand_contDiff hf i j)]
    apply norm_setIntegral_le_of_norm_le_const_ae' hK.measure_lt_top
    filter_upwards [] with k hk
    have hk' : ‖k‖ ≤ R := by simpa using hk
    exact norm_iteratedFDeriv_correctionIntegrand_le hf hk' r x (hb k hk') i j
  calc
    _ ≤ ‖((2 * Real.pi) ^ n : ℂ)⁻¹‖ *
        ((correctionIntegrandJetConstant r R * A) * volume.real (Metric.closedBall (0 : Euclidean n) R)) :=
      mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
    _ = _ := by unfold correctionKernelJetConstant; ring

end JanetCartan.ContinuumRow.TransportKernel
