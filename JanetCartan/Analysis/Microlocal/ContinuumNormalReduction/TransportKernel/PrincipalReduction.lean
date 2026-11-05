module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.TestCompletion
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.CorrectionKernelBounds.Kernel

/-!
# Completion of the diagonal principal term

For `app:ch_background:eq:bg-real-symbol`, diagonalize the original reflected
amplitude, then complete its diagonal. This retains precisely the Taylor
remainder bounded in `TransportKernel.RemainderBounds`. The extra term is the
literal compact-frequency kernel of the diagonal discrepancy, with Euclidean
Lebesgue measure and the explicit `(2π)⁻ⁿ` normalization.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius ComplexConjugate
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

section Completion
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))

/-- The completion discrepancy in the Fourier convention `k = 2πξ`
(`app:ch_background:eq:bg-symbol`). -/
def unitDiagonalCompletionErrorEntry (i j : Fin n) (x _y ξ : Euclidean n) : ℂ :=
  reflectedCompletionError a J u Ω K (x, x, (2 * Real.pi) • ξ) i j

/-- The completed reflected amplitude in the same Fourier convention
(`app:ch_background:eq:bg-real-symbol`). -/
def unitCompletedPrincipalEntry (i j : Fin n) (x _y ξ : Euclidean n) : ℂ :=
  completedReflectedAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j

/-- The bounded-frequency correction to the diagonal principal symbol. The phase
retains both physical positions; only the amplitude is evaluated on the diagonal
(`app:ch_background:eq:bg-symbol`). -/
def diagonalCompletionErrorKernel (i j : Fin n) (x y : Euclidean n) : ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k,
    NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
      (reflectedCompletionError a J u Ω K (x, x, k) i j : ℂ)

/-- The diagonal correction retains the checked physical-frequency normalization
(`app:ch_background:eq:bg-symbol`). -/
theorem diagonalCompletionErrorKernel_eq_amplitudeKernel (i j : Fin n)
    (x y : Euclidean n) :
    diagonalCompletionErrorKernel a J u Ω K i j x y =
      amplitudeKernel (unitDiagonalCompletionErrorEntry a J u Ω K i j) x y := by
  exact (amplitudeKernel_eq_physicalFrequency_integral (fun x _y k ↦
    (reflectedCompletionError a J u Ω K (x, x, k) i j : ℂ)) x y).symm

/-- The completed principal term in the exact reduction is the fixed smooth
cutoff times `2 (2π)^n (d₀(x,k)+d₀(x,-k))`, evaluated at `k = 2πξ`.
No evenness of the angular mask is assumed (`app:ch_background:eq:bg-real-symbol`). -/
theorem unitCompletedPrincipalEntry_eq_reflectedDiagonal (i j : Fin n)
    (x y ξ : Euclidean n) :
    unitCompletedPrincipalEntry a J u Ω K i j x y ξ =
      (TransportSymbol.completionCutoff ((2 * Real.pi) • ξ) *
        reflectedDiagonalMatrix (TransportSymbol.homogeneousDiagonal a J u Ω K x)
          ((2 * Real.pi) • ξ) i j : ℝ) := by
  unfold unitCompletedPrincipalEntry
  rw [completedReflectedAmplitude_diagonal]
  rfl

/-- The principal matrix used in the source-tested decomposition has the
positive-semidefinite comparison of `app:ch_background:eq:bg-real-symbol`,
including its fixed completion at low frequency. The positive homogeneous
weight is supplied by the detector positivity lemmas in `SymbolBridge`. -/
theorem unitCompletedPrincipalEntry_posSemidef_comparison (x ξ : Euclidean n)
    (hpos : (TransportSymbol.homogeneousDiagonal a J u Ω K x
      (-((2 * Real.pi) • ξ))).PosSemidef) :
    (completedReflectedAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) -
      TransportSymbol.completionCutoff ((2 * Real.pi) • ξ) •
        ((2 * (2 * Real.pi) ^ n) • TransportSymbol.homogeneousDiagonal a J u Ω K x
          ((2 * Real.pi) • ξ))).PosSemidef :=
  completedReflectedAmplitude_diagonal_comparison a J u Ω K x _ hpos

variable (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hhigh : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)

include he hhigh hC hcomparison

/-- Joint absolute integrability of the actual completion discrepancy against
a compact continuous source test. Its frequency radius is divided by `2π`;
there is no unproved Fourier integrability premise for this term
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_unitDiagonalCompletionErrorEntry_test (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      f p.2 • unitDiagonalCompletionErrorEntry a J u Ω K i j x p.2 p.1) := by
  have hc : Continuous (fun p : Euclidean n × Euclidean n ↦
      unitDiagonalCompletionErrorEntry a J u Ω K i j x p.2 p.1) :=
    Complex.continuous_ofReal.comp (((realMatrixEntry i j).continuous.comp he.continuous).comp
      (continuous_const.prodMk (continuous_const.prodMk
        (continuous_fst.const_smul (2 * Real.pi)))))
  apply ((hf.comp continuous_snd).smul hc).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro
    ((isCompact_closedBall (0 : Euclidean n) (max 2 (2 * C) / (2 * Real.pi))).prod hfc.isCompact)
  intro p hp
  by_cases hξ : p.1 ∈ Metric.closedBall (0 : Euclidean n) (max 2 (2 * C) / (2 * Real.pi))
  · have hy : p.2 ∉ tsupport f := fun hy ↦ hp ⟨hξ, hy⟩
    simp [image_eq_zero_of_notMem_tsupport hy]
  · have hξ' : max 2 (2 * C) < ‖(2 * Real.pi) • p.1‖ := by
      have hp' : max 2 (2 * C) / (2 * Real.pi) < ‖p.1‖ := by simpa using hξ
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [(div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hp']
    simp [unitDiagonalCompletionErrorEntry, reflectedCompletionError_eq_zero_of_large_frequency
      a J u Ω K hhigh hC hcomparison (x, x, (2 * Real.pi) • p.1) hξ'.le]

/-- The correction's source Fourier transform is absolutely integrable by
Fubini and the unit modulus of the Fourier phase
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_sourceAmplitudeTransform_diagonalCompletionError (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Integrable (sourceAmplitudeTransform (unitDiagonalCompletionErrorEntry a J u Ω K i j) f x) := by
  have hi := integrable_unitDiagonalCompletionErrorEntry_test a J u Ω K he hhigh hC hcomparison
    i j f hf hfc x
  have hp : Continuous (fun p : Euclidean n × Euclidean n ↦
      Real.fourierChar (-inner ℝ p.2 p.1)) := by fun_prop
  have hphase : Integrable (fun p : Euclidean n × Euclidean n ↦
      Real.fourierChar (-inner ℝ p.2 p.1) •
        (f p.2 • unitDiagonalCompletionErrorEntry a J u Ω K i j x p.2 p.1)) := by
    apply hi.norm.mono' (hp.aestronglyMeasurable.smul hi.aestronglyMeasurable)
    filter_upwards [] with p
    exact le_of_eq (Circle.norm_smul _ _)
  unfold sourceAmplitudeTransform
  simpa only [Real.fourier_eq] using hphase.integral_prod_left

/-- Fubini identifies the source-tested discrepancy operator with the literal
normalized correction kernel. No separate kernel-action input is assumed
(`app:ch_background:eq:bg-symbol`). -/
theorem fullAmplitudeOperator_diagonalCompletionError_eq_kernel (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    fullAmplitudeOperator (unitDiagonalCompletionErrorEntry a J u Ω K i j) f x =
      ∫ y, f y * diagonalCompletionErrorKernel a J u Ω K i j x y := by
  rw [fullAmplitudeOperator_eq_integral_amplitudeKernel _ f x
    (integrable_unitDiagonalCompletionErrorEntry_test a J u Ω K he hhigh hC hcomparison
      i j f hf hfc x)]
  simp only [diagonalCompletionErrorKernel_eq_amplitudeKernel, smul_eq_mul]

/-- The correction kernel is absolutely integrable against the same tests;
this is the actual source integral occurring in the completed operator
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_diagonalCompletionErrorKernel_test (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Integrable (fun y ↦ f y * diagonalCompletionErrorKernel a J u Ω K i j x y) := by
  simp_rw [diagonalCompletionErrorKernel_eq_amplitudeKernel]
  exact integrable_amplitudeKernel_test (unitDiagonalCompletionErrorEntry a J u Ω K i j) f x
      (integrable_unitDiagonalCompletionErrorEntry_test a J u Ω K he hhigh hC hcomparison
        i j f hf hfc x)

omit hhigh hC hcomparison in
/-- Source integration respects the actual completion decomposition. Both
amplitudes are evaluated at the same `2πξ`, with no angular symmetry
assumption (`app:ch_background:eq:bg-real-symbol`). -/
theorem sourceAmplitudeTransform_diagonal_reflected_eq_completed_add_error
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x ξ : Euclidean n) :
    sourceAmplitudeTransform (fun x _y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j : ℂ)) f x ξ =
      sourceAmplitudeTransform (unitCompletedPrincipalEntry a J u Ω K i j) f x ξ +
      sourceAmplitudeTransform (unitDiagonalCompletionErrorEntry a J u Ω K i j) f x ξ := by
  have hid : (fun x _y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j : ℂ)) =
      (fun x y ξ ↦ unitCompletedPrincipalEntry a J u Ω K i j x y ξ +
        unitDiagonalCompletionErrorEntry a J u Ω K i j x y ξ) := by
    funext x y ξ
    simp [unitCompletedPrincipalEntry, unitDiagonalCompletionErrorEntry, reflectedCompletionError]
  rw [hid]
  apply sourceAmplitudeTransform_add_of_compactSupport _ _ f x ξ hf hfc
  · exact Complex.continuous_ofReal.comp (((realMatrixEntry i j).continuous.comp hc.continuous).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_const)))
  · exact Complex.continuous_ofReal.comp (((realMatrixEntry i j).continuous.comp he.continuous).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_const)))

/-- Completion preserves convergence of the source Fourier integral: the
original transform is the completed transform plus an integrable bounded-
frequency discrepancy. Thus no new convergence hypothesis is introduced
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_sourceAmplitudeTransform_completedPrincipal
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : Euclidean n)
    (hi : Integrable (sourceAmplitudeTransform (fun x _y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j : ℂ)) f x)) :
    Integrable (sourceAmplitudeTransform (unitCompletedPrincipalEntry a J u Ω K i j) f x) := by
  have hie := integrable_sourceAmplitudeTransform_diagonalCompletionError a J u Ω K he hhigh hC
    hcomparison i j f hf hfc x
  apply (hi.sub hie).congr
  filter_upwards [] with ξ
  dsimp only [Pi.sub_apply]
  rw [sourceAmplitudeTransform_diagonal_reflected_eq_completed_add_error a J u Ω K he hc
    i j f hf hfc x ξ, add_sub_cancel_right]

/-- Exact source-tested completion of the transport operator. The error is
its actual Lebesgue kernel, and its absolute integrability is proved above.
The only convergence premise is on the original unregularized source
transform; no bounded unregularized carrier is assumed
(`app:ch_background:eq:bg-symbol`, `app:ch_background:eq:bg-real-symbol`). -/
theorem fullAmplitudeOperator_diagonal_reflected_eq_completed_add_kernel
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : Euclidean n)
    (hi : Integrable (sourceAmplitudeTransform (fun x _y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j : ℂ)) f x)) :
    fullAmplitudeOperator (fun x _y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j : ℂ)) f x =
      fullAmplitudeOperator (unitCompletedPrincipalEntry a J u Ω K i j) f x +
        ∫ y, f y * diagonalCompletionErrorKernel a J u Ω K i j x y := by
  rw [← fullAmplitudeOperator_diagonalCompletionError_eq_kernel a J u Ω K he hhigh hC hcomparison
    i j f hf hfc x]
  have hic := integrable_sourceAmplitudeTransform_completedPrincipal a J u Ω K he hhigh hC hcomparison
    hc i j f hf hfc x hi
  have hie := integrable_sourceAmplitudeTransform_diagonalCompletionError a J u Ω K he hhigh hC
    hcomparison i j f hf hfc x
  have hinv {g : Euclidean n → ℂ} (hg : Integrable g) :
      Integrable (fun ξ ↦ Real.fourierChar (inner ℝ ξ x) • g ξ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr hg
  simp only [fullAmplitudeOperator, Real.fourierInv_eq]
  simp_rw [sourceAmplitudeTransform_diagonal_reflected_eq_completed_add_error a J u Ω K he hc
    i j f hf hfc x, smul_add]
  exact integral_add (hinv hic) (hinv hie)

/-- The correction to the diagonal principal symbol is smooth jointly in both
kernel positions, by differentiation under the fixed frequency integral
(`app:ch_background:eq:bg-symbol`). -/
theorem diagonalCompletionErrorKernel_contDiff (i j : Fin n) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      diagonalCompletionErrorKernel a J u Ω K i j p.1 p.2) := by
  have hd : ContDiff ℝ ∞ (fun p : TransportSymbol.Variables n ↦
      reflectedCompletionError a J u Ω K (p.1, p.1, p.2.2)) :=
    he.comp (contDiff_fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd))
  have hs : ∀ p : TransportSymbol.Variables n, max 2 (2 * C) < ‖p.2.2‖ →
      reflectedCompletionError a J u Ω K (p.1, p.1, p.2.2) = 0 :=
    fun p hp ↦ reflectedCompletionError_eq_zero_of_large_frequency a J u Ω K
      hhigh hC hcomparison (p.1, p.1, p.2.2) hp.le
  exact contDiff_const.mul (correctionIntegral_contDiff hd hs i j)

/-- The literal conjugate transpose of the diagonal correction kernel is
smooth as well (`app:ch_background:eq:bg-symbol`). -/
theorem diagonalCompletionErrorKernel_adjoint_contDiff (i j : Fin n) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      conj (diagonalCompletionErrorKernel a J u Ω K j i p.2 p.1)) := by
  have hswap : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      diagonalCompletionErrorKernel a J u Ω K j i p.2 p.1) :=
    (diagonalCompletionErrorKernel_contDiff a J u Ω K he hhigh hC hcomparison j i).comp
      (f := fun p : Euclidean n × Euclidean n ↦ (p.2, p.1))
      (contDiff_snd.prodMk contDiff_fst)
  exact (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp hswap

end Completion

/-- Exact principal-plus-remainders decomposition of the source-tested reflected
normal. The Taylor remainder is that of the ORIGINAL full amplitude, whose
order-minus-one bound is proved in `RemainderBounds`. The second remainder is
the literal bounded-frequency correction to its diagonal. Only the shared
calculus's four source Fourier convergence inputs remain conditional; no
uncut carrier bound is assumed (`app:ch_background:eq:bg-real-symbol`). -/
theorem fullAmplitudeOperator_reflected_principal_reduction
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (reflectedSymbolAmplitude a J u Ω K))
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1)
    {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (i j : Fin n) (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (f : Euclidean n → ℂ) (x : Euclidean n)
    (hβ : ContDiff ℝ ∞ β)
    (hβa : ∀ ξ y, reflectedSymbolAmplitude a J u Ω K
      (x, y, (2 * Real.pi) • ξ) i j ≠ 0 → β y = 1)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hi : Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x))
    (hid : Integrable (sourceAmplitudeTransform (diagonalAmplitude (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (hir : Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude b (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (hiB : Integrable (sourceAmplitudeTransform (fullTaylorCoefficient (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x)) :
    fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x =
      fullAmplitudeOperator (unitCompletedPrincipalEntry a J u Ω K i j)
        (fun y ↦ β y • f y) x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x +
      ∫ y, (β y • f y) * diagonalCompletionErrorKernel a J u Ω K i j x y := by
  have ha' : ContDiff ℝ ∞ (fun p : TransportSymbol.Variables n ↦
      (reflectedSymbolAmplitude a J u Ω K (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp ha).comp
      (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul _))))
  have hβa' : ∀ ξ y, (reflectedSymbolAmplitude a J u Ω K
      (x, y, (2 * Real.pi) • ξ) i j : ℂ) ≠ 0 → β y = 1 := by
    intro ξ y hne
    exact hβa ξ y (fun hz ↦ hne (by simp [hz]))
  let c : Euclidean n → Euclidean n → Euclidean n → ℂ := fun x y ξ ↦
    reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j
  let rem : ℂ := fullAmplitudeOperator (diagonalRemainderAmplitude b c β) f x
  have hred := fullAmplitudeOperator_eq_diagonal_add_remainder b c β f x ha' hβ hβa'
    hf hfc hi hid hir hiB
  have hdiag := fullAmplitudeOperator_diagonalAmplitude c β f x
  have hid' : Integrable (sourceAmplitudeTransform (fun x _y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, x, (2 * Real.pi) • ξ) i j : ℂ))
      (fun y ↦ β y • f y) x) := by
    apply hid.congr
    filter_upwards [] with ξ
    unfold sourceAmplitudeTransform diagonalAmplitude
    apply congrArg (fun g : Euclidean n → ℂ ↦ 𝓕 g ξ)
    funext y
    dsimp only
    rw [smul_assoc, smul_comm]
  have he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K) := ha.sub hc
  have hbf : Continuous (fun y ↦ β y • f y) := hβ.continuous.smul hf
  have hbfc : HasCompactSupport (fun y ↦ β y • f y) := HasCompactSupport.smul_left (f := β) hfc
  have hsplit := fullAmplitudeOperator_diagonal_reflected_eq_completed_add_kernel a J u Ω K
    he hone hC hcomparison hc i j (fun y ↦ β y • f y)
    hbf hbfc x hid'
  exact hred.trans ((congrArg (fun z : ℂ ↦ z + rem) (hdiag.trans hsplit)).trans
    (add_right_comm _ _ _))

/-- Primitive regularity and punctured conic buffers supply all smoothness in
the principal-plus-remainders decomposition. The four source Fourier convergence
inputs are exactly those of the shared diagonal calculus; the bounded-frequency
term requires no additional integrability input. Consumers must instantiate the
geometric data and source convergence before claiming the actual normal reduction
(`app:ch_background:eq:bg-real-symbol`). -/
theorem fullAmplitudeOperator_principal_reduction_of_primitive_inputs
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (F : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2)
    {Ω : Set (TransportSymbol.Variables n × Euclidean 2)}
    {W Z : Set (TransportSymbol.InputVariables n)}
    (hΩ : IsOpen Ω) (h : TransportSymbol.PrimitiveRegularity a J W)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (TransportSymbol.inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (TransportSymbol.inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z)
    (hbuffer : closure (F '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    (hzero : ∀ t : ℝ, t ≤ 1 → a.high t = 0)
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1)
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hlower : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖)
    {K : Set (Euclidean 2)} (hK : IsCompact K)
    (i j : Fin n) (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (f : Euclidean n → ℂ) (x : Euclidean n)
    (hβ : ContDiff ℝ ∞ β)
    (hβa : ∀ ξ y, reflectedSymbolAmplitude a J u Ω K
      (x, y, (2 * Real.pi) • ξ) i j ≠ 0 → β y = 1)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hi : Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x))
    (hid : Integrable (sourceAmplitudeTransform (diagonalAmplitude (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (hir : Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude b (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (hiB : Integrable (sourceAmplitudeTransform (fullTaylorCoefficient (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x)) :
    fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x =
      fullAmplitudeOperator (unitCompletedPrincipalEntry a J u Ω K i j)
        (fun y ↦ β y • f y) x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x +
      ∫ y, (β y • f y) * diagonalCompletionErrorKernel a J u Ω K i j x y := by
  have ha := (TransportSymbol.amplitude_smooth_and_derivatives_of_punctured_buffer
    a J u F hΩ h hu hmap hright hs hbuffer hzero hCupper hℓ hlow hupper hK).1
  have hh := TransportSymbol.homogeneousAmplitude_contDiffOn_punctured
    a J u F hΩ h hu hmap hright hs hbuffer hK
  have har : ContDiff ℝ ∞ (reflectedSymbolAmplitude a J u Ω K) :=
    (ha.add (ha.comp
      (contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))).const_smul _
  exact fullAmplitudeOperator_reflected_principal_reduction a J u Ω K har
    (completedReflectedAmplitude_contDiff a J u Ω K hh) hone hClower hlower
    i j b β f x hβ hβa hf hfc hi hid hir hiB

end JanetCartan.ContinuumRow.TransportKernel
