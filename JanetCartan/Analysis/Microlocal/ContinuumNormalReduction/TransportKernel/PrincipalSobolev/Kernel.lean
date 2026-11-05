module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.CompactKernel

/-!
# Localized diagonal correction on Euclidean L²

The bounded-frequency error following `app:ch_background:eq:bg-real-symbol`
is the diagonal correction in the principal reduction. We retain its literal
frequency normalization and Euclidean Lebesgue measures. The compact-kernel
realization identifies the Hilbert adjoint on every L² datum.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel
variable {n N : ℕ}

/-- Fixed physical mask for the diagonal error after
`app:ch_background:eq:bg-real-symbol`. -/
def diagonalCorrectionMask (χ β : Euclidean n → ℝ) (p : Euclidean n × Euclidean n) : ℂ :=
  (χ p.1 : ℂ) * (β p.2 : ℂ)

/-- Smoothness of the fixed physical mask in
`app:ch_background:eq:bg-real-symbol`. -/
theorem diagonalCorrectionMask_contDiff {χ β : Euclidean n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (diagonalCorrectionMask χ β) :=
  (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)).mul
    (Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_snd))

/-- Compact support in both physical positions for the correction in
`app:ch_background:eq:bg-real-symbol`. -/
theorem diagonalCorrectionMask_hasCompactSupport {χ β : Euclidean n → ℝ}
    (hχ : HasCompactSupport χ) (hβ : HasCompactSupport β) :
    HasCompactSupport (diagonalCorrectionMask χ β) := by
  apply HasCompactSupport.intro (hχ.prod hβ)
  intro p hp
  simp only [mem_prod, not_and_or] at hp
  rcases hp with hx | hy
  · simp [diagonalCorrectionMask, image_eq_zero_of_notMem_tsupport hx]
  · simp [diagonalCorrectionMask, image_eq_zero_of_notMem_tsupport hy]

variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ β : Euclidean n → ℝ)

/-- The literal localized diagonal kernel in
`fullAmplitudeOperator_principal_reduction_of_primitive_inputs`
(`app:ch_background:eq:bg-real-symbol`). -/
def localizedDiagonalCorrectionKernel (i j : Fin n) (x y : Euclidean n) : ℂ :=
  diagonalCorrectionMask χ β (x, y) * diagonalCompletionErrorKernel a J u Ω K i j x y

/-- The literal matrix-adjoint kernel, with exchanged positions and indices
(`app:ch_background:eq:bg-real-symbol`). -/
def localizedDiagonalCorrectionAdjointKernel (i j : Fin n) (x y : Euclidean n) : ℂ :=
  conj (localizedDiagonalCorrectionKernel a J u Ω K χ β j i y x)

/-- The physical masks exchange under the literal adjoint
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionAdjointKernel_eq (i j : Fin n) (x y : Euclidean n) :
    localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j x y =
      diagonalCorrectionMask β χ (x, y) *
        conj (diagonalCompletionErrorKernel a J u Ω K j i y x) := by
  simp only [localizedDiagonalCorrectionAdjointKernel, localizedDiagonalCorrectionKernel,
    diagonalCorrectionMask, map_mul, Complex.conj_ofReal]
  ring

/-- Localization preserves compact physical support
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionKernel_hasCompactSupport
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β) (i j : Fin n) :
    HasCompactSupport (Function.uncurry
      (localizedDiagonalCorrectionKernel a J u Ω K χ β i j)) :=
  (diagonalCorrectionMask_hasCompactSupport hχs hβs).mul_right

/-- Compact support of the literal adjoint uses the exchanged fixed masks
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionAdjointKernel_hasCompactSupport
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β) (i j : Fin n) :
    HasCompactSupport (Function.uncurry
      (localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j)) := by
  change HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
    localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j p.1 p.2)
  simp_rw [localizedDiagonalCorrectionAdjointKernel_eq]
  exact (diagonalCorrectionMask_hasCompactSupport hβs hχs).mul_right

variable (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)

include he hone hC hcomparison hχ hβ in
/-- The localized literal diagonal kernel is smooth
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionKernel_contDiff (i j : Fin n) :
    ContDiff ℝ ∞ (Function.uncurry
      (localizedDiagonalCorrectionKernel a J u Ω K χ β i j)) :=
  (diagonalCorrectionMask_contDiff hχ hβ).mul
    (diagonalCompletionErrorKernel_contDiff a J u Ω K he hone hC hcomparison i j)

include he hone hC hcomparison hχ hβ in
/-- Smoothness of the actual adjoint kernel
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionAdjointKernel_contDiff (i j : Fin n) :
    ContDiff ℝ ∞ (Function.uncurry
      (localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j)) := by
  change ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
    localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j p.1 p.2)
  simp_rw [localizedDiagonalCorrectionAdjointKernel_eq]
  exact (diagonalCorrectionMask_contDiff hβ hχ).mul
    (diagonalCompletionErrorKernel_adjoint_contDiff a J u Ω K he hone hC hcomparison i j)

variable (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β)

/-- The diagonal correction on the full Euclidean L² space, constructed from
its actual smooth compact kernel (`app:ch_background:eq:bg-real-symbol`). -/
def localizedDiagonalCorrectionOperator (i j : Fin n) :
    Lp ℂ 2 (volume : Measure (Euclidean n)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  compactKernelOperator
    (localizedDiagonalCorrectionKernel_contDiff a J u Ω K χ β he hone hC
      hcomparison hχ hβ i j).continuous
    (localizedDiagonalCorrectionKernel_hasCompactSupport a J u Ω K χ β hχs hβs i j)

/-- Identification on every L² datum with the literal integral from the
principal reduction (`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionOperator_ae_integral (i j : Fin n)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC hcomparison
      hχ hβ hχs hβs i j f =ᵐ[volume]
        fun x ↦ ∫ y, localizedDiagonalCorrectionKernel a J u Ω K χ β i j x y * f y :=
  compactKernelOperator_ae_integral _ _ f

/-- The localized operator is exactly the correction appearing in
`fullAmplitudeOperator_principal_reduction_of_primitive_inputs`, multiplied
by the output cutoff (`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionOperator_ae_principal_integral (i j : Fin n)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC hcomparison
      hχ hβ hχs hβs i j f =ᵐ[volume]
        fun x ↦ χ x • ∫ y, (β y • f y) * diagonalCompletionErrorKernel a J u Ω K i j x y := by
  filter_upwards [localizedDiagonalCorrectionOperator_ae_integral a J u Ω K χ β
    he hone hC hcomparison hχ hβ hχs hβs i j f] with x hx
  rw [hx, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [localizedDiagonalCorrectionKernel, diagonalCorrectionMask, Complex.real_smul]
  ring

/-- The Hilbert adjoint exchanges positions and conjugates the kernel, with
the same Euclidean measures (`app:ch_background:eq:bg-real-symbol`). -/
theorem localizedDiagonalCorrectionOperator_adjoint_ae_integral (i j : Fin n)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) :
    (localizedDiagonalCorrectionOperator a J u Ω K χ β he hone hC hcomparison
      hχ hβ hχs hβs j i).adjoint f =ᵐ[volume]
        fun x ↦ ∫ y, localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j x y * f y :=
  compactKernelOperator_adjoint_ae_integral _ _ f

include he hone hC hcomparison hχ hβ hχs hβs in
/-- Absolute convergence for every L² input and every output position
(`app:ch_background:eq:bg-real-symbol`). -/
theorem integrable_localizedDiagonalCorrectionKernel_mul_L2 (i j : Fin n)
    (f : Lp ℂ 2 (volume : Measure (Euclidean n))) (x : Euclidean n) :
    Integrable (fun y ↦ localizedDiagonalCorrectionKernel a J u Ω K χ β i j x y * f y) :=
  integrable_compactKernel_mul_L2
    (localizedDiagonalCorrectionKernel_contDiff a J u Ω K χ β he hone hC
      hcomparison hχ hβ i j).continuous
    (localizedDiagonalCorrectionKernel_hasCompactSupport a J u Ω K χ β hχs hβs i j) f x

end JanetCartan.ContinuumRow.TransportKernel
