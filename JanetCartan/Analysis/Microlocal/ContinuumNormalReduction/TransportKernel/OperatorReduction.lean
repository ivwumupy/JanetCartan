module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev

/-!
# The actual remainder operators in the principal reduction

The two bounded operators estimated after `app:ch_background:eq:bg-real-symbol`
are exactly the Taylor remainder and diagonal correction in the source-tested
identity. This module identifies their action, including the fixed physical
cutoffs, on compact smooth tests. All measures here are Euclidean Lebesgue.

The remainder's smoothness, support and physical derivative budget are precisely
the witnesses produced by
`exists_localized_reflectedRemainder_integer_gain_of_primitiveNorms`. The correction
is the literal compact-kernel operator estimated by
`exists_localizedDiagonalCorrectionOperator_sobolev_of_primitiveNorms`.
Neither operator action nor a Sobolev estimate is assumed in the identity below.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction Pseudodifferential AmplitudeBound ContinuumNormal
variable {n N : ℕ}

private theorem fullAmplitudeOperator_localized_on_test
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (χ γ : Euclidean n → ℝ) (f : Euclidean n → ℂ) (x : Euclidean n)
    (hγ : ∀ y, γ y • f y = f y) :
    fullAmplitudeOperator (fun x y ξ ↦ χ x • (γ y • c x y ξ)) f x =
      χ x • fullAmplitudeOperator c f x := by
  have he (ξ y : Euclidean n) :
      f y • (χ x • (γ y • c x y ξ)) = χ x • (f y • c x y ξ) := by
    calc
      _ = χ x • ((γ y • f y) • c x y ξ) := by
        simp only [smul_eq_mul, Complex.real_smul]
        ring
      _ = _ := by rw [hγ y]
  simp only [fullAmplitudeOperator, sourceAmplitudeTransform, Real.fourierInv_eq,
    Real.fourier_eq, he]
  simp_rw [smul_comm (Real.fourierChar _) (χ x), integral_smul]
  simp_rw [smul_comm (Real.fourierChar _) (χ x), integral_smul]

/-- The actual bounded Taylor-remainder and diagonal-correction operators give
the exact localized principal reduction on compact smooth tests. The former
uses the ORIGINAL reflected full amplitude; the latter uses the diagonal
completion discrepancy, with the normalized physical frequency integral.
The source Fourier convergence inputs are those of the shared diagonal calculus
(`app:ch_background:eq:bg-real-symbol`). -/
theorem localized_reflected_principal_reduction
    (hn : 0 < n)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (reflectedSymbolAmplitude a J u Ω K))
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1)
    {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (i j : Fin n) (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β χ γ : Euclidean n → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hβs : HasCompactSupport β) (hχs : HasCompactSupport χ)
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f)
    (hγf : ∀ y ∈ tsupport f, γ y = 1)
    (hβa : ∀ x ξ y, reflectedSymbolAmplitude a J u Ω K
      (x, y, (2 * Real.pi) • ξ) i j ≠ 0 → β y = 1)
    (hi : ∀ x, Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x))
    (hid : ∀ x, Integrable (sourceAmplitudeTransform (diagonalAmplitude (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (hir : ∀ x, Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude basis
      (fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (hiB : ∀ x, Integrable (sourceAmplitudeTransform (fullTaylorCoefficient (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) f x))
    (R M : ℝ) :
    let c := fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)
    let rem := diagonalRemainderAmplitude basis c β
    let brem := localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) rem χ γ
    ∀ (hb : ContDiff ℝ ∞ (Function.uncurry brem))
      (hs : ∀ ξ, SupportedInCenteredBox R (brem ξ))
      (hM : HasAmplitudeDerivativeBound brem (2 * (n + 1)) M),
    let fL2 := (hf.continuous.memLp_of_hasCompactSupport hfs).toLp f
    let Trem := twoPositionL2Operator hn R brem hb hs M hM
    let Tcorr := localizedDiagonalCorrectionOperator a J u Ω K χ β
      (ha.sub hc) hone hC hcomparison hχ hβ hχs hβs i j
    (fun x ↦ χ x • fullAmplitudeOperator c f x) =ᵐ[volume]
      fun x ↦ χ x • fullAmplitudeOperator (unitCompletedPrincipalEntry a J u Ω K i j)
        (fun y ↦ β y • f y) x + Trem fL2 x + Tcorr fL2 x := by
  dsimp only
  intro hb hs hM
  let c := fun x y ξ ↦
    (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)
  let rem := diagonalRemainderAmplitude basis c β
  have hγ : ∀ y, γ y • f y = f y := by
    intro y
    by_cases hy : y ∈ tsupport f
    · rw [hγf y hy, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have ht := localizedRemainderL2Operator_toLp_ae_fullAmplitudeOperator
    hn R rem χ γ hb hs M hM f hf hfs
  have he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K) := ha.sub hc
  have hcorr := localizedDiagonalCorrectionOperator_ae_principal_integral
    a J u Ω K χ β he hone hC hcomparison hχ hβ hχs hβs i j
    ((hf.continuous.memLp_of_hasCompactSupport hfs).toLp f)
  have hcoe : ((hf.continuous.memLp_of_hasCompactSupport hfs).toLp f :
      Lp ℂ 2 (volume : Measure (Euclidean n))) =ᵐ[volume] f :=
    (hf.continuous.memLp_of_hasCompactSupport hfs).coeFn_toLp
  have hkernel (x : Euclidean n) :
      (∫ y, (β y • ((hf.continuous.memLp_of_hasCompactSupport hfs).toLp f :
        Lp ℂ 2 (volume : Measure (Euclidean n))) y) *
        diagonalCompletionErrorKernel a J u Ω K i j x y) =
      ∫ y, (β y • f y) * diagonalCompletionErrorKernel a J u Ω K i j x y :=
    integral_congr_ae (hcoe.mono (fun y hy ↦ by dsimp only; rw [hy]))
  filter_upwards [ht, hcorr] with x hx hc'
  rw [hx, hc', hkernel x, fullAmplitudeOperator_localized_on_test rem χ γ f x hγ,
    fullAmplitudeOperator_reflected_principal_reduction a J u Ω K ha hc hone hC hcomparison
      i j basis β f x hβ (hβa x) hf.continuous hfs (hi x) (hid x) (hir x) (hiB x),
    smul_add, smul_add]

end JanetCartan.ContinuumRow.TransportKernel
