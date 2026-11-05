module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskDerivative
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Oscillatory phase transport

Pointwise chain rules for `app:ch_osc:prop:osc-normal`. The sole geometric
input is the phase velocity identity; no integrated identity is assumed.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.NormalComparison.CompactTransport

variable {n : ℕ}

/-- Coordinate expansion of the phase differential in
`app:ch_osc:prop:osc-normal`. -/
theorem differential_eq_sum (L : Euclidean n →L[ℝ] ℝ) (w : Euclidean n) :
    L w = ∑ j, w j * L (EuclideanSpace.single j 1) := by
  have hw : w = ∑ j, w j • EuclideanSpace.single j 1 := by
    ext i
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hw]
  simp

/-- The smooth phase extension gives a smooth oscillatory factor
(`app:ch_osc:prop:osc-normal`). -/
theorem contDiff_oscillatoryFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : ℝ) :
    ContDiff ℝ ∞ (fun u ↦ oscillatoryFactor K (φ u)) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ))).cexp

/-- Input-coordinate chain rule for the oscillatory factor in
`app:ch_osc:prop:osc-normal`. -/
theorem partialDeriv_oscillatoryFactor {φ : Euclidean n → ℝ} {u : Euclidean n}
    (hφ : DifferentiableAt ℝ φ u) (K : ℝ) (j : Fin n) :
    partialDeriv (fun u ↦ oscillatoryFactor K (φ u)) u j =
      oscillatoryFactor K (φ u) * (Complex.I * (K * partialDeriv φ u j : ℝ)) := by
  have hd := (((Complex.ofRealCLM.hasFDerivAt.comp u
    (hφ.hasFDerivAt.const_mul K)).const_mul Complex.I).cexp).fderiv
  have hh := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1)) hd
  simpa [oscillatoryFactor, partialDeriv, Function.comp_def] using hh

/-- The geometric velocity identity gives transport of the exponential in
`app:ch_osc:prop:osc-normal`. All physical positions can be arbitrary spectator
parameters in `Φ` and `w`. -/
theorem deriv_oscillatoryFactor_transport {Φ : ℝ × Euclidean n → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (s K : ℝ) (u w : Euclidean n)
    (hv : deriv (fun t ↦ Φ (t, u)) s = fderiv ℝ (fun v ↦ Φ (s, v)) u w) :
    deriv (fun t ↦ oscillatoryFactor K (Φ (t, u))) s =
      ∑ j, w j • partialDeriv (fun v ↦ oscillatoryFactor K (Φ (s, v))) u j := by
  have ht : DifferentiableAt ℝ (fun t ↦ Φ (t, u)) s :=
    (hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s
  have hu : DifferentiableAt ℝ (fun v ↦ Φ (s, v)) u :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) u
  rw [show deriv (fun t ↦ oscillatoryFactor K (Φ (t, u))) s =
      oscillatoryFactor K (Φ (s, u)) * (Complex.I * (K * deriv (fun t ↦ Φ (t, u)) s : ℝ)) from
    (((ht.hasDerivAt.const_mul K).ofReal_comp.const_mul Complex.I).cexp).deriv]
  rw [hv, differential_eq_sum]
  simp_rw [partialDeriv_oscillatoryFactor hu K, Complex.real_smul]
  simp only [Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold partialDeriv
  ring

/-- The actual parameter derivative of a jointly smooth amplitude is smooth
in the input variable (`app:ch_osc:prop:osc-normal`). -/
theorem contDiff_parameterDeriv {A : ℝ × Euclidean n → ℂ}
    (hA : ContDiff ℝ ∞ A) (s : ℝ) :
    ContDiff ℝ ∞ (fun u ↦ deriv (fun t ↦ A (t, u)) s) := by
  have h : ContDiff ℝ ∞ (Function.uncurry (fun (u : Euclidean n) (t : ℝ) ↦ A (t, u))) :=
    hA.comp (contDiff_snd.prodMk contDiff_fst)
  exact (h.fderiv contDiff_const (by simp)).clm_apply contDiff_const

end JanetCartan.NormalComparison.CompactTransport
