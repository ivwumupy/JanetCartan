module
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module

/-!
# Exact derivatives of modulated complex waves

Product-rule identities used in `app:ch_waves:thm:leading` and
`app:ch_waves:thm:wkb` of paper.tex. The frequency `lam` is the physical
frequency in `exp (I * lam * φ)`; the unit-torus convention therefore puts
any required `2 * Real.pi` in the physical phase/frequency itself.

The amplitudes take values in any complex normed vector space with its
compatible real scalar structure, in particular `EuclideanSpace ℂ (Fin N)`.
All derivatives are real Fréchet derivatives. The second derivative means
first differentiating in the constant direction `v`, then in `w`.
The Euclidean coordinate versions use the existing `partialDeriv`.

First derivatives require differentiability at the evaluation point; second
derivatives require `ContDiff ℝ 2`. Quadratures are given through arbitrary
continuous complex linear coordinates `L`, with explicit real and imaginary
amplitude expansions. The two-term field is exactly
`lam⁻² * exp (I * lam * φ) * (a + lam⁻¹ * b)`.
These are exact calculus identities: phase existence, transport equations,
reconstruction, and analytic estimates remain separate inputs.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The oscillatory scalar in `app:ch_waves:thm:leading`, at physical frequency `lam`. -/
def waveCarrier (lam : ℝ) (φ : E → ℝ) (x : E) : ℂ :=
  Complex.exp (Complex.I * (lam : ℂ) * (φ x : ℂ))
/-- The actual vector field `exp (I * lam * φ) • a` in `app:ch_waves:thm:leading`. -/
def modulatedWave (lam : ℝ) (φ : E → ℝ) (a : E → F) (x : E) : F :=
  waveCarrier lam φ x • a x
/-- The exact demodulated first derivative in `app:ch_waves:thm:leading`. -/
def waveFirstAmplitude (lam : ℝ) (φ : E → ℝ) (a : E → F) (x v : E) : F :=
  (Complex.I * (lam : ℂ) * (fderiv ℝ φ x v : ℂ)) • a x + fderiv ℝ a x v

/-- Chain rule for the scalar carrier in `app:ch_waves:thm:leading`. -/
theorem hasFDerivAt_waveCarrier {lam : ℝ} {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    HasFDerivAt (waveCarrier lam φ)
      (waveCarrier lam φ x • ((Complex.I * (lam : ℂ)) •
        (Complex.ofRealCLM.comp (fderiv ℝ φ x)))) x := by
  exact ((Complex.ofRealCLM.hasFDerivAt.comp x hφ.hasFDerivAt).const_smul
    (Complex.I * (lam : ℂ))).cexp

/-- Exact first derivative of the modulated field in `app:ch_waves:thm:leading`. -/
theorem fderiv_modulatedWave {lam : ℝ} {φ : E → ℝ} {a : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) (v : E) :
    fderiv ℝ (modulatedWave lam φ a) x v =
      waveCarrier lam φ x • waveFirstAmplitude lam φ a x v := by
  change fderiv ℝ (waveCarrier lam φ • a) x v = _
  rw [((hasFDerivAt_waveCarrier (lam := lam) hφ).smul ha.hasFDerivAt).fderiv]
  simp [waveFirstAmplitude, smul_add, smul_smul, mul_assoc, add_comm]

/-- The demodulated second derivative in `app:ch_waves:thm:wkb`, with explicit `-lam²`,
`I * lam`, and frequency-independent terms. -/
def waveSecondAmplitude (lam : ℝ) (φ : E → ℝ) (a : E → F) (x v w : E) : F :=
  (-((lam : ℂ) ^ 2) * (fderiv ℝ φ x v : ℂ) * (fderiv ℝ φ x w : ℂ)) • a x +
    (Complex.I * (lam : ℂ)) •
      ((fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x w : ℂ) • a x +
        (fderiv ℝ φ x v : ℂ) • fderiv ℝ a x w +
        (fderiv ℝ φ x w : ℂ) • fderiv ℝ a x v) +
    fderiv ℝ (fun y ↦ fderiv ℝ a y v) x w

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- Regularity of constant-direction derivatives used in `app:ch_waves:thm:wkb`. -/
theorem differentiable_fderiv_apply_const {a : E → F} (ha : ContDiff ℝ 2 a) (v : E) :
    Differentiable ℝ (fun y ↦ fderiv ℝ a y v) := by
  exact ((ha.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)

/-- Derivative of the first amplitude used in `app:ch_waves:thm:wkb`. -/
theorem fderiv_waveFirstAmplitude {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (x v w : E) :
    fderiv ℝ (fun y ↦ waveFirstAmplitude lam φ a y v) x w =
      (Complex.I * (lam : ℂ)) •
        ((fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x w : ℂ) • a x +
        (fderiv ℝ φ x v : ℂ) • fderiv ℝ a x w) +
      fderiv ℝ (fun y ↦ fderiv ℝ a y v) x w := by
  have hp := differentiable_fderiv_apply_const hφ v
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp x (hp x).hasFDerivAt).const_smul
    (Complex.I * (lam : ℂ))
  have hd := (hc.smul (ha.differentiable (by norm_num) x).hasFDerivAt).add
    (differentiable_fderiv_apply_const ha v x).hasFDerivAt
  change HasFDerivAt (fun y ↦ waveFirstAmplitude lam φ a y v) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    smul_add, smul_smul, add_comm]

/-- Regularity needed to differentiate the amplitude in `app:ch_waves:thm:wkb`. -/
theorem differentiable_waveFirstAmplitude {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (v : E) :
    Differentiable ℝ (fun y ↦ waveFirstAmplitude lam φ a y v) := by
  have hp : Differentiable ℝ (fun y ↦ fderiv ℝ φ y v) :=
    differentiable_fderiv_apply_const hφ v
  have hc : Differentiable ℝ (fun y ↦ (Complex.I * (lam : ℂ)) *
      (fderiv ℝ φ y v : ℂ)) :=
    (Complex.ofRealCLM.differentiable.comp hp).const_smul (Complex.I * (lam : ℂ))
  exact (hc.smul (ha.differentiable (by norm_num))).add (differentiable_fderiv_apply_const ha v)

/-- Exact second derivative of the field in `app:ch_waves:thm:wkb`. -/
theorem fderiv_fderiv_modulatedWave {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (x v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ (modulatedWave lam φ a) y v) x w =
      waveCarrier lam φ x • waveSecondAmplitude lam φ a x v w := by
  have he : (fun y ↦ fderiv ℝ (modulatedWave lam φ a) y v) =
      modulatedWave lam φ (fun y ↦ waveFirstAmplitude lam φ a y v) := by
    funext y
    exact fderiv_modulatedWave (hφ.differentiable (by norm_num) y)
      (ha.differentiable (by norm_num) y) v
  rw [he, fderiv_modulatedWave (hφ.differentiable (by norm_num) x)
    (differentiable_waveFirstAmplitude hφ ha v x)]
  congr 1
  rw [waveFirstAmplitude]
  rw [fderiv_waveFirstAmplitude hφ ha]
  unfold waveSecondAmplitude
  simp only [waveFirstAmplitude, smul_add, smul_smul]
  have hc : (Complex.I * (lam : ℂ) * (fderiv ℝ φ x w : ℂ)) *
      (Complex.I * (lam : ℂ) * (fderiv ℝ φ x v : ℂ)) =
      -((lam : ℂ) ^ 2) * (fderiv ℝ φ x v : ℂ) * (fderiv ℝ φ x w : ℂ) := by
    calc
      _ = Complex.I ^ 2 * ((lam : ℂ) ^ 2 * (fderiv ℝ φ x v : ℂ) *
        (fderiv ℝ φ x w : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hc]
  module

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Exact removal of the oscillation in `app:ch_waves:thm:wkb`. -/
theorem waveCarrier_neg_mul (lam : ℝ) (φ : E → ℝ) (x : E) :
    waveCarrier (-lam) φ x * waveCarrier lam φ x = 1 := by
  simp only [waveCarrier, Complex.ofReal_neg, mul_neg, neg_mul, Complex.exp_neg]
  exact inv_mul_cancel₀ (Complex.exp_ne_zero _)

/-- The demodulated first derivative used in `app:ch_waves:thm:leading`. -/
theorem demodulated_fderiv_modulatedWave {lam : ℝ} {φ : E → ℝ} {a : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) (v : E) :
    waveCarrier (-lam) φ x • fderiv ℝ (modulatedWave lam φ a) x v =
      waveFirstAmplitude lam φ a x v := by
  rw [fderiv_modulatedWave hφ ha, smul_smul, waveCarrier_neg_mul, one_smul]

/-- The demodulated second derivative used in `app:ch_waves:thm:wkb`. -/
theorem demodulated_fderiv_fderiv_modulatedWave {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (x v w : E) :
    waveCarrier (-lam) φ x •
      fderiv ℝ (fun y ↦ fderiv ℝ (modulatedWave lam φ a) y v) x w =
      waveSecondAmplitude lam φ a x v w := by
  rw [fderiv_fderiv_modulatedWave hφ ha, smul_smul, waveCarrier_neg_mul, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Cosine quadrature of the carrier in `app:ch_waves:thm:leading`. -/
theorem waveCarrier_re (lam : ℝ) (φ : E → ℝ) (x : E) :
    (waveCarrier lam φ x).re = Real.cos (lam * φ x) := by
  unfold waveCarrier
  rw [show Complex.I * (lam : ℂ) * (φ x : ℂ) = (↑(lam * φ x) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Sine quadrature of the carrier in `app:ch_waves:thm:leading`. -/
theorem waveCarrier_im (lam : ℝ) (φ : E → ℝ) (x : E) :
    (waveCarrier lam φ x).im = Real.sin (lam * φ x) := by
  unfold waveCarrier
  rw [show Complex.I * (lam : ℂ) * (φ x : ℂ) = (↑(lam * φ x) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] in
/-- Real quadrature through a complex linear coordinate, for `app:ch_waves:thm:leading`. -/
theorem modulatedWave_re (lam : ℝ) (φ : E → ℝ) (a : E → F)
    (L : F →L[ℂ] ℂ) (x : E) :
    (L (modulatedWave lam φ a x)).re =
      Real.cos (lam * φ x) * (L (a x)).re -
        Real.sin (lam * φ x) * (L (a x)).im := by
  simp only [modulatedWave, map_smul, smul_eq_mul, Complex.mul_re,
    waveCarrier_re, waveCarrier_im]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] in
/-- Imaginary quadrature through a complex linear coordinate, for `app:ch_waves:thm:leading`. -/
theorem modulatedWave_im (lam : ℝ) (φ : E → ℝ) (a : E → F)
    (L : F →L[ℂ] ℂ) (x : E) :
    (L (modulatedWave lam φ a x)).im =
      Real.cos (lam * φ x) * (L (a x)).im +
        Real.sin (lam * φ x) * (L (a x)).re := by
  simp only [modulatedWave, map_smul, smul_eq_mul, Complex.mul_im,
    waveCarrier_re, waveCarrier_im]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- Commutation of coordinates and differentiation used in `app:ch_waves:thm:leading`. -/
theorem fderiv_linear_observable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun y ↦ L (f y)) x v = L (fderiv ℝ f x v) := by
  exact congrArg (fun D : E →L[ℝ] G ↦ D v)
    (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- Differentiability of the actual wave in `app:ch_waves:thm:leading`. -/
theorem differentiable_modulatedWave {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : Differentiable ℝ φ) (ha : Differentiable ℝ a) :
    Differentiable ℝ (modulatedWave lam φ a) :=
  fun x ↦ ((hasFDerivAt_waveCarrier (hφ x)).smul (ha x).hasFDerivAt).differentiableAt

/-- Smoothness of the actual wave in `app:ch_waves:thm:leading`. -/
theorem contDiff_modulatedWave {lam : ℝ} {φ : E → ℝ} {a : E → F} {k : ℕ∞ω}
    (hφ : ContDiff ℝ k φ) (ha : ContDiff ℝ k a) :
    ContDiff ℝ k (modulatedWave lam φ a) :=
  (((Complex.ofRealCLM.contDiff.comp hφ).const_smul (Complex.I * (lam : ℂ))).cexp).smul ha

/-- First derivative of the real quadrature in `app:ch_waves:thm:leading`. -/
theorem fderiv_modulatedWave_re {lam : ℝ} {φ : E → ℝ} {a : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x)
    (L : F →L[ℂ] ℂ) (v : E) :
    fderiv ℝ (fun y ↦ (L (modulatedWave lam φ a y)).re) x v =
      Real.cos (lam * φ x) * (L (waveFirstAmplitude lam φ a x v)).re -
        Real.sin (lam * φ x) * (L (waveFirstAmplitude lam φ a x v)).im := by
  have he : fderiv ℝ (fun y ↦ (L (modulatedWave lam φ a y)).re) x v =
      (L (fderiv ℝ (modulatedWave lam φ a) x v)).re :=
    fderiv_linear_observable (Complex.reCLM.comp (L.restrictScalars ℝ))
      (((hasFDerivAt_waveCarrier (lam := lam) hφ).smul ha.hasFDerivAt).differentiableAt) v
  rw [he, fderiv_modulatedWave hφ ha]
  exact modulatedWave_re lam φ (fun y ↦ waveFirstAmplitude lam φ a y v) L x

/-- First derivative of the imaginary quadrature in `app:ch_waves:thm:leading`. -/
theorem fderiv_modulatedWave_im {lam : ℝ} {φ : E → ℝ} {a : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x)
    (L : F →L[ℂ] ℂ) (v : E) :
    fderiv ℝ (fun y ↦ (L (modulatedWave lam φ a y)).im) x v =
      Real.cos (lam * φ x) * (L (waveFirstAmplitude lam φ a x v)).im +
        Real.sin (lam * φ x) * (L (waveFirstAmplitude lam φ a x v)).re := by
  have he : fderiv ℝ (fun y ↦ (L (modulatedWave lam φ a y)).im) x v =
      (L (fderiv ℝ (modulatedWave lam φ a) x v)).im :=
    fderiv_linear_observable (Complex.imCLM.comp (L.restrictScalars ℝ))
      (((hasFDerivAt_waveCarrier (lam := lam) hφ).smul ha.hasFDerivAt).differentiableAt) v
  rw [he, fderiv_modulatedWave hφ ha]
  exact modulatedWave_im lam φ (fun y ↦ waveFirstAmplitude lam φ a y v) L x

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- Commutation of coordinates and second derivatives used in `app:ch_waves:thm:wkb`. -/
theorem fderiv_fderiv_linear_observable {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ L (f z)) y v) x w =
      L (fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w) := by
  have he : (fun y ↦ fderiv ℝ (fun z ↦ L (f z)) y v) =
      (fun y ↦ L (fderiv ℝ f y v)) := by
    funext y
    exact fderiv_linear_observable L (hf.differentiable (by norm_num) y) v
  rw [he]
  exact fderiv_linear_observable L (differentiable_fderiv_apply_const hf v x) w

/-- Second derivative of the real quadrature in `app:ch_waves:thm:wkb`. -/
theorem fderiv_fderiv_modulatedWave_re {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a)
    (L : F →L[ℂ] ℂ) (x v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ (L (modulatedWave lam φ a z)).re) y v) x w =
      Real.cos (lam * φ x) * (L (waveSecondAmplitude lam φ a x v w)).re -
        Real.sin (lam * φ x) * (L (waveSecondAmplitude lam φ a x v w)).im := by
  have he : fderiv ℝ (fun y ↦ fderiv ℝ
      (fun z ↦ (L (modulatedWave lam φ a z)).re) y v) x w =
      (L (fderiv ℝ (fun y ↦ fderiv ℝ (modulatedWave lam φ a) y v) x w)).re :=
    fderiv_fderiv_linear_observable (Complex.reCLM.comp (L.restrictScalars ℝ))
      (contDiff_modulatedWave hφ ha) x v w
  rw [he, fderiv_fderiv_modulatedWave hφ ha]
  exact modulatedWave_re lam φ (fun y ↦ waveSecondAmplitude lam φ a y v w) L x

/-- Second derivative of the imaginary quadrature in `app:ch_waves:thm:wkb`. -/
theorem fderiv_fderiv_modulatedWave_im {lam : ℝ} {φ : E → ℝ} {a : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a)
    (L : F →L[ℂ] ℂ) (x v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ (L (modulatedWave lam φ a z)).im) y v) x w =
      Real.cos (lam * φ x) * (L (waveSecondAmplitude lam φ a x v w)).im +
        Real.sin (lam * φ x) * (L (waveSecondAmplitude lam φ a x v w)).re := by
  have he : fderiv ℝ (fun y ↦ fderiv ℝ
      (fun z ↦ (L (modulatedWave lam φ a z)).im) y v) x w =
      (L (fderiv ℝ (fun y ↦ fderiv ℝ (modulatedWave lam φ a) y v) x w)).im :=
    fderiv_fderiv_linear_observable (Complex.imCLM.comp (L.restrictScalars ℝ))
      (contDiff_modulatedWave hφ ha) x v w
  rw [he, fderiv_fderiv_modulatedWave hφ ha]
  exact modulatedWave_im lam φ (fun y ↦ waveSecondAmplitude lam φ a y v w) L x

/-- Euclidean coordinate version of the first product identity in `app:ch_waves:thm:leading`. -/
theorem partialDeriv_modulatedWave {n : ℕ} {lam : ℝ} {φ : Euclidean n → ℝ}
    {a : Euclidean n → F} {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) (i : Fin n) :
    partialDeriv (modulatedWave lam φ a) x i = waveCarrier lam φ x •
      ((Complex.I * (lam : ℂ) * (↑(partialDeriv φ x i) : ℂ)) • a x + partialDeriv a x i) :=
  fderiv_modulatedWave hφ ha _

/-- Euclidean coordinate second derivative for `app:ch_waves:thm:wkb`. -/
theorem partialDeriv_partialDeriv_modulatedWave {n : ℕ} {lam : ℝ}
    {φ : Euclidean n → ℝ} {a : Euclidean n → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (x : Euclidean n) (i j : Fin n) :
    partialDeriv (fun y ↦ partialDeriv (modulatedWave lam φ a) y i) x j =
      waveCarrier lam φ x • waveSecondAmplitude lam φ a x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
  fderiv_fderiv_modulatedWave hφ ha _ _ _

/-- The field in `app:ch_waves:eq:WKB-u`, with `τ = lam⁻¹`. -/
def twoTermWave (lam : ℝ) (φ : E → ℝ) (a b : E → F) : E → F :=
  modulatedWave lam φ (fun x ↦ ((lam : ℂ)⁻¹) ^ 2 • (a x + (lam : ℂ)⁻¹ • b x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] in
/-- The exact `lam⁻²` and `lam⁻³` weights of `app:ch_waves:eq:WKB-u`. -/
theorem twoTermWave_eq_sum (lam : ℝ) (φ : E → ℝ) (a b : E → F) :
    twoTermWave lam φ a b =
      ((lam : ℂ)⁻¹) ^ 2 • modulatedWave lam φ a +
        ((lam : ℂ)⁻¹) ^ 3 • modulatedWave lam φ b := by
  funext x
  simp only [twoTermWave, modulatedWave, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
  module

/-- First derivative of `app:ch_waves:eq:WKB-u`, retaining both exact frequency weights. -/
theorem fderiv_twoTermWave {lam : ℝ} {φ : E → ℝ} {a b : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (v : E) :
    fderiv ℝ (twoTermWave lam φ a b) x v = waveCarrier lam φ x •
      (((lam : ℂ)⁻¹) ^ 2 • waveFirstAmplitude lam φ a x v +
        ((lam : ℂ)⁻¹) ^ 3 • waveFirstAmplitude lam φ b x v) := by
  have hwa := ((hasFDerivAt_waveCarrier (lam := lam) hφ).smul ha.hasFDerivAt).differentiableAt
  have hwb := ((hasFDerivAt_waveCarrier (lam := lam) hφ).smul hb.hasFDerivAt).differentiableAt
  change DifferentiableAt ℝ (modulatedWave lam φ a) x at hwa
  change DifferentiableAt ℝ (modulatedWave lam φ b) x at hwb
  rw [twoTermWave_eq_sum, fderiv_add (hwa.const_smul _) (hwb.const_smul _),
    fderiv_const_smul hwa, fderiv_const_smul hwb]
  simp only [add_apply, smul_apply]
  rw [fderiv_modulatedWave hφ ha, fderiv_modulatedWave hφ hb]
  module

/-- Second derivative of `app:ch_waves:eq:WKB-u`, retaining both exact frequency weights. -/
theorem fderiv_fderiv_twoTermWave {lam : ℝ} {φ : E → ℝ} {a b : E → F}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (x v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ (twoTermWave lam φ a b) y v) x w =
      waveCarrier lam φ x •
        (((lam : ℂ)⁻¹) ^ 2 • waveSecondAmplitude lam φ a x v w +
          ((lam : ℂ)⁻¹) ^ 3 • waveSecondAmplitude lam φ b x v w) := by
  have hwa := contDiff_modulatedWave (lam := lam) hφ ha
  have hwb := contDiff_modulatedWave (lam := lam) hφ hb
  have he : (fun y ↦ fderiv ℝ (twoTermWave lam φ a b) y v) =
      ((lam : ℂ)⁻¹) ^ 2 • (fun y ↦ fderiv ℝ (modulatedWave lam φ a) y v) +
      ((lam : ℂ)⁻¹) ^ 3 • (fun y ↦ fderiv ℝ (modulatedWave lam φ b) y v) := by
    funext y
    rw [twoTermWave_eq_sum,
      fderiv_add ((hwa.differentiable (by norm_num) y).const_smul _)
        ((hwb.differentiable (by norm_num) y).const_smul _),
      fderiv_const_smul (hwa.differentiable (by norm_num) y),
      fderiv_const_smul (hwb.differentiable (by norm_num) y)]
    rfl
  rw [he, fderiv_add ((differentiable_fderiv_apply_const hwa v x).const_smul _)
    ((differentiable_fderiv_apply_const hwb v x).const_smul _),
    fderiv_const_smul (differentiable_fderiv_apply_const hwa v x),
    fderiv_const_smul (differentiable_fderiv_apply_const hwb v x)]
  simp only [add_apply, smul_apply]
  rw [fderiv_fderiv_modulatedWave hφ ha, fderiv_fderiv_modulatedWave hφ hb]
  module

omit [IsScalarTower ℝ ℂ F] in
/-- Real first amplitude in `app:ch_waves:thm:leading`, with its exact power of `lam`. -/
theorem waveFirstAmplitude_re (lam : ℝ) (φ : E → ℝ) (a : E → F)
    (L : F →L[ℂ] ℂ) (x v : E) :
    (L (waveFirstAmplitude lam φ a x v)).re =
      -lam * fderiv ℝ φ x v * (L (a x)).im + (L (fderiv ℝ a x v)).re := by
  simp only [waveFirstAmplitude, map_add, map_smul, smul_eq_mul, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [IsScalarTower ℝ ℂ F] in
/-- Imaginary first amplitude in `app:ch_waves:thm:leading`, with its exact power of `lam`. -/
theorem waveFirstAmplitude_im (lam : ℝ) (φ : E → ℝ) (a : E → F)
    (L : F →L[ℂ] ℂ) (x v : E) :
    (L (waveFirstAmplitude lam φ a x v)).im =
      lam * fderiv ℝ φ x v * (L (a x)).re + (L (fderiv ℝ a x v)).im := by
  simp only [waveFirstAmplitude, map_add, map_smul, smul_eq_mul, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [IsScalarTower ℝ ℂ F] in
/-- Real second amplitude in `app:ch_waves:thm:wkb`, with the `lam²` and `lam` terms. -/
theorem waveSecondAmplitude_re (lam : ℝ) (φ : E → ℝ) (a : E → F)
    (L : F →L[ℂ] ℂ) (x v w : E) :
    (L (waveSecondAmplitude lam φ a x v w)).re =
      -lam ^ 2 * fderiv ℝ φ x v * fderiv ℝ φ x w * (L (a x)).re -
      lam * (fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x w * (L (a x)).im +
        fderiv ℝ φ x v * (L (fderiv ℝ a x w)).im +
        fderiv ℝ φ x w * (L (fderiv ℝ a x v)).im) +
      (L (fderiv ℝ (fun y ↦ fderiv ℝ a y v) x w)).re := by
  simp only [waveSecondAmplitude, map_add, map_smul, smul_eq_mul, pow_two,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [IsScalarTower ℝ ℂ F] in
/-- Imaginary second amplitude in `app:ch_waves:thm:wkb`, with the `lam²` and `lam` terms. -/
theorem waveSecondAmplitude_im (lam : ℝ) (φ : E → ℝ) (a : E → F)
    (L : F →L[ℂ] ℂ) (x v w : E) :
    (L (waveSecondAmplitude lam φ a x v w)).im =
      -lam ^ 2 * fderiv ℝ φ x v * fderiv ℝ φ x w * (L (a x)).im +
      lam * (fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x w * (L (a x)).re +
        fderiv ℝ φ x v * (L (fderiv ℝ a x w)).re +
        fderiv ℝ φ x w * (L (fderiv ℝ a x v)).re) +
      (L (fderiv ℝ (fun y ↦ fderiv ℝ a y v) x w)).im := by
  simp only [waveSecondAmplitude, map_add, map_smul, smul_eq_mul, pow_two,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end JanetCartan
