module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Operator
import Mathlib.Tactic.Module

/-!
# Exact ambient WKB amplitudes

The polynomial obtained from `app:ch_waves:eq:exact-W-amplitude`, and the
exact derivative-amplitude difference in `app:ch_waves:eq:WKB-amplitude-difference`.
The formulas retain all powers through `λ⁻³`. They assert identities, not the
uniform graded bounds or existence of geometric reconstruction data.
-/

@[expose] public noncomputable section

namespace JanetCartan.WKB

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The displacement amplitude after substituting `b₀ + λ⁻¹ b₁` in
`app:ch_waves:eq:exact-W-amplitude`. -/
def reconstructionAmplitude (lam : ℝ) (ν₀ ν₁ V₀ V₁ : E → F) (x : E) : F :=
  (Complex.I * (lam : ℂ)⁻¹) • ν₀ x +
    ((lam : ℂ)⁻¹)^2 • (V₀ x + Complex.I • ν₁ x) + ((lam : ℂ)⁻¹)^3 • V₁ x

/-- Pointwise regularity needed for `app:ch_waves:eq:WKB-amplitude-difference`. -/
theorem differentiableAt_reconstructionAmplitude {lam : ℝ} {ν₀ ν₁ V₀ V₁ : E → F}
    {x : E} (hν₀ : DifferentiableAt ℝ ν₀ x) (hν₁ : DifferentiableAt ℝ ν₁ x)
    (hV₀ : DifferentiableAt ℝ V₀ x) (hV₁ : DifferentiableAt ℝ V₁ x) :
    DifferentiableAt ℝ (reconstructionAmplitude lam ν₀ ν₁ V₀ V₁) x :=
  ((hν₀.const_smul _).add ((hV₀.add (hν₁.const_smul _)).const_smul _)).add
    (hV₁.const_smul _)

/-- The derivative of the polynomial amplitude in `app:ch_waves:eq:exact-W-amplitude`. -/
theorem fderiv_reconstructionAmplitude {lam : ℝ} {ν₀ ν₁ V₀ V₁ : E → F}
    {x : E} (hν₀ : DifferentiableAt ℝ ν₀ x) (hν₁ : DifferentiableAt ℝ ν₁ x)
    (hV₀ : DifferentiableAt ℝ V₀ x) (hV₁ : DifferentiableAt ℝ V₁ x) (v : E) :
    fderiv ℝ (reconstructionAmplitude lam ν₀ ν₁ V₀ V₁) x v =
      (Complex.I * (lam : ℂ)⁻¹) • fderiv ℝ ν₀ x v +
        ((lam : ℂ)⁻¹)^2 • (fderiv ℝ V₀ x v + Complex.I • fderiv ℝ ν₁ x v) +
        ((lam : ℂ)⁻¹)^3 • fderiv ℝ V₁ x v := by
  exact congrArg (fun D : E →L[ℝ] F ↦ D v)
    ((((hν₀.hasFDerivAt.const_smul _).add
      ((hV₀.hasFDerivAt.add (hν₁.hasFDerivAt.const_smul _)).const_smul _)).add
      (hV₁.hasFDerivAt.const_smul _)).fderiv)

/-- The leading tensor `A₀ = -ν₀ ⊗ dφ` in
`app:ch_waves:eq:arbitrary-b-amplitudes`, evaluated in a direction. -/
def leadingDerivativeAmplitude (φ : E → ℝ) (ν : E → F) (x v : E) : F :=
  -(fderiv ℝ φ x v : ℂ) • ν x

/-- The exact coefficient of `λ⁻¹` in `app:ch_waves:eq:WKB-amplitude-difference`. -/
def derivativeCorrection₁ (φ : E → ℝ) (ν₀ ν₁ V₀ : E → F) (x v : E) : F :=
  -(fderiv ℝ φ x v : ℂ) • ν₁ x +
    Complex.I • ((fderiv ℝ φ x v : ℂ) • V₀ x + fderiv ℝ ν₀ x v)

/-- The exact coefficient of `λ⁻²` in `app:ch_waves:eq:WKB-amplitude-difference`. -/
def derivativeCorrection₂ (φ : E → ℝ) (ν₁ V₀ V₁ : E → F) (x v : E) : F :=
  Complex.I • ((fderiv ℝ φ x v : ℂ) • V₁ x + fderiv ℝ ν₁ x v) + fderiv ℝ V₀ x v

/-- Exact demodulated ambient derivative, including the `λ⁻³` term,
underlying `app:ch_waves:eq:WKB-amplitude-difference`. -/
theorem derivative_expansion {lam : ℝ} (hlam : lam ≠ 0)
    {φ : E → ℝ} {ν₀ ν₁ V₀ V₁ : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x)
    (hν₀ : DifferentiableAt ℝ ν₀ x) (hν₁ : DifferentiableAt ℝ ν₁ x)
    (hV₀ : DifferentiableAt ℝ V₀ x) (hV₁ : DifferentiableAt ℝ V₁ x) (v : E) :
    waveCarrier (-lam) φ x •
      fderiv ℝ (modulatedWave lam φ (reconstructionAmplitude lam ν₀ ν₁ V₀ V₁)) x v =
    leadingDerivativeAmplitude φ ν₀ x v +
      (lam : ℂ)⁻¹ • derivativeCorrection₁ φ ν₀ ν₁ V₀ x v +
      ((lam : ℂ)⁻¹)^2 • derivativeCorrection₂ φ ν₁ V₀ V₁ x v +
      ((lam : ℂ)⁻¹)^3 • fderiv ℝ V₁ x v := by
  rw [demodulated_fderiv_modulatedWave hφ
    (differentiableAt_reconstructionAmplitude hν₀ hν₁ hV₀ hV₁)]
  rw [waveFirstAmplitude, fderiv_reconstructionAmplitude hν₀ hν₁ hV₀ hV₁]
  unfold reconstructionAmplitude leadingDerivativeAmplitude derivativeCorrection₁ derivativeCorrection₂
  have hc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have h₀ : (Complex.I * (lam : ℂ) * (fderiv ℝ φ x v : ℂ)) *
      (Complex.I * (lam : ℂ)⁻¹) = -(fderiv ℝ φ x v : ℂ) := by
    field_simp
    linear_combination (fderiv ℝ φ x v : ℂ) * Complex.I_sq
  have h₁ : (Complex.I * (lam : ℂ) * (fderiv ℝ φ x v : ℂ)) *
      ((lam : ℂ)⁻¹)^2 = (lam : ℂ)⁻¹ * (Complex.I * (fderiv ℝ φ x v : ℂ)) := by
    field_simp
  have h₂ : (Complex.I * (lam : ℂ) * (fderiv ℝ φ x v : ℂ)) *
      ((lam : ℂ)⁻¹)^3 = ((lam : ℂ)⁻¹)^2 * (Complex.I * (fderiv ℝ φ x v : ℂ)) := by
    field_simp
  have h₁i : (Complex.I * (lam : ℂ) * (fderiv ℝ φ x v : ℂ)) *
      (((lam : ℂ)⁻¹)^2 * Complex.I) = -((fderiv ℝ φ x v : ℂ) * (lam : ℂ)⁻¹) := by
    field_simp
    linear_combination (fderiv ℝ φ x v : ℂ) * Complex.I_sq
  simp only [smul_add, smul_smul, h₀, h₁, h₂, h₁i]
  module

/-- Factoring one inverse frequency out of the exact derivative error in
`app:ch_waves:eq:WKB-amplitude-difference`. Bounds on the displayed coefficients
are separate analytic inputs. -/
theorem derivative_amplitude_difference {lam : ℝ} (hlam : lam ≠ 0)
    {φ : E → ℝ} {ν₀ ν₁ V₀ V₁ : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x)
    (hν₀ : DifferentiableAt ℝ ν₀ x) (hν₁ : DifferentiableAt ℝ ν₁ x)
    (hV₀ : DifferentiableAt ℝ V₀ x) (hV₁ : DifferentiableAt ℝ V₁ x) (v : E) :
    waveCarrier (-lam) φ x •
      fderiv ℝ (modulatedWave lam φ (reconstructionAmplitude lam ν₀ ν₁ V₀ V₁)) x v -
        leadingDerivativeAmplitude φ ν₀ x v =
    (lam : ℂ)⁻¹ • (derivativeCorrection₁ φ ν₀ ν₁ V₀ x v +
      (lam : ℂ)⁻¹ • derivativeCorrection₂ φ ν₁ V₀ V₁ x v +
      ((lam : ℂ)⁻¹)^2 • fderiv ℝ V₁ x v) := by
  rw [derivative_expansion hlam hφ hν₀ hν₁ hV₀ hV₁]
  module

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- Applying any first-order ambient reconstruction to the actual two-term
wave gives exactly the polynomial from `app:ch_waves:eq:exact-W-amplitude`.
Specializing the coefficients to the geometric reconstruction remains an input. -/
theorem firstOrder_reconstruction_twoTermWave {n : ℕ} {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A]
    (C : Euclidean n → Fin n → A →ₗ[ℂ] F) (D : Euclidean n → A →ₗ[ℂ] F)
    {lam : ℝ} (hlam : lam ≠ 0) {φ : Euclidean n → ℝ} {a b : Euclidean n → A}
    (hφ : Differentiable ℝ φ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    firstOrderApply C D (twoTermWave lam φ a b) =
      modulatedWave lam φ (reconstructionAmplitude lam
        (fun x ↦ principalSymbol C φ x (a x)) (fun x ↦ principalSymbol C φ x (b x))
        (firstOrderApply C D a) (firstOrderApply C D b)) := by
  funext x
  rw [firstOrder_twoTermWave_expansion C D hlam (hφ x) (ha x) (hb x)]
  simp only [modulatedWave, reconstructionAmplitude]
  module

/-- The exact derivative-amplitude difference for the reconstructed primary
field itself (`app:ch_waves:eq:WKB-amplitude-difference`). The four regularity
inputs concern the normal and reconstructed amplitudes, not the desired error. -/
theorem firstOrder_reconstruction_amplitude_difference {n : ℕ} {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A]
    (C : Euclidean n → Fin n → A →ₗ[ℂ] F) (D : Euclidean n → A →ₗ[ℂ] F)
    {lam : ℝ} (hlam : lam ≠ 0) {φ : Euclidean n → ℝ} {a b : Euclidean n → A}
    (hφ : Differentiable ℝ φ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x v : Euclidean n)
    (hν₀ : DifferentiableAt ℝ (fun y ↦ principalSymbol C φ y (a y)) x)
    (hν₁ : DifferentiableAt ℝ (fun y ↦ principalSymbol C φ y (b y)) x)
    (hV₀ : DifferentiableAt ℝ (firstOrderApply C D a) x)
    (hV₁ : DifferentiableAt ℝ (firstOrderApply C D b) x) :
    let ν₀ := fun y ↦ principalSymbol C φ y (a y)
    let ν₁ := fun y ↦ principalSymbol C φ y (b y)
    let V₀ := firstOrderApply C D a
    let V₁ := firstOrderApply C D b
    waveCarrier (-lam) φ x •
      fderiv ℝ (firstOrderApply C D (twoTermWave lam φ a b)) x v -
        leadingDerivativeAmplitude φ ν₀ x v =
    (lam : ℂ)⁻¹ • (derivativeCorrection₁ φ ν₀ ν₁ V₀ x v +
      (lam : ℂ)⁻¹ • derivativeCorrection₂ φ ν₁ V₀ V₁ x v +
      ((lam : ℂ)⁻¹)^2 • fderiv ℝ V₁ x v) := by
  dsimp only
  rw [firstOrder_reconstruction_twoTermWave C D hlam hφ ha hb]
  exact derivative_amplitude_difference hlam (hφ x) hν₀ hν₁ hV₀ hV₁ v

end JanetCartan.WKB
