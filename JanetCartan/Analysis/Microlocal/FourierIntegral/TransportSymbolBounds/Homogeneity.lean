module

public import JanetCartan.Analysis.Matrix.AdjugateSymbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Masks
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Radial degrees of the transport primitives

The covector derivatives of the actual normalized adjugate have degrees minus
one and minus two. These identities supply the radial inputs to the amplitude
bounds in `app:ch_regular_base:eq:direct-graph-amplitudes`; they require neither
invertibility of the adjugate nor global smoothness at the zero covector.
-/

@[expose] public noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiating a radial identity loses one covector degree. This is used
for the two actual adjugate jets in
`app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem fderiv_transport_scaling (f : E → F) {t a : ℝ} (ht : t ≠ 0)
    (hf : ∀ ξ, f (t • ξ) = a • f ξ) (ξ : E) :
    fderiv ℝ f (t • ξ) = (t⁻¹ * a) • fderiv ℝ f ξ := by
  have hfun : (fun ζ ↦ f (t • ζ)) = fun ζ ↦ a • f ζ := funext hf
  have h := congrArg (fun g ↦ fderiv ℝ g ξ) hfun
  rw [fderiv_comp_smul] at h
  change t • fderiv ℝ f (t • ξ) = fderiv ℝ (a • f) ξ at h
  rw [fderiv_const_smul_field] at h
  have hi := congrArg (fun L ↦ t⁻¹ • L) h
  simpa only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ ht, one_smul] using hi

set_option backward.isDefEq.respectTransparency false

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The first covector jet of the normalized adjugate has degree minus one,
as used in the first term of `app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem fderiv_normalizedAdjugateSymbol_smul
    (H : E →ₗ[ℝ] Matrix m m ℝ) {t : ℝ} (ht : 0 < t) (ξ : E) :
    fderiv ℝ (normalizedAdjugateSymbol H) (t • ξ) =
      t⁻¹ • fderiv ℝ (normalizedAdjugateSymbol H) ξ := by
  simpa using fderiv_transport_scaling (F := Matrix m m ℝ)
    (normalizedAdjugateSymbol H) ht.ne'
    (a := 1) (fun ζ ↦ by simpa using normalizedAdjugateSymbol_smul H ht ζ) ξ

/-- The second covector jet has degree minus two. Together with the degree-one
phase Hessian this gives the second degree-minus-one correction term in
`app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem secondFDeriv_normalizedAdjugateSymbol_smul
    (H : E →ₗ[ℝ] Matrix m m ℝ) {t : ℝ} (ht : 0 < t) (ξ : E) :
    fderiv ℝ (fderiv ℝ (normalizedAdjugateSymbol H)) (t • ξ) =
      (t⁻¹ ^ 2) • fderiv ℝ (fderiv ℝ (normalizedAdjugateSymbol H)) ξ := by
  simpa only [pow_two] using
    fderiv_transport_scaling (F := E →L[ℝ] Matrix m m ℝ)
      (fderiv ℝ (normalizedAdjugateSymbol H)) ht.ne'
      (fderiv_normalizedAdjugateSymbol_smul H ht) ξ

variable {ι R : Type*} [Fintype ι] [Ring R] [Algebra ℂ R]

/-- The two correction terms have the same radial degree. The phase Hessian
contributes its degree one, exactly as in
`app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem correctionAmplitude_rescale (c1 dU : ι → R) (c2 : ι → ι → R)
    (S : ι → ι → ℂ) (U : R) {t : ℂ} (ht : t ≠ 0) :
    correctionAmplitude (fun j ↦ t⁻¹ • c1 j) dU
      (fun j l ↦ (t⁻¹ ^ 2) • c2 j l) (fun j l ↦ t * S j l) U =
      t⁻¹ • correctionAmplitude c1 dU c2 S U := by
  have hscale (z : ℂ) : (t * z) * t⁻¹ ^ 2 = t⁻¹ * z := by
    field_simp
  have hterm (j l : ι) : (t * S j l) • (((t⁻¹ ^ 2) • c2 j l) * U) =
      t⁻¹ • (S j l • (c2 j l * U)) := by
    rw [smul_mul_assoc, smul_smul, hscale, smul_smul]
  simp only [correctionAmplitude]
  simp_rw [hterm]
  simp only [smul_mul_assoc, ← Finset.smul_sum, smul_sub]
  congr 1 <;> apply smul_comm

/-- Multiplication by the physical coefficients retains the radial degree of
both terms of the complete remainder, including `B b₋₁`
(`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem transportRemainder_rescale (A db : ι → R) (B b : R) (t : ℂ) :
    transportRemainder A (fun j ↦ t • db j) B (t • b) =
      t • transportRemainder A db B b := by
  simp only [transportRemainder, mul_smul_comm, ← Finset.smul_sum,
    ← smul_add, smul_smul]
  rw [mul_comm]

end JanetCartan.FourierIntegral
