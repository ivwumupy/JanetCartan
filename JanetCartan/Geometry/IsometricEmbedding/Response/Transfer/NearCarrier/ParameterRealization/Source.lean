module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Kernel

/-!
# Source integration for the parameter phase contribution

The signed source step in `app:ch_response:eq:direct-envelope-profile`.
Forward coefficients are independent of the source position. Reverse
coefficients are `C B⁻¹`; their entire source derivative must be retained.
Compact support removes the boundary terms. These statements concern the
literal source integral, before frequency integration and L² completion.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.NearCarrierParameter

open FourierIntegral ReverseDerivative
variable {n r : ℕ}

/-- The forward parameter phase contribution transfers with a positive sign.
Here `C` is the row of `phaseCoefficient` at fixed output and covector.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem integral_forward_parameter_phase
    (Φ : Euclidean n → Euclidean n → ℝ) (x δ : Euclidean n) (C : Fin n → ℝ)
    (g : Euclidean n → Fin r → ℂ) (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    (∫ y, ((Complex.I * ((∑ l, C l * δ l : ℝ) : ℂ)) *
        graphOscillation Φ x y δ) • g y) =
      ∑ l, ∫ y, graphOscillation Φ x y δ • ((C l : ℂ) • partialDeriv g y l) := by
  have hc : Complex.I * ((∑ l, C l * δ l : ℝ) : ℂ) =
      ∑ l, (C l : ℂ) * (Complex.I * (δ l : ℂ)) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  conv_lhs => arg 2; ext y; rw [mul_smul]
  rw [integral_smul, hc, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_smul, graphOscillation_source_integration_by_parts Φ x δ l g hg hgs]
  simp_rw [smul_comm (graphOscillation Φ x _ δ) (C l : ℂ), integral_smul]

/-- The reverse coefficient row is `C B⁻¹`, in that order. Its negative is the
datum amplitude coefficient. Source: `app:ch_response:eq:direct-envelope-profile`. -/
def reverseCoefficient (C : Euclidean n → Fin n → ℝ)
    (J : Euclidean n → Matrix (Fin n) (Fin n) ℝ) (x : Euclidean n) : Fin n → ℝ :=
  Matrix.vecMul (C x) (J x)

/-- Algebraic cancellation of the averaged mixed matrix against its supplied
inverse. The phase coefficient is a row, not a column.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseCoefficient_dot_gradient
    (C : Euclidean n → Fin n → ℝ)
    (B J : Euclidean n → Matrix (Fin n) (Fin n) ℝ) (x δ : Euclidean n)
    (hJB : J x * B x = 1) :
    ∑ l, reverseCoefficient C J x l * (B x).mulVec (fun k ↦ δ k) l =
      ∑ l, C x l * δ l := by
  change dotProduct (Matrix.vecMul (C x) (J x)) ((B x).mulVec (fun k ↦ δ k)) = _
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hJB, Matrix.vecMul_one]
  rfl

/-- Reverse parameter phase multiplication is the positive source derivative
combination before integration by parts. Integration then supplies the minus
sign. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverse_parameter_phase_trade
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y x δ : Euclidean n) (C : Euclidean n → Fin n → ℝ)
    (B J : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hJB : J x * B x = 1)
    (hS : DifferentiableAt ℝ (fun z ↦ phaseIncrement S ζ ρ z δ) x)
    (hgrad : ∀ l, partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
      (B x).mulVec (fun k ↦ δ k) l) :
    -((Complex.I * ((∑ l, C x l * δ l : ℝ) : ℂ)) * oscillation S ζ ρ y x δ) =
      ∑ l, (reverseCoefficient C J x l : ℂ) *
        partialDeriv (fun z ↦ oscillation S ζ ρ y z δ) x l := by
  simp_rw [partialDeriv_oscillation_source S ζ ρ y x δ _ hS, hgrad]
  rw [← reverseCoefficient_dot_gradient C B J x δ hJB]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_neg_distrib, mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The literal reverse source integration by parts has a negative divergence
of `C B⁻¹ g`. Invertibility and the spatial phase identity are needed only on
the support of `g`. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem integral_reverse_parameter_phase
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y δ : Euclidean n) (C : Euclidean n → Fin n → ℝ)
    (B J : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (g : Euclidean n → Fin r → ℂ)
    (hS : ContDiff ℝ ∞ (fun x ↦ phaseIncrement S ζ ρ x δ))
    (hC : ∀ j, ContDiff ℝ ∞ (fun x ↦ C x j))
    (hJ : ∀ j l, ContDiff ℝ ∞ (fun x ↦ J x j l))
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g)
    (hJB : ∀ x ∈ tsupport g, J x * B x = 1)
    (hgrad : ∀ x ∈ tsupport g, ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x).mulVec (fun k ↦ δ k) l) :
    (∫ x, (-((Complex.I * ((∑ l, C x l * δ l : ℝ) : ℂ)) *
        oscillation S ζ ρ y x δ)) • g x) =
      -∑ l, ∫ x, oscillation S ζ ρ y x δ •
        partialDeriv (fun z ↦ (reverseCoefficient C J z l : ℂ) • g z) x l := by
  let e := fun x ↦ oscillation S ζ ρ y x δ
  let G := fun l x ↦ (reverseCoefficient C J x l : ℂ) • g x
  have he : ContDiff ℝ ∞ e :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub hS))).cexp
  have hR (l : Fin n) : ContDiff ℝ ∞ (fun x ↦ reverseCoefficient C J x l) := by
    change ContDiff ℝ ∞ (fun x ↦ ∑ j, C x j * J x j l)
    exact ContDiff.sum (fun j _ ↦ (hC j).mul (hJ j l))
  have hG (l : Fin n) : ContDiff ℝ ∞ (G l) :=
    (Complex.ofRealCLM.contDiff.comp (hR l)).smul hg
  have hsG (l : Fin n) : HasCompactSupport (G l) :=
    hgs.smul_left (f := fun x ↦ (reverseCoefficient C J x l : ℂ))
  have hi (l : Fin n) : Integrable (fun x ↦ partialDeriv e x l • G l x) :=
    (((he.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      (hG l).continuous).integrable_of_hasCompactSupport
        ((hsG l).smul_left (f := fun x ↦ partialDeriv e x l))
  have hibp (l : Fin n) :
      (∫ x, partialDeriv e x l • G l x) = -(∫ x, e x • partialDeriv (G l) x l) := by
    have h : (∫ x, e x • partialDeriv (G l) x l) =
        -(∫ x, partialDeriv e x l • G l x) := by
      apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hi l)
      · exact (he.continuous.smul (((hG l).continuous_fderiv (by simp)).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
            (((hsG l).fderiv_apply ℝ _).smul_left (f := e))
      · exact (he.continuous.smul (hG l).continuous).integrable_of_hasCompactSupport
          ((hsG l).smul_left (f := e))
      · exact fun x _ ↦ he.differentiable (by simp) x
      · exact fun x _ ↦ (hG l).differentiable (by simp) x
    exact neg_eq_iff_eq_neg.mp h.symm
  calc
    _ = ∫ x, ∑ l, partialDeriv e x l • G l x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport g
      · rw [reverse_parameter_phase_trade S ζ ρ y x δ C B J (hJB x hx)
          (hS.differentiable (by simp) x) (hgrad x hx), Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro l _
        simp only [G, e, smul_smul, mul_comm]
      · simp only [image_eq_zero_of_notMem_tsupport hx, smul_zero, G,
          Finset.sum_const_zero]
    _ = ∑ l, ∫ x, partialDeriv e x l • G l x :=
      integral_finsetSum _ (fun l _ ↦ hi l)
    _ = _ := by simp only [hibp, Finset.sum_neg_distrib, G, e]

/-- Leibniz expansion of the full reverse source divergence. Applied with
`R = C B⁻¹`, it retains the derivative of the inverse matrix and of every
source cutoff. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem partialDeriv_coefficient_matrixAction
    (R : Euclidean n → ℝ) (a : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : Euclidean n → Fin r → ℂ) (x : Euclidean n) (l : Fin n)
    (hR : DifferentiableAt ℝ R x) (ha : DifferentiableAt ℝ a x)
    (hu : DifferentiableAt ℝ u x) :
    partialDeriv (fun z ↦ (R z : ℂ) • (a z).mulVec (u z)) x l =
      ((R x : ℂ) • a x).mulVec (partialDeriv u x l) +
        (partialDeriv (fun z ↦ (R z : ℂ) • a z) x l).mulVec (u x) := by
  simp_rw [← Matrix.smul_mulVec]
  exact ReverseDerivative.partialDeriv_matrix_mulVec _ u x l
    ((Complex.ofRealCLM.differentiableAt.comp x hR).smul ha) hu

end JanetCartan.ResponseTransfer.NearCarrierParameter
