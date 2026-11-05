module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Transport
public import Mathlib.Analysis.Matrix.Normed

/-!
# Pointwise bounds for the literal transport amplitudes

The norm estimates in `app:ch_regular_base:eq:direct-graph-amplitudes` and
`app:ch_regular_base:eq:direct-graph-identity`. All products retain their order.
The hypotheses permit the Frobenius matrix norm; the identity is never assigned
norm one. These estimates are prerequisites for the joint derivative estimates
consumed by the finite graph calculus, not assertions of symbol seminorm bounds.
-/

@[expose] public noncomputable section

open scoped BigOperators
namespace JanetCartan.FourierIntegral
variable {ι R : Type*} [Fintype ι] [NormedRing R] [NormedAlgebra ℂ R]

omit [NormedAlgebra ℂ R] in
/-- The leading product in `app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem norm_leadingAmplitude_le (c U : R) :
    ‖leadingAmplitude c U‖ ≤ ‖c‖ * ‖U‖ := norm_mul_le c U

/-- Both terms of `b₋₁`, with the literal coefficient `1/2`, from
`app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem norm_correctionAmplitude_le (c1 dU : ι → R) (c2 : ι → ι → R)
    (S : ι → ι → ℂ) (U : R) :
    ‖correctionAmplitude c1 dU c2 S U‖ ≤
      (∑ j, ‖c1 j‖ * ‖dU j‖) +
        (1 / 2 : ℝ) * ∑ j, ∑ l, ‖S j l‖ * (‖c2 j l‖ * ‖U‖) := by
  have hfirst : ‖∑ j, c1 j * dU j‖ ≤ ∑ j, ‖c1 j‖ * ‖dU j‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ norm_mul_le _ _)
  have hsecond : ‖∑ j, ∑ l, S j l • (c2 j l * U)‖ ≤
      ∑ j, ∑ l, ‖S j l‖ * (‖c2 j l‖ * ‖U‖) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
  unfold correctionAmplitude
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, norm_neg, Complex.norm_I, norm_div, Complex.norm_ofNat,
    one_mul]
  exact add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by norm_num))

/-- The complete remainder bound includes `B b₋₁`, as required by
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem norm_transportRemainder_le (A db : ι → R) (B b : R) :
    ‖transportRemainder A db B b‖ ≤
      (∑ j, ‖A j‖ * ‖db j‖) + ‖B‖ * ‖b‖ := by
  simp only [transportRemainder, norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ norm_mul_le _ _))
    (norm_mul_le _ _))

/-- Fixed source, target and angle masks in the graph amplitude of
`app:ch_regular_base:thm:actual-calculus`, Step 5, are all retained. -/
def maskedTransportAmplitude (χt χs χg : ℂ) (b : R) : R :=
  χt • (χs • (χg • b))

/-- The exact pointwise mask contribution for
`app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem norm_maskedTransportAmplitude (χt χs χg : ℂ) (b : R) :
    ‖maskedTransportAmplitude χt χs χg b‖ =
      ‖χt‖ * (‖χs‖ * (‖χg‖ * ‖b‖)) := by
  simp only [maskedTransportAmplitude, norm_smul]

section Matrices
open scoped Matrix.Norms.Frobenius
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Literal matrix adjunction preserves the Frobenius bound, including all
three masks (`app:ch_regular_base:eq:actual-one-high`, order zero). -/
theorem norm_maskedTransportAmplitude_conjTranspose (χt χs χg : ℂ)
    (b : Matrix m m ℂ) :
    ‖(maskedTransportAmplitude χt χs χg b).conjTranspose‖ =
      ‖χt‖ * (‖χs‖ * (‖χg‖ * ‖b‖)) := by
  rw [Matrix.frobenius_norm_conjTranspose, norm_maskedTransportAmplitude]

/-- Entrywise conjugation preserves the same Frobenius bound
(`app:ch_regular_base:eq:actual-one-high`, order zero). -/
theorem norm_maskedTransportAmplitude_conjugate (χt χs χg : ℂ)
    (b : Matrix m m ℂ) :
    ‖(maskedTransportAmplitude χt χs χg b).map star‖ =
      ‖χt‖ * (‖χs‖ * (‖χg‖ * ‖b‖)) := by
  rw [Matrix.frobenius_norm_map_eq _ _ norm_star, norm_maskedTransportAmplitude]
end Matrices
end JanetCartan.FourierIntegral
