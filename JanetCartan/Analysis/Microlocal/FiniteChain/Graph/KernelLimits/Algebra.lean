module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Kernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Regularized joint graph integrands

Literal integrands for `app:ch_regular:eq:joint-kernel-phase`. Frequencies in
`regularizedJointAmplitude` are physical. In the reverse orientation the original
amplitude positions remain `(u,z)`, although the input and output are reversed.
The complementary output factor includes the identity. These definitions alone
make no assertion about the unregularized oscillatory operator.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}

/-- The three Fourier measures in `app:ch_regular:eq:joint-kernel-phase`. -/
def jointNormalization (n : ℕ) : ℂ := ((2 * Real.pi) ^ (3 * n) : ℂ)⁻¹

/-- Multiplication of the three literal operator normalizations in
`app:ch_regular:eq:joint-kernel-phase`. -/
theorem jointNormalization_eq_cube (n : ℕ) :
    jointNormalization n = (((2 * Real.pi) ^ n : ℂ)⁻¹) ^ 3 := by
  simp only [jointNormalization, mul_comm 3 n, pow_mul, inv_pow]

/-- The physical-covector amplitude of `app:ch_regular:eq:joint-kernel-phase`.
The source shoulder belongs to `mi`; neither amplitude position is frozen. -/
def regularizedJointAmplitude (A : FullAmplitude n r) (mi mo : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (p : JointVariables (Euclidean n)) : Matrix (Fin r) (Fin r) ℂ :=
  ((χA p.2.1 * χo p.2.2.2 * (1 - mo (x, p.2.2.2)) * mi (y, p.2.2.1) : ℝ) : ℂ) •
    A p.1.1 p.1.2 p.2.1

/-- Matrix-valued joint integrand for both orientations in
`app:ch_regular:eq:joint-kernel-phase`. -/
def regularizedJointIntegrand (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (p : JointVariables (Euclidean n)) : Matrix (Fin r) (Fin r) ℂ :=
  Complex.exp (Complex.I * (jointPhase backward S x y p : ℂ)) •
    regularizedJointAmplitude A mi mo χA χo x y p

/-- The joint matrix kernel before removal of the frequency cutoffs
(`app:ch_regular:eq:joint-kernel-phase`). -/
def regularizedJointKernel (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  jointNormalization n • ∫ p, regularizedJointIntegrand backward S A mi mo χA χo x y p

/-- The three forward oscillations multiply to the full joint phase;
consumer: the literal composition in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem forward_oscillation_product (S : Euclidean n → Euclidean n → ℝ)
    (x y u z ξ η ζ : Euclidean n) :
    graphOscillation (fun a b => inner ℝ a b) x u ζ *
      graphOscillation S u z ξ * graphOscillation (fun a b => inner ℝ a b) z y η =
      Complex.exp (Complex.I * (forwardPhase S x y u z ξ η ζ : ℂ)) := by
  simp only [graphOscillation, ← Complex.exp_add]
  congr 1
  simp only [forwardPhase, inner_sub_left, Complex.ofReal_add, Complex.ofReal_sub]
  ring

/-- Literal reversal conjugates only the graph oscillation and exchanges the
intermediate input/output positions (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem reverse_oscillation_product (S : Euclidean n → Euclidean n → ℝ)
    (x y u z ξ η ζ : Euclidean n) :
    graphOscillation (fun a b => inner ℝ a b) x z ζ *
      star (graphOscillation S u z ξ) *
      graphOscillation (fun a b => inner ℝ a b) u y η =
      Complex.exp (Complex.I * (reversePhase S x y u z ξ η ζ : ℂ)) := by
  simp only [graphOscillation, RCLike.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  simp only [reversePhase, inner_sub_left, Complex.ofReal_add, Complex.ofReal_sub]
  ring

/-- Scaling the three physical covectors recovers exactly the published full
amplitude, including `1-mo` (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointAmplitude_rescale (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) {ρ : ℝ} (hρ : ρ ≠ 0) (p : JointVariables (Euclidean n)) :
    regularizedJointAmplitude A (fun q => mi (q.1, ρ⁻¹ • q.2))
      (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo x y (p.1, ρ • p.2) =
      jointAmplitude ρ A mi mo χA χo x y p := by
  simp [regularizedJointAmplitude, jointAmplitude, smul_smul, hρ]

/-- Rescaling acts only on the three frequency variables, with either literal
orientation (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointPhase_rescale (backward : Bool) (S φ : Euclidean n → Euclidean n → ℝ)
    (x y : Euclidean n) (ρ : ℝ) (p : JointVariables (Euclidean n))
    (hφ : S p.1.1 (ρ • p.2.1) = ρ * φ p.1.1 p.2.1) :
    jointPhase backward S x y (p.1, ρ • p.2) = ρ * jointPhase backward φ x y p := by
  cases backward
  · exact forwardPhase_rescale S φ ρ x y _ _ _ _ _ hφ
  · exact reversePhase_rescale S φ ρ x y _ _ _ _ _ hφ

end JanetCartan.FiniteChain.Graph.KernelLimits
