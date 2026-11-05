module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.FrequencyCutoff

/-!
# Literal reverse kernels in original coordinates

The reverse integral for `app:ch_regular_base:eq:actual-adjoint-trade` keeps the
original `(x,y,η)` order. Its initial amplitude is `A x y η |>.conjTranspose`;
the later transferred amplitudes are already reverse amplitudes. Identifying
this integral with the Hilbert adjoint requires the separate kernel-pairing
argument and is not asserted by the definition.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Normalized literal reverse integral, with output `y` and source `x`.
Initialize `C` with the conjugate transpose of the full forward amplitude.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
def reverseGraphOperator (S : Euclidean n → Euclidean n → ℝ)
    (C : FullAmplitude n r) (v : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) : Fin r → ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ η, ∫ x, star (graphOscillation S x y η) • (C x y η).mulVec (v x)

/-- Source masks stay in the original `x` position of the reverse amplitude.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem reverseGraphOperator_source_mul
    (S : Euclidean n → Euclidean n → ℝ) (C : FullAmplitude n r)
    (b : Euclidean n → ℂ) (v : Euclidean n → Fin r → ℂ) :
    reverseGraphOperator S C (fun x ↦ b x • v x) =
      reverseGraphOperator S (fun x y η ↦ b x • C x y η) v := by
  funext y
  simp only [reverseGraphOperator, Matrix.mulVec_smul, Matrix.smul_mulVec]

/-- Output masks stay in the original `y` position of the reverse amplitude.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem reverseGraphOperator_target_mul
    (S : Euclidean n → Euclidean n → ℝ) (C : FullAmplitude n r)
    (b : Euclidean n → ℂ) (v : Euclidean n → Fin r → ℂ) (y : Euclidean n) :
    reverseGraphOperator S (fun x y η ↦ b y • C x y η) v y =
      b y • reverseGraphOperator S C v y := by
  simp only [reverseGraphOperator, Matrix.smul_mulVec,
    smul_comm (star (graphOscillation S _ _ _)), integral_smul, smul_comm _ (b y)]

/-- Literal adjunction conjugates the frequency cutoff exactly once, along with
the initial amplitude. Subsequent reverse transfers use this amplitude without
further conjugation (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem frequencyCutFullAmplitude_conjTranspose
    (χ : Euclidean n → ℂ) (A : FullAmplitude n r) :
    (fun x y η ↦ (frequencyCutFullAmplitude χ A x y η).conjTranspose) =
      frequencyCutFullAmplitude (fun η ↦ star (χ η))
        (fun x y η ↦ (A x y η).conjTranspose) := by
  funext x y η
  simp [frequencyCutFullAmplitude]

end JanetCartan.FourierIntegral
