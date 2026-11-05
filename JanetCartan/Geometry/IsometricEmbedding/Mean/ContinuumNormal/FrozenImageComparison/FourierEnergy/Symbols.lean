module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Model

/-!
# The frozen image channel symbol and its normal

The finite-dimensional algebra in `paper-v2.tex`,
`app:ch_background:prop:bg-frame`, identifies the literal differentiated Bessel
symbols with the physical-frequency normal matrix. All identities include
dimension zero and arbitrary constant real coefficient arrays. The consumer is
the real adjoint energy identity in `FrozenImageComparison.FourierEnergy`.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The matrix of the literal differentiated Bessel symbols in the frozen channel
(`app:ch_background:prop:bg-frame`). Its frequency variable is Mathlib's `ξ`;
the differentiated symbols themselves use the physical frequency `2πξ`. -/
def uncutChannelMatrix (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ ∑ a, (A a i j : ℂ) * imageDerivativeBesselSymbol a ξ

/-- Fiber action of the actual frozen channel symbol, for the multiplier
identification in `app:ch_background:prop:bg-frame`. -/
def uncutChannelAction (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E)
    (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 ((uncutChannelMatrix A ξ).mulVec v)

/-- Conjugate-transpose fiber action, consumed by the literal adjoint Fourier
identity and its Plancherel norm in `app:ch_background:prop:bg-frame`. -/
def uncutChannelAdjointAction (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E)
    (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 ((uncutChannelMatrix A ξ).conjTranspose.mulVec v)

/-- The frozen channel has symbol `i M(2πξ) / ⟨2πξ⟩`
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
theorem uncutChannelMatrix_apply (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E)
    (i j : Fin n) :
    uncutChannelMatrix A ξ i j = Complex.I * (imageBesselSymbol ξ : ℂ) *
      (principalMatrix A ((2 * Real.pi) • ξ) i j : ℂ) := by
  simp only [uncutChannelMatrix, imageDerivativeBesselSymbol, principalMatrix,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The channel symbol times its conjugate transpose is exactly the specified
normal matrix, with no Fourier normalization loss
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
theorem uncutChannelMatrix_mul_conjTranspose
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E) :
    uncutChannelMatrix A ξ * (uncutChannelMatrix A ξ).conjTranspose =
      (normalMatrix A ((2 * Real.pi) • ξ)).map Complex.ofReal := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, uncutChannelMatrix_apply,
    Complex.star_def, map_mul, Complex.conj_I,
    Complex.conj_ofReal, normalMatrix, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.transpose_apply, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hq := congrArg Complex.ofReal (imageBesselSymbol_sq ξ)
  simp only [Complex.ofReal_mul] at hq
  calc
    _ = ((imageBesselSymbol ξ : ℂ) * (imageBesselSymbol ξ : ℂ)) *
        ((principalMatrix A ((2 * Real.pi) • ξ) i l : ℂ) *
          (principalMatrix A ((2 * Real.pi) • ξ) j l : ℂ)) := by
      calc
        _ = -(Complex.I * Complex.I) *
            ((imageBesselSymbol ξ : ℂ) * (imageBesselSymbol ξ : ℂ)) *
            ((principalMatrix A ((2 * Real.pi) • ξ) i l : ℂ) *
              (principalMatrix A ((2 * Real.pi) • ξ) j l : ℂ)) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    _ = _ := by rw [hq]

/-- The normal fiber action factors through the channel and its adjoint
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem normalComplexAction_eq_uncutChannelAction_adjoint
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E)
    (v : EuclideanSpace ℂ (Fin n)) :
    normalComplexAction A ((2 * Real.pi) • ξ) v =
      uncutChannelAction A ξ (uncutChannelAdjointAction A ξ v) := by
  simp only [normalComplexAction, uncutChannelAction, uncutChannelAdjointAction]
  rw [← uncutChannelMatrix_mul_conjTranspose, ← Matrix.mulVec_mulVec]

/-- The complex normal pairing is the real squared adjoint-symbol norm.
This is the pointwise algebra needed by
`norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy`
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem inner_normalComplexAction_eq_norm_sq
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E)
    (v : EuclideanSpace ℂ (Fin n)) :
    inner ℂ v (normalComplexAction A ((2 * Real.pi) • ξ) v) =
      (‖uncutChannelAdjointAction A ξ v‖ ^ 2 : ℝ) := by
  calc
    _ = inner ℂ (uncutChannelAdjointAction A ξ v)
        (uncutChannelAdjointAction A ξ v) := by
      rw [normalComplexAction_eq_uncutChannelAction_adjoint]
      simp only [uncutChannelAction, uncutChannelAdjointAction,
        EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
        Matrix.conjTranspose_conjTranspose, dotProduct_comm]
    _ = _ := by
      simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rfl

/-- Taking the real part preserves the exact squared adjoint-symbol norm
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem re_inner_normalComplexAction_eq_norm_sq
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (ξ : E)
    (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ v (normalComplexAction A ((2 * Real.pi) • ξ) v)).re =
      ‖uncutChannelAdjointAction A ξ v‖ ^ 2 := by
  rw [inner_normalComplexAction_eq_norm_sq, Complex.ofReal_re]

end JanetCartan.ContinuumNormal.FrozenImageComparison
