module

public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Real-matrix adapter for the Euclidean frozen energy

The real quadratic positivity supplied by the frozen model in
`paper-v2.tex`, `app:ch_background:prop:bg-frame`, applies to both quadratures
of a complex Fourier vector. This module reuses the shared real-part and
complex-inclusion maps; it does not construct a frozen symbol.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumNormal.EuclideanSupportGap

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin n)

/-- Complex-linear action of a real finite matrix, for the frozen symbol in
`app:ch_background:prop:bg-frame`. -/
def complexifyMatrix (a : Matrix (Fin n) (Fin n) ℝ) : V →L[ℂ] V :=
  (Matrix.toEuclideanLin (a.map (fun x ↦ (x : ℂ)))).toContinuousLinearMap

/-- The complexified action retains the literal matrix entries
(`app:ch_background:prop:bg-frame`). -/
theorem complexifyMatrix_apply (a : Matrix (Fin n) (Fin n) ℝ) (z : V) (i : Fin n) :
    complexifyMatrix a z i = ∑ j, (a i j : ℂ) * z j := rfl

/-- Complexification agrees with the shared inclusion on real vectors
(`app:ch_background:prop:bg-frame`). -/
theorem complexifyMatrix_inclusion (a : Matrix (Fin n) (Fin n) ℝ) (v : E) :
    complexifyMatrix a (euclideanComplexInclusion v) =
      euclideanComplexInclusion (a.toEuclideanLin v) := by
  ext i
  simp [complexifyMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- The continuous real-linear adapter transports continuity and uniform
bounds of the actual finite real symbol (`app:ch_background:prop:bg-frame`). -/
def complexifyMatrixCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (V →L[ℂ] V) :=
  LinearMap.toContinuousLinearMap
    { toFun := complexifyMatrix
      map_add' := by
        intro a b
        ext z i
        simp [complexifyMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext z i
        simp [complexifyMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum, mul_assoc] }

/-- Real and imaginary quadratures of the complexified quadratic form, with
Mathlib's conjugate-linear first argument (`app:ch_background:prop:bg-frame`). -/
theorem re_inner_complexifyMatrix (a : Matrix (Fin n) (Fin n) ℝ) (z : V) :
    (inner ℂ z (complexifyMatrix a z)).re =
      inner ℝ (euclideanRealPart z) (a.toEuclideanLin (euclideanRealPart z)) +
      inner ℝ (euclideanRealPart (-Complex.I • z))
        (a.toEuclideanLin (euclideanRealPart (-Complex.I • z))) := by
  simp [complexifyMatrix, PiLp.inner_apply, RCLike.inner_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib]

/-- The two real quadratures retain the full complex squared norm
(`app:ch_background:prop:bg-frame`). -/
theorem norm_sq_eq_quadratures (z : V) :
    ‖z‖ ^ 2 = ‖euclideanRealPart z‖ ^ 2 +
      ‖euclideanRealPart (-Complex.I • z)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Complex.sq_norm, Complex.normSq_apply]
  simp [Finset.sum_add_distrib, pow_two]

/-- A real quadratic lower bound implies the same complex quadratic lower
bound, so the frozen-model producer only owes real positivity
(`app:ch_background:prop:bg-frame`). -/
theorem complexifyMatrix_gap (a : Matrix (Fin n) (Fin n) ℝ) {c : ℝ}
    (ha : ∀ v : E, c * ‖v‖ ^ 2 ≤ inner ℝ v (a.toEuclideanLin v)) (z : V) :
    c * ‖z‖ ^ 2 ≤ (inner ℂ z (complexifyMatrix a z)).re := by
  rw [re_inner_complexifyMatrix, norm_sq_eq_quadratures, mul_add]
  exact add_le_add (ha _) (ha _)

/-- Real nonnegativity transfers without any additional spectral premise
(`app:ch_background:prop:bg-frame`). -/
theorem complexifyMatrix_nonneg (a : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ v : E, 0 ≤ inner ℝ v (a.toEuclideanLin v)) (z : V) :
    0 ≤ (inner ℂ z (complexifyMatrix a z)).re := by
  rw [re_inner_complexifyMatrix]
  exact add_nonneg (ha _) (ha _)

/-- Continuity of the complexified symbol follows from the real symbol
(`app:ch_background:prop:bg-frame`). -/
theorem continuous_complexifyMatrix {a : E → Matrix (Fin n) (Fin n) ℝ}
    (ha : Continuous a) : Continuous (fun k ↦ complexifyMatrix (a k)) :=
  complexifyMatrixCLM.continuous.comp ha

/-- The literal quadrature decomposition of the complexified action
(`app:ch_background:prop:bg-frame`). -/
theorem complexifyMatrix_eq_quadratures (a : Matrix (Fin n) (Fin n) ℝ) (z : V) :
    complexifyMatrix a z =
      euclideanComplexInclusion (a.toEuclideanLin (euclideanRealPart z)) +
        Complex.I • euclideanComplexInclusion
          (a.toEuclideanLin (euclideanRealPart (-Complex.I • z))) := by
  ext i
  apply Complex.ext <;>
    simp [complexifyMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- A uniform real operator bound supplies a uniform complex operator bound,
without asking the parent for a new analytic estimate
(`app:ch_background:prop:bg-frame`). -/
theorem norm_complexifyMatrix_le (a : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : ‖a.toEuclideanLin.toContinuousLinearMap‖ ≤ M) :
    ‖complexifyMatrix a‖ ≤ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hre (z : V) : ‖euclideanRealPart z‖ ≤ ‖z‖ :=
    (euclideanRealPart.le_opNorm z).trans
      (by simpa using mul_le_mul_of_nonneg_right euclideanRealPart_norm_le (norm_nonneg z))
  have ha (v : E) : ‖a.toEuclideanLin v‖ ≤ M * ‖v‖ :=
    (a.toEuclideanLin.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg v))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [complexifyMatrix_eq_quadratures]
  calc
    _ ≤ ‖euclideanComplexInclusion (a.toEuclideanLin (euclideanRealPart z))‖ +
        ‖Complex.I • euclideanComplexInclusion
          (a.toEuclideanLin (euclideanRealPart (-Complex.I • z)))‖ := norm_add_le _ _
    _ = ‖a.toEuclideanLin (euclideanRealPart z)‖ +
        ‖a.toEuclideanLin (euclideanRealPart (-Complex.I • z))‖ := by
      simp [norm_smul, euclideanComplexInclusion_norm]
    _ ≤ M * ‖z‖ + M * ‖z‖ := by
      apply add_le_add
      · exact (ha _).trans (mul_le_mul_of_nonneg_left (hre z) hM0)
      · have hz : ‖euclideanRealPart (-Complex.I • z)‖ ≤ ‖z‖ := by
          simpa [norm_smul] using hre (-Complex.I • z)
        exact (ha _).trans (mul_le_mul_of_nonneg_left hz hM0)
    _ = (2 * M) * ‖z‖ := by ring

end JanetCartan.ContinuumNormal.EuclideanSupportGap
