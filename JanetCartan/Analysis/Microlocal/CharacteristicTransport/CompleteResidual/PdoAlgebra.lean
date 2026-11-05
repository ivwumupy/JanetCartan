module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.PdoAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Basic

/-!
# Compact-frequency PDO algebra for the complete residual

The consumer is the sum of the retarded endpoint and the algebraic correction
in `app:ch_regular_base:eq:energy-complete-residual`. All symbols use physical
covectors and the same frequency cutoff and source-masked Schwartz datum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Matrix
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The canonical physical PDO with a specified compact frequency cutoff.
The datum includes the original right source mask
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def cutPhysicalPDO (θ : E → ℂ) (c : E → E → Mat) (v : SchwartzMap E FV) : E → FV :=
  graphOperator (fun x ξ ↦ inner ℝ x ξ) (fun x _ ξ ↦ θ ξ • c x ξ) v

private theorem integrable_cutPhysicalPDO (θ : E → ℂ) (c : E → E → Mat)
    (v : SchwartzMap E FV) (x : E) (hθ : Continuous θ) (hθcs : HasCompactSupport θ)
    (hc : Continuous (c x)) :
    Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
      (θ ξ • c x ξ).mulVec (sourceInputFourierTransform v ξ)) := by
  have hm : Continuous (fun ξ ↦ (θ ξ • c x ξ).mulVec (sourceInputFourierTransform v ξ)) :=
    sourceMatrixAction.continuous₂.comp ((hθ.smul hc).prodMk
      (sourceInputFourierTransform v).continuous)
  apply ((by fun_prop : Continuous (fun ξ : E ↦
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)))).smul hm).integrable_of_hasCompactSupport
  apply hθcs.mono'
  intro ξ hξ
  by_contra h
  have hz := image_eq_zero_of_notMem_tsupport h
  simp [hz] at hξ

/-- Addition under the canonical PDO is justified by its common compact
frequency support, not by formal linearity of a potentially divergent integral
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cutPhysicalPDO_add (θ : E → ℂ) (c e : E → E → Mat)
    (v : SchwartzMap E FV) (x : E) (hθ : Continuous θ) (hθcs : HasCompactSupport θ)
    (hc : Continuous (c x)) (he : Continuous (e x)) :
    cutPhysicalPDO θ (fun y ξ ↦ c y ξ + e y ξ) v x =
      cutPhysicalPDO θ c v x + cutPhysicalPDO θ e v x := by
  simp only [cutPhysicalPDO, graphOperator_eq_sourceFourierIntegral, smul_add,
    Matrix.add_mulVec]
  rw [integral_add (integrable_cutPhysicalPDO θ c v x hθ hθcs hc)
    (integrable_cutPhysicalPDO θ e v x hθ hθcs he), smul_add]

/-- Scalar normalization of the physical algebraic correction. In particular,
`z = 1/i`, without changing either physical mask
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cutPhysicalPDO_smul (θ : E → ℂ) (c : E → E → Mat)
    (v : SchwartzMap E FV) (x : E) (z : ℂ) :
    cutPhysicalPDO θ (fun y ξ ↦ z • c y ξ) v x = z • cutPhysicalPDO θ c v x := by
  simp only [cutPhysicalPDO, graphOperator_eq_sourceFourierIntegral, Matrix.smul_mulVec,
    smul_comm (θ _) z, smul_comm (Complex.exp _) z, integral_smul,
    smul_comm (((2 * Real.pi) ^ n : ℂ)⁻¹) z]

/-- Smoothness of the literal finite-frequency PDO follows from its primitive
symbol and the compact source/frequency masks. This supplies the smooth
regularizations used in the weak-limit passage
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem contDiff_cutPhysicalPDO (θ : E → ℂ) (c : E → E → Mat)
    (v : SchwartzMap E FV) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hc : ContDiff ℝ ∞ (Function.uncurry c)) (hvcs : HasCompactSupport (v : E → FV)) :
    ContDiff ℝ ∞ (cutPhysicalPDO θ c v) := by
  have hp : ContDiff ℝ ∞ (fun p : E × E ↦ inner ℝ p.1 p.2) :=
    contDiff_fst.inner ℝ contDiff_snd
  have ha : ContDiff ℝ ∞ (fun p : E × E ↦ θ p.2 • c p.1 p.2) :=
    (hθ.comp contDiff_snd).smul hc
  apply contDiffOn_univ.mp
  exact contDiffOn_graphOperator_of_compact isOpen_univ hθcs
    hp.contDiffOn ha.contDiffOn
    (fun _ _ ξ hξ ↦ by simp [image_eq_zero_of_notMem_tsupport hξ])
    (v.smooth ⊤) hvcs

/-- Joint smoothness of the original symbol proves frequency continuity of
its full physical derivative, including B₀. This discharges the integral
splitting premise for the third residual term
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem continuous_physicalSymbolApply_frequency
    (A : E → Fin n → Mat) (B : E → Mat) (c : E → E → Mat)
    (hc : ContDiff ℝ ∞ (Function.uncurry c)) (x : E) :
    Continuous (physicalSymbolApply A B c x) := by
  have hd : Continuous (fun p : E × E ↦ fderiv ℝ (fun y ↦ c y p.2) p.1) := by
    have hh := contDiffOn_parameterFDeriv (U := univ) (V := univ)
      isOpen_univ isOpen_univ hc.contDiffOn
    exact (contDiffOn_univ.mp (by simpa using hh)).continuous
  apply Continuous.add
  · apply continuous_finsetSum
    intro a _
    exact continuous_const.mul
      ((hd.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  · exact continuous_const.mul (hc.continuous.comp (continuous_const.prodMk continuous_id))

/-- The actual complement inverse cancels the leading retarded endpoint.
The normalized left nullvector and the completion determinant are exactly the
inputs of `complementInverse_identity`; the oblique projection is not assumed
to be orthogonal. This is the matrix cancellation behind `Op(α)` in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem leading_endpoint_add_complementInverse
    (H A : Matrix (Fin q) (Fin q) ℝ) (k l : Fin q → ℝ) (e σ β : ℝ)
    (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1)
    (hd : (RegularSector.Characteristic.pencilCompletion H A k l e).det ≠ 0) :
    (σ * β) • (A * Matrix.vecMulVec k l) +
      (H + e • A) * ((σ * β) • RegularSector.Characteristic.complementInverse H A k l e) =
      (σ * β) • (1 : Matrix (Fin q) (Fin q) ℝ) := by
  rw [Matrix.mul_smul, RegularSector.Characteristic.complementInverse_identity hl hn hd,
    RegularSector.Characteristic.complementProjection, Matrix.mul_vecMulVec, ← smul_add]
  congr 1
  abel

end JanetCartan.CharacteristicTransport.CompleteResidual
