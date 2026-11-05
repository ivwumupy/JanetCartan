module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Differential
import Mathlib.Tactic.Module

/-!
# Reduced first-order WKB cancellation

Exact algebra for `app:ch_waves:eq:primary-algebraic-correction` and
`app:ch_waves:eq:WKB-residual`. The operator has arbitrary complex-linear
first-order coefficients and a zeroth-order coefficient (including the actual
Christoffel terms). The phase and transport equations are inputs, not existence
claims. The physical frequency convention is that of `Waves.Differential`.
-/

@[expose] public noncomputable section
open JanetCartan
namespace JanetCartan.WKB

variable {n : ℕ} {F H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
/-- The full first-order operator in `app:ch_waves:eq:reduced-symbol`. -/
def firstOrderApply (C : Euclidean n → Fin n → F →ₗ[ℂ] H)
    (D : Euclidean n → F →ₗ[ℂ] H) (b : Euclidean n → F) (x : Euclidean n) : H :=
  ∑ i, C x i (partialDeriv b x i) + D x (b x)
/-- Principal symbol at `dφ`, as in `app:ch_waves:eq:reduced-symbol`. -/
def principalSymbol (C : Euclidean n → Fin n → F →ₗ[ℂ] H)
    (φ : Euclidean n → ℝ) (x : Euclidean n) : F →ₗ[ℂ] H :=
  ∑ i, (↑(partialDeriv φ x i) : ℂ) • C x i

/-- Product expansion before cancellation in `app:ch_waves:eq:WKB-residual`. -/
theorem firstOrder_twoTermWave (C : Euclidean n → Fin n → F →ₗ[ℂ] H)
    (D : Euclidean n → F →ₗ[ℂ] H) {lam : ℝ} {φ : Euclidean n → ℝ}
    {a b : Euclidean n → F} {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    firstOrderApply C D (twoTermWave lam φ a b) x = waveCarrier lam φ x •
      (((lam : ℂ)⁻¹)^2 • ((Complex.I * (lam : ℂ)) • principalSymbol C φ x (a x) +
        firstOrderApply C D a x) +
       ((lam : ℂ)⁻¹)^3 • ((Complex.I * (lam : ℂ)) • principalSymbol C φ x (b x) +
        firstOrderApply C D b x)) := by
  unfold firstOrderApply
  simp only [partialDeriv, fderiv_twoTermWave hφ ha hb]
  simp only [waveFirstAmplitude,
    twoTermWave, modulatedWave, map_smul, map_add, smul_add, smul_smul,
    principalSymbol, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_add_distrib, ← Finset.smul_sum]
  simp only [partialDeriv, mul_assoc, ← smul_smul, ← Finset.smul_sum]
  module

/-- Every frequency order in the reduced equation, before the two cancellations
of `app:ch_waves:eq:WKB-residual`. -/
theorem firstOrder_twoTermWave_expansion (C : Euclidean n → Fin n → F →ₗ[ℂ] H)
    (D : Euclidean n → F →ₗ[ℂ] H) {lam : ℝ} (hlam : lam ≠ 0)
    {φ : Euclidean n → ℝ} {a b : Euclidean n → F} {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    firstOrderApply C D (twoTermWave lam φ a b) x = waveCarrier lam φ x •
      ((lam : ℂ)⁻¹ • (Complex.I • principalSymbol C φ x (a x)) +
       ((lam : ℂ)⁻¹)^2 • (Complex.I • principalSymbol C φ x (b x) +
         firstOrderApply C D a x) +
       ((lam : ℂ)⁻¹)^3 • firstOrderApply C D b x) := by
  rw [firstOrder_twoTermWave C D hφ ha hb]
  have hc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have h₂ : ((lam : ℂ)⁻¹)^2 * (Complex.I * (lam : ℂ)) =
      (lam : ℂ)⁻¹ * Complex.I := by field_simp
  have h₃ : ((lam : ℂ)⁻¹)^3 * (Complex.I * (lam : ℂ)) =
      ((lam : ℂ)⁻¹)^2 * Complex.I := by field_simp
  congr 1
  simp only [smul_add, smul_smul, h₂, h₃]
  module

/-- Eikonal and transport cancellation leave exactly the cubic residual in
`app:ch_waves:eq:WKB-residual`. No transport solution is constructed here. -/
theorem firstOrder_twoTermWave_residual (C : Euclidean n → Fin n → F →ₗ[ℂ] H)
    (D : Euclidean n → F →ₗ[ℂ] H) {lam : ℝ} (hlam : lam ≠ 0)
    {φ : Euclidean n → ℝ} {a b : Euclidean n → F} {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x)
    (heikonal : principalSymbol C φ x (a x) = 0)
    (htransport : Complex.I • principalSymbol C φ x (b x) +
      firstOrderApply C D a x = 0) :
    firstOrderApply C D (twoTermWave lam φ a b) x =
      waveCarrier lam φ x • (((lam : ℂ)⁻¹)^3 • firstOrderApply C D b x) := by
  rw [firstOrder_twoTermWave_expansion C D hlam hφ ha hb, heikonal, htransport]
  simp

/-- The correction `i (M|K)⁻¹ p` in `app:ch_waves:eq:primary-algebraic-correction`.
Here `K = kᗮ`, `L = lᗮ`, and transport places `p = P b₀` in `L`, so the
projection in the manuscript is the identity on this input. -/
def algebraicCorrection (K : Submodule ℂ F) (L : Submodule ℂ H)
    (e : K ≃ₗ[ℂ] L) (p : L) : F := Complex.I • (e.symm p : F)

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- The restricted inverse produces the transport cancellation of
`app:ch_waves:eq:primary-algebraic-correction`, from its actual inverse property. -/
theorem algebraicCorrection_cancel (K : Submodule ℂ F) (L : Submodule ℂ H)
    (e : K ≃ₗ[ℂ] L) (M : F →ₗ[ℂ] H)
    (hM : ∀ v : K, M v = (e v : H)) (p : L) :
    Complex.I • M (algebraicCorrection K L e p) + (p : H) = 0 := by
  simp only [algebraicCorrection, map_smul, hM, e.apply_symm_apply, smul_smul]
  rw [Complex.I_mul_I, neg_one_smul, neg_add_cancel]

end JanetCartan.WKB
