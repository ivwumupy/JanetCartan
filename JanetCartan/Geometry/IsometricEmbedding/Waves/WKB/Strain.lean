module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Operator
public import JanetCartan.LinearAlgebra.NormalInverse
import Mathlib.Tactic.Module

/-!
# Exact half-strain and cubic WKB residual

The normal-inverse algebra behind `app:ch_waves:eq:exact-half-strain` and the
conditional full strain formula `app:ch_waves:eq:WKB-residual`. The latter uses
the actual complex extension of the coordinate linearized metric. Its geometric
half-strain identity is an explicit input; no construction of a frame, immersion,
phase, or transport solution is asserted.
-/

@[expose] public noncomputable section

namespace JanetCartan.WKB

/-- Normal completion cancels exactly the complementary strain, the algebraic
step in `app:ch_waves:eq:exact-half-strain`. Surjectivity supplies the inverse. -/
theorem normalCompletion_halfStrain {T N : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
    (B : T →ₗ[ℝ] N) (hB : Function.Surjective B) (a : T) :
    a - B.adjoint (NormalInverse.normalCompletion B hB a) = B.ker.starProjection a := by
  rw [NormalInverse.adjoint_normalCompletion, Submodule.starProjection_orthogonal_val]
  abel

/-- Complex extension of `Dγ_G W`, in the coordinate convention of
`app:ch_waves:eq:exact-half-strain`. The background immersion is real. -/
def complexLinearizedMetric {n N : ℕ} (G : Euclidean n → Euclidean N)
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) (x : Euclidean n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j ↦
  ∑ k, ((partialDeriv G x i k : ℂ) * partialDeriv W x j k +
    partialDeriv W x i k * (partialDeriv G x j k : ℂ))

/-- The real Frobenius Gram matrix of the stress frame in
`app:ch_waves:eq:WKB-residual`. -/
def stressGram {n m : ℕ} (Q : Fin m → MetricTensor n) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ tensorPairing (Q i) (Q j)

/-- The complex-linear inverse-Gram reconstruction in
`app:ch_waves:eq:WKB-residual`. Projection onto the actual stress space is a
geometric input to the half-strain identity below. -/
def stressReconstruction {n m : ℕ} (Q : Fin m → MetricTensor n) :
    (Fin m → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun p := ∑ i, ∑ j, (((stressGram Q)⁻¹ i j : ℂ) * p j) • (Q i).map Complex.ofReal
  map_add' p q := by
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]
    congr 1
    funext i
    congr 1
    funext j
    congr 1
    ring

/-- From the exact geometric half-strain formula and the eikonal/transport
relations, the demodulated full strain is the explicit inverse-Gram cubic
residual of `app:ch_waves:eq:WKB-residual`. The half-strain hypothesis is for
all twice continuously differentiable input fields; it contains no WKB cancellation. -/
theorem twoTermWave_strain_residual {n m N : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (C : Euclidean n → Fin n → F →ₗ[ℂ] (Fin m → ℂ))
    (D : Euclidean n → F →ₗ[ℂ] (Fin m → ℂ))
    (G : Euclidean n → Euclidean N)
    (V : (Euclidean n → F) → Euclidean n → EuclideanSpace ℂ (Fin N))
    (Q : Euclidean n → Fin m → MetricTensor n)
    {lam : ℝ} (hlam : lam ≠ 0) {φ : Euclidean n → ℝ}
    {a b : Euclidean n → F} {x : Euclidean n}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b)
    (hhalf : ∀ u : Euclidean n → F, ContDiff ℝ 2 u →
      (2 : ℂ)⁻¹ • complexLinearizedMetric G (V u) x =
        stressReconstruction (Q x) (firstOrderApply C D u x))
    (heikonal : principalSymbol C φ x (a x) = 0)
    (htransport : Complex.I • principalSymbol C φ x (b x) +
      firstOrderApply C D a x = 0) :
    waveCarrier (-lam) φ x • complexLinearizedMetric G (V (twoTermWave lam φ a b)) x =
      ((2 : ℂ) * ((lam : ℂ)⁻¹)^3) •
        ∑ i, ∑ j, (((stressGram (Q x))⁻¹ i j : ℂ) * firstOrderApply C D b x j) •
          (Q x i).map Complex.ofReal := by
  have hu : ContDiff ℝ 2 (twoTermWave lam φ a b) :=
    contDiff_modulatedWave hφ ((ha.add (hb.const_smul _)).const_smul _)
  have hs := congrArg ((2 : ℂ) • ·) (hhalf (twoTermWave lam φ a b) hu)
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] at hs
  rw [hs, firstOrder_twoTermWave_residual C D hlam (hφ.differentiable (by norm_num) x)
      (ha.differentiable (by norm_num) x) (hb.differentiable (by norm_num) x)
      heikonal htransport,
    map_smul, map_smul]
  calc
    _ = ((2 : ℂ) * ((lam : ℂ)⁻¹)^3) •
        ((waveCarrier (-lam) φ x * waveCarrier lam φ x) •
          stressReconstruction (Q x) (firstOrderApply C D b x)) := by module
    _ = _ := by rw [waveCarrier_neg_mul, one_smul]; rfl

end JanetCartan.WKB
