module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Symbol
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorKernel

/-!
# Compact normal symbols and the literal matrix integral

The Fubini step in `app:ch_regular_base:eq:actual-normal-amplitude` follows
from joint compact support of the normal symbol and compact support of the
smooth test. This is consumed by the compact graph/PDO identification.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds

open AmplitudeBound Pseudodifferential

variable {n r : ℕ}
local notation "E" => Euclidean n

private theorem integrable_compactSymbol_test (b : E → Euclidean (2*n) → Matrix (Fin r) (Fin r) ℂ)
    (hb : Continuous (Function.uncurry b)) (hs : HasCompactSupport (Function.uncurry b))
    (u : E → ℂ) (hu : Continuous u) (hsu : HasCompactSupport u)
    (x : E) (i j : Fin r) :
    Integrable (fun p : E × E ↦ u p.2 • b p.1 (pairedPosition x p.2) i j) := by
  have hc : Continuous (fun p : E × E ↦ u p.2 • b p.1 (pairedPosition x p.2) i j) := by
    apply (hu.comp continuous_snd).smul
    exact (continuous_apply j).comp ((continuous_apply i).comp (hb.comp
      (continuous_fst.prodMk (continuous_pairedPosition.comp
        (continuous_const.prodMk continuous_snd)))))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    ((hs.image continuous_fst).prod hsu)
  intro p hp
  have hu0 : u p.2 ≠ 0 := by
    intro h
    exact hp (by simp [h])
  have hb0 : b p.1 (pairedPosition x p.2) ≠ 0 := by
    intro h
    exact hp (by simp [h])
  exact ⟨⟨(p.1, pairedPosition x p.2), subset_tsupport _ hb0, rfl⟩,
    subset_tsupport _ hu0⟩

/-- Fubini identifies the literal full matrix operator with the cycle-frequency
normal integral on compact continuous tests. This supplies the testwise step
for `compactVectorGraph_cross_eq_vectorTwoPositionL2Operator`, preserving both
positions and the exact phase (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem compactSymbol_matrixFullAmplitudeOperator_eq_cycleIntegral
    (b : E → Euclidean (2*n) → Matrix (Fin r) (Fin r) ℂ)
    (hb : Continuous (Function.uncurry b)) (hs : HasCompactSupport (Function.uncurry b))
    (u : E → EuclideanSpace ℂ (Fin r)) (hu : Continuous u) (hsu : HasCompactSupport u)
    (x : E) :
    matrixFullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
      (fun y j ↦ u y j) x = fun i ↦ ∑ j, ∫ y, (∫ ξ,
        Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) *
          b ξ (pairedPosition x y) i j) * u y j := by
  funext i
  apply Finset.sum_congr rfl
  intro j _
  have hc : Continuous (fun y ↦ u y j) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).continuous.comp hu
  have hcs : HasCompactSupport (fun y ↦ u y j) :=
    hsu.comp_left (g := fun v : EuclideanSpace ℂ (Fin r) ↦ v j) rfl
  rw [fullAmplitudeOperator_eq_integral_amplitudeKernel _ _ x
    (integrable_compactSymbol_test b hb hs _ hc hcs x i j)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [amplitudeKernel_eq_integral, smul_eq_mul, real_inner_comm]
  exact mul_comm _ _

end JanetCartan.FourierIntegral.LowBounds
