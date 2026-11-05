module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.FiniteExpansion
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Extension

/-!
# Downstream Euclidean vector Fourier assembly for graph operators

This proves the implication from the exact finite weak expansion
`app:ch_regular_base:eq:graph-derivative-transfer` and its quantitative branch
L² bounds to the strong tame bound `app:ch_regular_base:eq:fio-input`, for every
natural input order, including zero, and every vector Sobolev datum.

The Hilbert space is literally `Lp (EuclideanSpace ℂ (Fin r)) 2 volume` on
Euclidean Lebesgue space; the existing Fourier weights and normalization are
unchanged. All constants precede the high majorant, operators, and datum.

The weak identities are conditional inputs produced by the checked forward,
reverse, and literal-adjoint theorems in `SobolevBounds.WeakTransfer`. The
branch norms are conditional inputs produced by the parent's primitive-budget
and low-L² construction. Instantiating both is the obligation of
`jc-deduce-fio-strong-sobolev`; this module does not prove a graph realization.

`graph_vector_reconstruction` supplies the additional gain-one implication
from actual Hˢ first derivatives and the original output's low L² norm.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv JanetCartan.Pseudodifferential
open scoped SchwartzMap
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The complete downstream strong estimate for a supplied bounded L² operator.
The finite weak expansion and branch norms imply output membership and the tame
bound for every vector Sobolev input, including `s = 0`. The scalar density
extension discharges the passage from compact tests to all data.

For the forward graph set `U` to its bounded L² realization; for the literal
adjoint set `U` to that realization's Hilbert adjoint, and initialize `A` with
the conjugate-transposed amplitude in original coordinate order. The parent
must supply the matching `R`, `P`, weak identities, and branch bounds.
Source: `app:ch_regular_base:eq:graph-derivative-transfer` through
`app:ch_regular_base:eq:fio-input`. -/
theorem exists_graph_vector_sobolev_constant_all_data (s : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (R : Fin n → FullAmplitude n r → FullAmplitude n r)
        (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
        (A : FullAmplitude n r) (T : FullAmplitude n r → H →L[ℂ] H)
        (U : H →L[ℂ] H) (Hhigh : ℝ), 0 ≤ Hhigh →
      (∀ (u : graphTestSpace n r) is, is.length ≤ s →
        orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
          (U (graphTestToLp u) : 𝓢'(E, V)) =
        ((fullAmplitudeDerivativeTerms R P A is).map fun p ↦
          (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
            𝓢'(E, V))).sum) →
      (∀ is, is.length ≤ s → ∀ p ∈ fullAmplitudeDerivativeTerms R P A is,
        ‖T p.1‖ ≤ C * Hhigh ^ (((s : ℝ) - p.2.length) / s)) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (U u) ∧
          vectorFourierSobolevNorm (s : ℝ) (U u) ≤ K *
            (vectorFourierSobolevNorm (s : ℝ) u + Hhigh * ‖u‖) := by
  obtain ⟨K, hK, htest⟩ := exists_graph_vector_sobolev_expansion_constant (n := n) (r := r) s C hC
  refine ⟨1 + (r : ℝ) * r * K, by positivity, ?_⟩
  intro R P A T U Hhigh hH hw hb u hu
  have h := graph_vector_bound_of_compactSmooth U s (s : ℝ) K Hhigh hK.le hH
    (fun v ↦ htest R P A T Hhigh hH v (U (graphTestToLp v)) (hw v) hb) u hu
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith)
    (add_nonneg (norm_nonneg _) (mul_nonneg hH (norm_nonneg _)))

end JanetCartan.FourierIntegral
