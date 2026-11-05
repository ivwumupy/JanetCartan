module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Normal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Limit

/-!
# Conditional graph L² realization from the complete normal

This supplies the deduction in `app:ch_regular_base:thm:actual-calculus`, Step 1,
for `jc-finite-fio-calculus` and `jc-response-near-carrier`. The producers still
owe compact-frequency realizations, their exact complete normal identities,
uniform finite normal-amplitude bounds, and a.e. convergence of the literal
integrals on compact smooth tests. No unregularized boundedness or L² convergence
is an input. Fatou supplies test-limit membership and density supplies the unique
bounded extension. Its literal Hilbert adjoint has the same low bound.

The graph integral retains physical covectors and `(2π)⁻ⁿ`. The normal PDO uses
the existing Mathlib Fourier convention; its exact identification must include
the change of covector by `2π`. All source cutoffs remain inside the full graph
amplitude. A producer using the pure type-I normal formula must first prove an
exact source reduction with its summable coefficients; that reduction is not
asserted here. These conditional results do not complete the actual calculus.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.FourierIntegral

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The literal graph integral, viewed in the Euclidean complex fiber rather
than the supremum norm on coordinates (`app:ch_regular_base:eq:fio-input`). -/
def graphTestOutput (S : E → E → ℝ) (A : FullAmplitude n r)
    (u : graphTestSpace n r) (x : E) : V :=
  WithLp.toLp 2 (graphOperator S A (fun y ↦ (u.val y).ofLp) x)

/-- Compact-frequency inputs for `app:ch_regular_base:thm:actual-calculus`,
Step 1. Bounds for these individual regularizations are not assumed uniform.
The support fields retain both actual physical cutoffs in the full amplitude;
`realizes` identifies the compact-frequency operator with the literal integral. -/
structure GraphRegularization (S : E → E → ℝ) (A : FullAmplitude n r) where
  outputSet : Set E
  sourceSet : Set E
  outputCompact : IsCompact outputSet
  sourceCompact : IsCompact sourceSet
  physicalSupport : ∀ x y η, x ∉ outputSet ∨ y ∉ sourceSet → A x y η = 0
  cutoff : ℕ → E → ℂ
  cutoffCompact : ∀ k, HasCompactSupport (cutoff k)
  cutoffSmooth : ∀ k, ContDiff ℝ ∞ (cutoff k)
  operator : ℕ → H →L[ℂ] H
  realizes : ∀ k u, operator k (graphTestToLp u) =ᵐ[volume]
    graphTestOutput S (fun x y η ↦ cutoff k η • A x y η) u

/-- Uniform graph bound from the exact complete normal identification and a
fixed Frobenius derivative reserve, as in
`app:ch_regular_base:eq:actual-normal-kernel`–`actual-normal-amplitude`.
This identity must include source cutoffs; the pure type-I formula alone does
not meet this hypothesis for a source-dependent amplitude. -/
theorem norm_graphRegularization_uniform (hn : 0 < n) (R : ℝ)
    {S : E → E → ℝ} {A : FullAmplitude n r} (G : GraphRegularization S A)
    (b : ℕ → E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ k, GraphNormalAmplitudeBounds (b k) R M)
    (hN : ∀ k, (G.operator k).comp (G.operator k).adjoint =
      graphNormalL2Operator hn R (b k) M (hb k)) (k : ℕ) :
    ‖G.operator k‖ ≤ Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M)) :=
  norm_graphRegularization_le hn R (b k) hM (hb k) (G.operator k) (hN k)

/-- `app:ch_regular_base:thm:actual-calculus`, Step 1, conditional on the
actual complete normal calculation and a.e. test convergence. This proves L²
membership of the literal test outputs, the unique bounded realization, and
the same low bound for the Hilbert adjoint. There is no L²-convergence premise.
The derivative reserve and constant are independent of any higher seminorm. -/
theorem exists_graphL2Realization (hn : 0 < n) (R : ℝ)
    {S : E → E → ℝ} {A : FullAmplitude n r} (G : GraphRegularization S A)
    (b : ℕ → E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ k, GraphNormalAmplitudeBounds (b k) R M)
    (hN : ∀ k, (G.operator k).comp (G.operator k).adjoint =
      graphNormalL2Operator hn R (b k) M (hb k))
    (hlimit : ∀ u : graphTestSpace n r, ∀ᵐ x ∂volume,
      Tendsto (fun k ↦ graphTestOutput S (fun x y η ↦ G.cutoff k η • A x y η) u x)
        atTop (𝓝 (graphTestOutput S A u x))) :
    let C := Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M))
    (∀ u, MemLp (graphTestOutput S A u) 2 volume ∧
      (eLpNorm (graphTestOutput S A u) 2 volume).toReal ≤ C * ‖graphTestToLp u‖) ∧
    ∃ U : H →L[ℂ] H, ‖U‖ ≤ C ∧ ‖U.adjoint‖ ≤ C ∧
      (∀ u, U (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
      ∀ W : H →L[ℂ] H,
        (∀ u, W (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) → W = U := by
  dsimp only
  have hbound := norm_graphRegularization_uniform hn R G b hM hb hN
  have hl (u : graphTestSpace n r) : ∀ᵐ x ∂volume,
      Tendsto (fun k ↦ G.operator k (graphTestToLp u) x) atTop
        (𝓝 (graphTestOutput S A u x)) := by
    have he := ae_all_iff.mpr (fun k ↦ G.realizes k u)
    filter_upwards [he, hlimit u] with x hx hlx
    exact hlx.congr (fun k ↦ (hx k).symm)
  refine ⟨?_, exists_graphLimit_extension G.operator (graphTestOutput S A)
    (Real.sqrt_nonneg _) hbound hl⟩
  intro u
  exact graphLimit_memLp_bound (fun k ↦ G.operator k (graphTestToLp u))
    (graphTestOutput S A u) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fun k ↦ ((G.operator k).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound k) (norm_nonneg _))) (hl u)

end JanetCartan.FourierIntegral
