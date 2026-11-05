module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Kernels
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Tests
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Distributional realization premises for weak graph transfer

The weak-limit input for `app:ch_regular_base:eq:graph-derivative-transfer` is
convergence of the literal regularized kernel pairings on compact smooth source
data. The supplied operator acts on the complex Euclidean-fiber L² space.
There is no derivative recurrence or Sobolev bound in this interface.

The producers are `jc-deduce-graph-l2-realization` and `jc-finite-fio-calculus`.
For every modified amplitude the final Sobolev assembly must supply the stated
realization; for the initial reverse amplitude it must use the Hilbert adjoint
of the forward operator and the conjugate-transposed full amplitude in original
coordinate order. This module only specifies the input, and proves closure of
the actual source test domain under coordinate differentiation.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Coordinate differentiation on compact smooth source data, consumed by the
finite expansion in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def graphTestPartialDeriv (i : Fin n) (u : graphTestSpace n r) : graphTestSpace n r :=
  ⟨fun x ↦ partialDeriv u.val x i,
    ((u.property.1.fderiv_right (by simp)).clm_apply contDiff_const),
    u.property.2.fderiv_apply ℝ (EuclideanSpace.single i 1)⟩

/-- Source test differentiation agrees with the coordinate arrays used by the
literal kernel. The L² fiber remains Euclidean, not the coordinate supremum norm.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphTestPartialDeriv_coordinates (i : Fin n) (u : graphTestSpace n r) (x : E) :
    ((graphTestPartialDeriv i u).val x).ofLp =
      partialDeriv (fun y ↦ (u.val y).ofLp) x i := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).toContinuousLinearMap
  have h := L.hasFDerivAt.comp x ((u.property.1.differentiable (by simp) x).hasFDerivAt)
  exact (congrArg (fun D : E →L[ℝ] (Fin r → ℂ) ↦
    D (EuclideanSpace.single i 1)) h.fderiv).symm

/-- Precise distributional realization of the literal frequency-regularized
kernels on compact smooth source tests. Set `K = graphOperator S` for forward
transfer, or `K = reverseGraphOperator S` for reverse transfer. In the latter
case start with `A = fun x y η ↦ (A₀ x y η).conjTranspose` and the actual
Hilbert adjoint as `T`; a complex forward cutoff becomes its complex conjugate.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`.

This is an explicit allowed realization premise, not a proof of realization.
Compact support, phase smoothness and homogeneity, and inverse gaps remain
separate geometric inputs to the compact-frequency integration-by-parts proof. -/
def GraphDistributionalRealization
    (K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ)
    (χ : ℕ → E → ℂ) (A : FullAmplitude n r) (T : H →L[ℂ] H) : Prop :=
  ∀ (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)),
    Tendsto (fun k ↦ ∫ x, φ x • WithLp.toLp 2
      (K (frequencyCutFullAmplitude (χ k) A) (fun y ↦ (u.val y).ofLp) x))
      atTop (𝓝 ((T (graphTestToLp u) : 𝓢'(E, V)) φ))

end JanetCartan.FourierIntegral
