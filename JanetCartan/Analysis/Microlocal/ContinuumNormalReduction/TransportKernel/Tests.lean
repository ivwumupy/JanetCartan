module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Action
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Identification on tests without an unregularized carrier bound

For `app:ch_background:eq:bg-full-complex-amplitude`, convergence of the individual
regularized adjoints on two tests identifies the limiting normal pairing. This
requires no uniform operator bound, and constructs no unregularized carrier CLM.
The continuum-row and normal-reduction consumers must supply the stated strong
adjoint limits and, when used, convergence of the distributional kernel pairing.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
local notation "V" => EuclideanSpace ℂ (Fin n)

/-- The full matrix kernel paired with two output tests, in the order appropriate
for the complex inner product (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def normalTestPairing (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (v w : Torus n → V) : ℂ :=
  ∫ x, inner ℂ (v x) (WithLp.toLp 2 (fun i ↦
    ∑ j, ∫ y, regularizedNormalEntry d m x y i j * w y j))

/-- The literal normal on tests equals the pairing of the two Hilbert adjoints.
All matrix sums and Fubini exchanges are supplied by `carrierHilbertNormal_eq_matrix`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalTestPairing_eq_adjoint_inner (h : FiniteCarrierKernelBounds d m)
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f : CarrierL2 n, T f =ᵐ[volume] regularizedCarrierIntegral d m f)
    (v w : ComplexOutputL2 n)
    (hAdj : T.adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u) :
    normalTestPairing d m v w = inner ℂ (T.adjoint v) (T.adjoint w) := by
  rw [T.adjoint_inner_left, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [carrierHilbertNormal_eq_matrix h T hT w hAdj] with x hx
  congr 1
  exact PiLp.ext fun i ↦ (hx i).symm

/-- The checked real-quadrature adjoint identity gives exactly four times the
real part of the literal complex normal pairing. Both complex input quadratures
are retained (`app:ch_background:eq:bg-real-symbol`). -/
theorem realCarrierNormal_pairing (h : FiniteCarrierKernelBounds d m)
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f : CarrierL2 n, T f =ᵐ[volume] regularizedCarrierIntegral d m f)
    (r s : OutputL2 n)
    (hAdj : T.adjoint (l2ComplexInclusion volume s) =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d (l2ComplexInclusion volume s) u) :
    inner ℝ r (realQuadratureChannel T ((realQuadratureChannel T).adjoint s)) =
      4 * (normalTestPairing d m (l2ComplexInclusion volume r)
        (l2ComplexInclusion volume s)).re := by
  rw [normalTestPairing_eq_adjoint_inner h T hT _ _ hAdj,
    ← (realQuadratureChannel T).adjoint_inner_left]
  rw [realQuadratureChannel_adjoint_apply, realQuadratureChannel_adjoint_apply,
    real_inner_smul_left, real_inner_smul_right, real_inner_eq_complex_re]
  ring

/-- Strong convergence of the two regularized adjoints identifies the limit on
these tests, with no bound on `‖T_R‖`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem tendsto_normalTestPairing_of_adjoint_limits
    (m : ℕ → CarrierVariable n → ℝ)
    (h : ∀ R, FiniteCarrierKernelBounds d (m R))
    (T : ℕ → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ R (f : CarrierL2 n), T R f =ᵐ[volume] regularizedCarrierIntegral d (m R) f)
    (v w : ComplexOutputL2 n)
    (hAdj : ∀ R, (T R).adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m R u : ℂ) * carrierAdjointIntegral d w u)
    (av aw : CarrierL2 n)
    (hv : Tendsto (fun R ↦ (T R).adjoint v) atTop (𝓝 av))
    (hw : Tendsto (fun R ↦ (T R).adjoint w) atTop (𝓝 aw)) :
    Tendsto (fun R ↦ normalTestPairing d (m R) v w) atTop (𝓝 (inner ℂ av aw)) := by
  simpa only [normalTestPairing_eq_adjoint_inner (h _) (T _) (hT _) v w (hAdj _)]
    using hv.inner hw

/-- A distributional kernel limit on a pair of tests agrees with the limiting
adjoint pairing. The kernel convergence and the two strong adjoint convergences
are separate explicit analytic inputs
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalTestPairing_limit_identification
    (m : ℕ → CarrierVariable n → ℝ)
    (h : ∀ R, FiniteCarrierKernelBounds d (m R))
    (T : ℕ → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ R (f : CarrierL2 n), T R f =ᵐ[volume] regularizedCarrierIntegral d (m R) f)
    (v w : ComplexOutputL2 n)
    (hAdj : ∀ R, (T R).adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m R u : ℂ) * carrierAdjointIntegral d w u)
    (av aw : CarrierL2 n)
    (hv : Tendsto (fun R ↦ (T R).adjoint v) atTop (𝓝 av))
    (hw : Tendsto (fun R ↦ (T R).adjoint w) atTop (𝓝 aw))
    (L : ℂ) (hL : Tendsto (fun R ↦ normalTestPairing d (m R) v w) atTop (𝓝 L)) :
    L = inner ℂ av aw :=
  tendsto_nhds_unique hL (tendsto_normalTestPairing_of_adjoint_limits m h T hT v w hAdj av aw hv hw)

end JanetCartan.ContinuumRow.TransportKernel
