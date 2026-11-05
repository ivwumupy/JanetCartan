module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.OneStep

/-!
# The original source datum in joint carrier coordinates

In `paper-v2.tex`, `new:eq:carrier-ibp`, the input is `a_c(z)`.
Its derivatives in the output position and normalized covector vanish; its
source and parameter derivatives remain the derivatives of the original input.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

variable {n : ℕ} {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal input `a_c(z)`, retaining the source position and carrier
parameter, in `new:eq:carrier-ibp`. -/
def sourceDatum (a : Euclidean n × P → V) (q : Euclidean n × P)
    (w : CarrierVariables n) : V := a (w.fst, q.2)

/-- Only the parameter part of an external direction differentiates the
original input in `new:eq:carrier-ibp`. -/
theorem fderiv_sourceDatum_external
    {a : Euclidean n × P → V} (q e : Euclidean n × P) (w : CarrierVariables n)
    (ha : DifferentiableAt ℝ a (w.fst, q.2)) :
    fderiv ℝ (fun p ↦ sourceDatum a p w) q e =
      fderiv ℝ a (w.fst, q.2) (0, e.2) := by
  have h := ha.hasFDerivAt.comp q
    ((hasFDerivAt_const w.fst q).prodMk
      (ContinuousLinearMap.snd ℝ (Euclidean n) P).hasFDerivAt)
  exact congrArg (fun L : (Euclidean n × P) →L[ℝ] V ↦ L e) h.fderiv

/-- Only the source part of a joint integration direction differentiates
the original input in `new:eq:carrier-ibp`. -/
theorem fderiv_sourceDatum_integration
    {a : Euclidean n × P → V} (q : Euclidean n × P) (w v : CarrierVariables n)
    (ha : DifferentiableAt ℝ a (w.fst, q.2)) :
    fderiv ℝ (sourceDatum a q) w v =
      fderiv ℝ a (w.fst, q.2) (v.fst, 0) := by
  have h := ha.hasFDerivAt.comp w
    ((WithLp.fstL 2 ℝ (Euclidean n) (Euclidean n)).hasFDerivAt.prodMk
      (hasFDerivAt_const q.2 w))
  exact congrArg (fun L : CarrierVariables n →L[ℝ] V ↦ L v) h.fderiv

/-- The normalized covector derivative of `a_c(z)` is exactly zero,
as used in the derivative budget after `new:eq:carrier-ibp`. -/
theorem fderiv_sourceDatum_covector_eq_zero
    {a : Euclidean n × P → V} (q : Euclidean n × P) (w : CarrierVariables n)
    (θ : Euclidean n) (ha : DifferentiableAt ℝ a (w.fst, q.2)) :
    fderiv ℝ (sourceDatum a q) w (WithLp.toLp 2 (0, θ)) = 0 := by
  rw [fderiv_sourceDatum_integration q w _ ha]
  exact map_zero _

/-- An output-position derivative of `a_c(z)` is exactly zero. The
parameter derivatives are retained separately in `new:eq:carrier-ibp`. -/
theorem fderiv_sourceDatum_output_eq_zero
    {a : Euclidean n × P → V} (q : Euclidean n × P) (w : CarrierVariables n)
    (x : Euclidean n) (ha : DifferentiableAt ℝ a (w.fst, q.2)) :
    fderiv ℝ (fun p ↦ sourceDatum a p w) q (x, 0) = 0 := by
  rw [fderiv_sourceDatum_external q (x, 0) w ha]
  exact map_zero _

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
