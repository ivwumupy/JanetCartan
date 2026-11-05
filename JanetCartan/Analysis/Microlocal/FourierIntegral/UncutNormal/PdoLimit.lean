module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.PdoLimit.Scalar
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorKernel

/-!
# Strong continuity of the actual matrix two-position PDO

Pointwise convergence of smooth matrix amplitudes with common physical support
and finite physical derivative bounds implies strong convergence of the existing
`vectorTwoPositionL2Operator`. The coefficient and multiplier majorants are
constructed in the helper modules, using `app:ch_osc:lem:osc-amplitude`.

Consumer: identification of the same uncut graph cross-normal with the PDO of
`app:ch_regular_base:eq:actual-normal-amplitude`. The parent construction supplies
the uniform `GraphNormalAmplitudeBounds` for its cut and uncut symbols from the
original primitive jets, and the pointwise limit from `UncutNormal.CutoffSymbol`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff Matrix.Norms.Frobenius ComplexInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
namespace JanetCartan.FourierIntegral.UncutNormal
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Strong continuity of the existing graph-normal realization under pointwise
symbol convergence and a common finite physical derivative budget. Finite matrix
assembly preserves the scalar series limit from `app:ch_osc:lem:osc-amplitude`.
Consumer: the uncut cross-normal in `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem tendsto_graphNormalL2Operator_of_pointwise (hn : 0 < n) (R M : ℝ)
    (a : ℕ → E → P → Matrix (Fin r) (Fin r) ℂ)
    (b : E → P → Matrix (Fin r) (Fin r) ℂ)
    (ha : ∀ m, GraphNormalAmplitudeBounds (a m) R M)
    (hb : GraphNormalAmplitudeBounds b R M)
    (hlim : ∀ ξ z, Tendsto (fun m ↦ a m ξ z) atTop (𝓝 (b ξ z))) (f : H) :
    Tendsto (fun m ↦ graphNormalL2Operator hn R (a m) M (ha m) f) atTop
      (𝓝 (graphNormalL2Operator hn R b M hb f)) := by
  simp only [graphNormalL2Operator, graphMatrixL2Operator, sum_apply,
    ContinuousLinearMap.comp_apply]
  apply tendsto_finsetSum _ fun i _ ↦ ?_
  apply tendsto_finsetSum _ fun j _ ↦ ?_
  apply ((coordinateInjection i : ℂ →ₗᵢ[ℂ] V).toContinuousLinearMap.compLpL 2
    (volume : Measure E)).continuous.continuousAt.tendsto.comp
  apply PdoLimit.tendsto_twoPositionL2Operator
  intro ξ z
  exact (matrixEntryEvaluation i j).continuous.continuousAt.tendsto.comp (hlim ξ z)

/-- Strong convergence on every vector L² input of the SAME bounded matrix PDO
used in the compact cross-normal identity. Only pointwise symbol convergence,
fixed physical support and the uniform `2 * (n + 1)` physical derivative budget
are required (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem tendsto_vectorTwoPositionL2Operator_of_pointwise (hn : 0 < n) (R M : ℝ)
    (a : ℕ → E → P → Matrix (Fin r) (Fin r) ℂ)
    (b : E → P → Matrix (Fin r) (Fin r) ℂ)
    (ha : ∀ m, GraphNormalAmplitudeBounds (a m) R M)
    (hb : GraphNormalAmplitudeBounds b R M)
    (hlim : ∀ ξ z, Tendsto (fun m ↦ a m ξ z) atTop (𝓝 (b ξ z))) (f : H) :
    Tendsto (fun m ↦ vectorTwoPositionL2Operator hn R (a m) (ha m).smooth
      (ha m).support M (ha m).entry_bound f) atTop
      (𝓝 (vectorTwoPositionL2Operator hn R b hb.smooth hb.support M hb.entry_bound f)) := by
  have he (m : ℕ) :=
    vectorTwoPositionL2Operator_eq_graphNormalL2Operator hn R (a m) M (ha m)
  simpa only [he, vectorTwoPositionL2Operator_eq_graphNormalL2Operator hn R b M hb] using
    tendsto_graphNormalL2Operator_of_pointwise hn R M a b ha hb hlim f

/-- The strong PDO limit also holds against every L² test vector, as needed to
compare tested cross-normal identities in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem tendsto_vectorTwoPositionL2Operator_inner (hn : 0 < n) (R M : ℝ)
    (a : ℕ → E → P → Matrix (Fin r) (Fin r) ℂ)
    (b : E → P → Matrix (Fin r) (Fin r) ℂ)
    (ha : ∀ m, GraphNormalAmplitudeBounds (a m) R M)
    (hb : GraphNormalAmplitudeBounds b R M)
    (hlim : ∀ ξ z, Tendsto (fun m ↦ a m ξ z) atTop (𝓝 (b ξ z))) (f g : H) :
    Tendsto (fun m ↦ ⟪g, vectorTwoPositionL2Operator hn R (a m) (ha m).smooth
      (ha m).support M (ha m).entry_bound f⟫) atTop
      (𝓝 ⟪g, vectorTwoPositionL2Operator hn R b hb.smooth hb.support M hb.entry_bound f⟫) :=
  tendsto_const_nhds.inner (𝕜 := ℂ)
    (tendsto_vectorTwoPositionL2Operator_of_pointwise hn R M a b ha hb hlim f)

/-- Distributional convergence follows from the proved strong convergence of the
actual vector PDO, for removing the regularization in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem tendsto_vectorTwoPositionL2Operator_temperedDistribution
    (hn : 0 < n) (R M : ℝ)
    (a : ℕ → E → P → Matrix (Fin r) (Fin r) ℂ)
    (b : E → P → Matrix (Fin r) (Fin r) ℂ)
    (ha : ∀ m, GraphNormalAmplitudeBounds (a m) R M)
    (hb : GraphNormalAmplitudeBounds b R M)
    (hlim : ∀ ξ z, Tendsto (fun m ↦ a m ξ z) atTop (𝓝 (b ξ z))) (f : H) :
    Tendsto (fun m ↦ Lp.toTemperedDistribution
      (vectorTwoPositionL2Operator hn R (a m) (ha m).smooth
        (ha m).support M (ha m).entry_bound f)) atTop
      (𝓝 (Lp.toTemperedDistribution
        (vectorTwoPositionL2Operator hn R b hb.smooth hb.support M hb.entry_bound f))) :=
  (Lp.toTemperedDistributionCLM V (volume : Measure E) 2).continuous.continuousAt.tendsto.comp
    (tendsto_vectorTwoPositionL2Operator_of_pointwise hn R M a b ha hb hlim f)

end JanetCartan.FourierIntegral.UncutNormal
