module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.Regularization

/-!
# Strong convergence of literal adjoint PDO regularizations

The scalar adjoint is the same two-position PDO with reversed conjugate
amplitude. The scalar strong-limit theorem and finite vector assembly therefore
prove strong convergence of the actual Hilbert adjoints. This preserves the
original source and output masks in `app:ch_regular_base:eq:fio-input` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.PdoRealization
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The literal vector adjoints converge strongly under the same pointwise
symbol limit and finite physical derivative budget. Consumer: canonical PDO
regularizations in `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem tendsto_vectorPDO_adjoint_of_pointwise (hn : 0 < n) (R M : ℝ)
    (a : ℕ → E → P → Mat) (b : E → P → Mat)
    (ha : ∀ j, GraphNormalAmplitudeBounds (a j) R M)
    (hb : GraphNormalAmplitudeBounds b R M)
    (hlim : ∀ ξ z, Tendsto (fun j ↦ a j ξ z) atTop (𝓝 (b ξ z))) (u : H) :
    Tendsto (fun j ↦ (vectorTwoPositionL2Operator hn R (a j) (ha j).smooth
      (ha j).support M (ha j).entry_bound).adjoint u) atTop
      (𝓝 ((vectorTwoPositionL2Operator hn R b hb.smooth hb.support M hb.entry_bound).adjoint u)) := by
  simp only [vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint]
  simp only [vectorMatrixL2Operator_eq_sum, sum_apply, ContinuousLinearMap.comp_apply]
  apply tendsto_finsetSum _ fun i _ ↦ ?_
  apply tendsto_finsetSum _ fun j _ ↦ ?_
  apply ((coordinateInjection i : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r)).toContinuousLinearMap.compLpL 2
    (volume : Measure E)).continuous.continuousAt.tendsto.comp
  simp_rw [twoPositionL2Operator_adjoint]
  apply UncutNormal.PdoLimit.tendsto_twoPositionL2Operator
  intro ξ z
  exact continuous_star.continuousAt.tendsto.comp
    ((matrixEntryEvaluation j i).continuous.continuousAt.tendsto.comp
      (hlim ξ (positionReversal n z)))

/-- The original common smooth cutoffs converge strongly for the literal
adjoints as well as the forward canonical PDOs. Source:
`app:ch_regular_base:eq:energy-complete-residual` and `actual-adjoint-trade`. -/
theorem tendsto_canonicalGraph_frequencyCut_adjoint
    (hn : 0 < n) (A : FullAmplitude n r) {R M C : ℝ}
    (hb : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R M)
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hC : 1 ≤ C)
    (hθbound : ∀ j η, ‖θ j η‖ ≤ C)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1)) (u : H) :
    Tendsto (fun j ↦ (fullGraphOperator (fun x η ↦ inner ℝ x η)
      (frequencyCutFullAmplitude (θ j) A)).adjoint u) atTop
        (𝓝 ((fullGraphOperator (fun x η ↦ inner ℝ x η) A).adjoint u)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb.derivative 0 [] (by simp) 0)
  have hb' : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R (C * M) :=
    ⟨hb.smooth, hb.support, fun ξ is hi z ↦ (hb.derivative ξ is hi z).trans
      (le_mul_of_one_le_left hM hC)⟩
  let hc := fun j ↦ cycleSymbolBounds_frequencyCut A hb (θ j) (hθ j)
    (zero_le_one.trans hC) (hθbound j)
  have h := tendsto_vectorPDO_adjoint_of_pointwise hn R (C * M)
    (fun j ↦ physicalPDOCycleSymbol (frequencyCutFullAmplitude (θ j) A))
    (physicalPDOCycleSymbol A) hc hb' (fun ξ z ↦ by
      simpa only [physicalPDOCycleSymbol, frequencyCutFullAmplitude, one_smul] using
        (hθlim ((2 * Real.pi) • ξ)).smul_const (physicalPDOCycleSymbol A ξ z)) u
  have he j := canonicalGraph_eq_vectorTwoPositionL2Operator hn R
    (frequencyCutFullAmplitude (θ j) A) (hc j).smooth (hc j).support (C * M) (hc j).entry_bound
  simpa only [← he, ← canonicalGraph_eq_vectorTwoPositionL2Operator hn R A
    hb'.smooth hb'.support (C * M) hb'.entry_bound] using h

end JanetCartan.RegularSector.Characteristic.PdoRealization
