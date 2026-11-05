module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.Normalization
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.PdoLimit

/-!
# Smooth frequency regularization of the canonical PDO

For `app:ch_regular_base:eq:energy-complete-residual`, a prescribed common
smooth frequency cutoff is retained. Uniformly bounded cutoffs tending to one
produce actual strong limits of the canonical graph PDO, by the existing
matrix PDO convergence theorem. Sharp-ball convergence is not used here.
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

/-- A frequency-only factor commutes with every physical matrix derivative.
Consumer: `cycleSymbolBounds_frequencyCut`, for
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem matrixAmplitudeCoordinateDerivList_frequency_smul
    (b : P → Mat) (hb : ContDiff ℝ ∞ b) (a : ℂ) (is : List (Fin (2 * n))) (z : P) :
    matrixAmplitudeCoordinateDerivList is (fun z ↦ a • b z) z =
      a • matrixAmplitudeCoordinateDerivList is b z := by
  ext i j
  exact congrFun (euclideanCoordinateDerivList_const_mul
    ((matrixEntryEvaluation i j).contDiff.comp hb) a is) z

/-- Multiplication by a bounded smooth frequency cutoff preserves the physical
support and the fixed Frobenius reserve. These are symbol estimates, not
assumed graph bounds (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cycleSymbolBounds_frequencyCut
    (A : FullAmplitude n r) {R M C : ℝ}
    (hb : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R M)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hC : 0 ≤ C)
    (hθbound : ∀ η, ‖θ η‖ ≤ C) :
    GraphNormalAmplitudeBounds
      (physicalPDOCycleSymbol (frequencyCutFullAmplitude θ A)) R (C * M) := by
  have he : physicalPDOCycleSymbol (frequencyCutFullAmplitude θ A) =
      fun ξ z ↦ θ ((2 * Real.pi) • ξ) • physicalPDOCycleSymbol A ξ z := rfl
  rw [he]
  refine ⟨(hθ.comp (contDiff_fst.const_smul _)).smul hb.smooth, ?_, ?_⟩
  · intro ξ i j z hz
    exact hb.support ξ i j z (fun he ↦ hz (by simp [he]))
  · intro ξ is hi z
    rw [matrixAmplitudeCoordinateDerivList_frequency_smul (physicalPDOCycleSymbol A ξ)
      (hb.smooth.comp (contDiff_const.prodMk contDiff_id)), norm_smul]
    exact mul_le_mul (hθbound _) (hb.derivative ξ is hi z) (norm_nonneg _) hC

/-- Primitive symbol inputs construct the literal compact-test representatives
of the SAME canonical PDO. This supplies the `Preg` action required by
`CompleteResidual.completeResidual_operators_of_graph_regularizations`, with
any chosen common smooth frequency sequence.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem canonicalGraph_frequencyCut_realizes
    (hn : 0 < n) (A : FullAmplitude n r) {R M C : ℝ}
    (hb : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R M)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hC : 0 ≤ C)
    (hθbound : ∀ η, ‖θ η‖ ≤ C) (u : graphTestSpace n r) :
    fullGraphOperator (fun x η ↦ inner ℝ x η) (frequencyCutFullAmplitude θ A)
        (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (fun x η ↦ inner ℝ x η) (frequencyCutFullAmplitude θ A) u := by
  let hc := cycleSymbolBounds_frequencyCut A hb θ hθ hC hθbound
  rw [canonicalGraph_eq_vectorTwoPositionL2Operator hn R _ hc.smooth hc.support
    (C * M) hc.entry_bound]
  refine (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R _ hc.smooth
    hc.support (C * M) hc.entry_bound u.val (graphTest_memLp u)
    (fun j ↦ (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).restrictScalars ℝ).contDiff.comp
      u.property.1).of_le (by simp))
    (fun j ↦ u.property.2.comp_left (g := fun v : EuclideanSpace ℂ (Fin r) ↦ v j) rfl)).trans ?_
  exact Eventually.of_forall fun x ↦ congrArg (WithLp.toLp 2)
    (canonicalGraph_eq_matrixFullAmplitudeOperator _ hc.smooth (C * M) hc.entry_bound u x).symm

/-- Actual strong convergence on every Euclidean vector L² input for a
prescribed bounded smooth frequency sequence tending to one. The limit is the
choice-defined canonical graph, identified by literal tests and density.
This supplies the PDO strong-limit input of
`CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem tendsto_canonicalGraph_frequencyCut
    (hn : 0 < n) (A : FullAmplitude n r) {R M C : ℝ}
    (hb : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R M)
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hC : 1 ≤ C)
    (hθbound : ∀ j η, ‖θ j η‖ ≤ C)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1)) (u : H) :
    Tendsto (fun j ↦ fullGraphOperator (fun x η ↦ inner ℝ x η)
      (frequencyCutFullAmplitude (θ j) A) u) atTop
        (𝓝 (fullGraphOperator (fun x η ↦ inner ℝ x η) A u)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb.derivative 0 [] (by simp) 0)
  have hb' : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R (C * M) :=
    ⟨hb.smooth, hb.support, fun ξ is hi z ↦ (hb.derivative ξ is hi z).trans
      (le_mul_of_one_le_left hM hC)⟩
  let hc := fun j ↦ cycleSymbolBounds_frequencyCut A hb (θ j) (hθ j)
    (zero_le_one.trans hC) (hθbound j)
  have h := UncutNormal.tendsto_vectorTwoPositionL2Operator_of_pointwise hn R (C * M)
    (fun j ↦ physicalPDOCycleSymbol (frequencyCutFullAmplitude (θ j) A))
    (physicalPDOCycleSymbol A) hc hb' (fun ξ z ↦ by
      simpa only [physicalPDOCycleSymbol, frequencyCutFullAmplitude, one_smul] using
        (hθlim ((2 * Real.pi) • ξ)).smul_const (physicalPDOCycleSymbol A ξ z)) u
  have he j := canonicalGraph_eq_vectorTwoPositionL2Operator hn R
    (frequencyCutFullAmplitude (θ j) A) (hc j).smooth (hc j).support (C * M) (hc j).entry_bound
  simpa only [← he, ← canonicalGraph_eq_vectorTwoPositionL2Operator hn R A
    hb'.smooth hb'.support (C * M) hb'.entry_bound] using h

end JanetCartan.RegularSector.Characteristic.PdoRealization
