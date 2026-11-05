module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators

/-!
# Locality of full graph realizations

The full-amplitude low construction may use a smooth auxiliary phase. These
identities remove that extension from the actual forward and reverse kernels,
the bounded graph family and its distributional realizations. The consumer is
`exists_fullGraphFamily_of_wholeImage_phase`, for
`app:ch_regular_base:thm:actual-calculus`, Steps 1 and 3.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The reverse integral sees only phase values on the original full-amplitude
support (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem reverseGraphOperator_phase_congr (S S' : E → E → ℝ) (A : FullAmplitude n r)
    (he : ∀ x y η, A x y η ≠ 0 → S' x η = S x η)
    (v : E → Fin r → ℂ) : reverseGraphOperator S' A v = reverseGraphOperator S A v := by
  funext y
  unfold reverseGraphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases ha : A x y η = 0
  · simp only [ha, Matrix.zero_mulVec, smul_zero]
  · rw [graphOscillation, graphOscillation, he x y η ha]

/-- The Euclidean test output retains the original phase and normalization
when the auxiliary extension is removed. Source: actual-calculus Step 1. -/
theorem graphTestOutput_phase_congr
    (S S' : E → E → ℝ) (A : FullAmplitude n r)
    (he : ∀ x y η, A x y η ≠ 0 → S' x η = S x η) :
    graphTestOutput S' A = graphTestOutput S A := by
  funext u x
  exact congrArg (fun f : E → Fin r → ℂ ↦ WithLp.toLp 2 (f x))
    (graphOperator_phase_congr S S' A he (fun y ↦ (u.val y).ofLp))

/-- The unique bounded full graph is independent of the auxiliary extension.
No existence is inferred from this identity; the low construction separately
proves the test realization. Source: actual-calculus Step 1. -/
theorem FullLowBounds.fullGraphOperator_phase_congr
    (S S' : E → E → ℝ) (A : FullAmplitude n r)
    (he : ∀ x y η, A x y η ≠ 0 → S' x η = S x η) :
    FullLowBounds.fullGraphOperator S' A = FullLowBounds.fullGraphOperator S A := by
  unfold fullGraphOperator
  rw [graphTestOutput_phase_congr S S' A he]

/-- Literal adjunction preserves independence of the phase extension, in the
original physical variable order. Source: actual-adjoint-trade. -/
theorem FullLowBounds.reverseFullGraphOperator_phase_congr
    (S S' : E → E → ℝ) (A : FullAmplitude n r)
    (he : ∀ x y η, A x y η ≠ 0 → S' x η = S x η) :
    FullLowBounds.reverseFullGraphOperator S' A = FullLowBounds.reverseFullGraphOperator S A := by
  unfold reverseFullGraphOperator
  rw [fullGraphOperator_phase_congr S S' _ (fun x y η h ↦
    he x y η (fun hz ↦ h (by simp [hz])))]

/-- All compact-frequency forward pairings are unchanged by phase extension,
so the same bounded operator realizes the original phase. Source:
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphDistributionalRealization_phase_congr
    (S S' : E → E → ℝ) (χ : ℕ → E → ℂ) (A : FullAmplitude n r) (T : H →L[ℂ] H)
    (he : ∀ x y η, A x y η ≠ 0 → S' x η = S x η) :
    GraphDistributionalRealization (graphOperator S') χ A T ↔
      GraphDistributionalRealization (graphOperator S) χ A T := by
  have hk (j : ℕ) (u : E → Fin r → ℂ) := graphOperator_phase_congr S S'
    (frequencyCutFullAmplitude (χ j) A)
    (fun x y η h ↦ he x y η (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz]))) u
  simp only [GraphDistributionalRealization, hk]

/-- The original reverse pairings use the same conjugated cutoff and literal
Hilbert adjoint after phase extension. Source: actual-adjoint-trade. -/
theorem reverseGraphDistributionalRealization_phase_congr
    (S S' : E → E → ℝ) (χ : ℕ → E → ℂ) (A : FullAmplitude n r) (T : H →L[ℂ] H)
    (he : ∀ x y η, A x y η ≠ 0 → S' x η = S x η) :
    GraphDistributionalRealization (reverseGraphOperator S') χ A T ↔
      GraphDistributionalRealization (reverseGraphOperator S) χ A T := by
  have hk (j : ℕ) (u : E → Fin r → ℂ) := reverseGraphOperator_phase_congr S S'
    (frequencyCutFullAmplitude (χ j) A)
    (fun x y η h ↦ he x y η (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz]))) u
  simp only [GraphDistributionalRealization, hk]

end JanetCartan.FourierIntegral
