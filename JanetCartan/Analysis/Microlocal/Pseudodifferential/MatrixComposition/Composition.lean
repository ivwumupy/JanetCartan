module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Basic

/-!
# Exact finite matrix composition

The ordered finite contraction in `app:ch_regular_base:thm:actual-calculus`
is proved by distributing only absolutely convergent integrals.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

omit [Fintype I] in
/-- `app:ch_regular_base:thm:actual-calculus`: exact composition with a
source-independent matrix inner symbol, retaining both Fubini conditions. -/
theorem matrixFullAmplitudeOperator_comp_sourceIndependentOperator
    (c : V → V → V → Matrix I J ℂ) (b : V → V → Matrix J K ℂ)
    (u : K → 𝓢(V, ℂ)) (x : V)
    (hy : ∀ i j k ξ, Integrable (fun p : V × V ↦
      ((𝓕 (u k) : 𝓢(V, ℂ)) p.2 * symbolPlaneWave (fun y η ↦ b y η j k) p.2 p.1) * c x p.1 ξ i j))
    (hξ : ∀ i j k, Integrable (fun p : V × V ↦ (𝓕 (u k) : 𝓢(V, ℂ)) p.2 •
      sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j)
        (symbolPlaneWave (fun y η ↦ b y η j k) p.2) x p.1)) :
    matrixFullAmplitudeOperator c (matrixSourceIndependentOperator b u) x =
      matrixSourceIndependentOperator (matrixComposedSymbol c b) u x := by
  have hinner (i j k) := integrable_fullAmplitudeOperator_inner
    (fun x y ξ ↦ c x y ξ i j) (fun y η ↦ b y η j k) (u k) x (hy i j k) (hξ i j k)
  have hcomp (i j k) := integrable_composedSymbol_test
    (fun x y ξ ↦ c x y ξ i j) (fun y η ↦ b y η j k) (u k) x (hξ i j k)
  funext i
  simp only [matrixFullAmplitudeOperator, matrixSourceIndependentOperator]
  have hsum (j : J) := fullAmplitudeOperator_sum (fun x y ξ ↦ c x y ξ i j)
    (fun k ↦ sourceIndependentOperator (fun y η ↦ b y η j k) (u k)) x
    (fun k ↦ (hinner i j k).1) (fun k ↦ (hinner i j k).2)
  simp_rw [hsum]
  have heq (j : J) (k : K) := fullAmplitudeOperator_comp_sourceIndependentOperator
    (fun x y ξ ↦ c x y ξ i j) (fun y η ↦ b y η j k) (u k) x (hy i j k) (hξ i j k)
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [sourceIndependentOperator, Real.fourierInv_eq, matrixComposedSymbol,
    Finset.smul_sum]
  symm
  apply integral_finsetSum
  intro j _
  simpa only [inner_neg_right, neg_neg] using
    (Real.fourierIntegral_convergent_iff (-x)).2 (hcomp i j k)

omit [Fintype I] in
/-- `app:ch_regular_base:thm:actual-calculus`: exact matrix composition from
separate primitive source derivative bounds and a compact physical source mask.
The bounds are entrywise, allowing different rectangular matrix dimensions;
the derivative reserve is the scalar reserve `m + dim V + 1`. -/
theorem matrixFullAmplitudeOperator_comp_of_sourceSymbolBounds
    (a : V → V → V → Matrix I J ℂ) (b : V → V → Matrix J K ℂ)
    (χ : V → ℂ) (u : K → 𝓢(V, ℂ)) (x : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ∀ i j, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1 i j))
    (hb : ∀ j k, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ b p.1 p.2 j k))
    (B C : ℝ)
    (hB : ∀ j k d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y η,
      ‖iteratedFDeriv ℝ d (fun z ↦ b z η j k) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ i j d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ d (fun z ↦ a x z ξ i j) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    matrixFullAmplitudeOperator (fun x y ξ ↦ χ y • a x y ξ)
      (matrixSourceIndependentOperator b u) x =
      matrixSourceIndependentOperator (matrixComposedSymbol (fun x y ξ ↦ χ y • a x y ξ) b) u x := by
  have h (i j k) := composition_integrable_of_sourceSymbolBounds
    (fun x y ξ ↦ a x y ξ i j) (fun y η ↦ b y η j k) χ (u k) x m l hχ hχc
    (ha i j) (hb j k) B C (hB j k) (hC i j)
  exact matrixFullAmplitudeOperator_comp_sourceIndependentOperator _ b u x
    (fun i j k ↦ (h i j k).1) (fun i j k ↦ (h i j k).2)
end JanetCartan.Pseudodifferential
