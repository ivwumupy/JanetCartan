module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Composition
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.MatrixIntegrals
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Schwartz
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Bounds

/-!
# Actual matrix pseudodifferential composition

For `app:ch_regular_base:thm:actual-calculus`, item (3), construct the exact
source-independent composite matrix symbol and identify the operators with
actual Bochner integrals. Separate primitive source jets and a compact physical
mask discharge the convergence conditions, using `m + dim V + 1` derivatives.
All Fourier phases use the unit-frequency `2π` convention. Matrices carry the
Frobenius norm. This is an exact composition result; sharp symbol order and
Sobolev estimates belong to the parent finite calculus assembly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- `app:ch_regular_base:thm:actual-calculus`: the composite symbol is the
ordered iterated matrix integral, with convergence supplied by separate
primitive source bounds and the compact source mask. -/
theorem matrixComposedSymbol_eq_integral_of_sourceSymbolBounds
    (a : V → V → V → Matrix I J ℂ) (b : V → V → Matrix J K ℂ)
    (χ : V → ℂ) (x η : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ∀ i j, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1 i j))
    (hb : ∀ j k, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ b p.1 p.2 j k))
    (B C : ℝ)
    (hB : ∀ j k d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y,
      ‖iteratedFDeriv ℝ d (fun z ↦ b z η j k) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ i j d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ d (fun z ↦ a x z ξ i j) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    matrixComposedSymbol (fun x y ξ ↦ χ y • a x y ξ) b x η =
      Real.fourierChar (-⟪η, x⟫) • ∫ ξ, Real.fourierChar ⟪ξ, x⟫ •
        ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
          (Real.fourierChar ⟪η, y⟫ • ((χ y • a x y ξ) * b y η)) := by
  apply matrixComposedSymbol_eq_integral
  · intro i j k ξ
    have haξ := (ha i j).comp (f := fun y : V ↦ (ξ, y)) (by fun_prop)
    have hbη := (hb j k).comp (f := fun y : V ↦ (y, η)) (by fun_prop)
    exact integrable_symbolPlaneWave_mask (fun y ↦ a x y ξ i j) (fun y η ↦ b y η j k)
      χ η (m + Module.finrank ℝ V + 1) haξ hbη hχ hχc
  · intro i j k
    exact integrable_composedSymbol_frequency_of_sourceSymbolBounds
      (fun x y ξ ↦ a x y ξ i j) (fun y η ↦ b y η j k) χ x η m l hχ hχc
      (ha i j) (hb j k) B C (hB j k) (hC i j)

/-- `app:ch_regular_base:thm:actual-calculus`: exact composition of the actual
vector-valued Bochner integrals, with every convergence premise discharged by
separate primitive bounds. Finite families of Schwartz functions are the
coordinates of the finite-dimensional complex input datum. -/
theorem matrixComposition_integral_of_sourceSymbolBounds
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
    (∫ ξ, Real.fourierChar ⟪ξ, x⟫ • ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
      (χ y • a x y ξ).mulVec
        (∫ η, Real.fourierChar ⟪η, y⟫ • (b y η).mulVec (fun k ↦ (𝓕 (u k) : 𝓢(V, ℂ)) η))) =
    ∫ η, Real.fourierChar ⟪η, x⟫ •
      (matrixComposedSymbol (fun x y ξ ↦ χ y • a x y ξ) b x η).mulVec
        (fun k ↦ (𝓕 (u k) : 𝓢(V, ℂ)) η) := by
  let c := fun x y ξ ↦ χ y • a x y ξ
  have h (i j k) := composition_integrable_of_sourceSymbolBounds
    (fun x y ξ ↦ a x y ξ i j) (fun y η ↦ b y η j k) χ (u k) x m l hχ hχc
    (ha i j) (hb j k) B C (hB j k) (hC i j)
  have hi (i j k) := integrable_fullAmplitudeOperator_inner
    (fun x y ξ ↦ c x y ξ i j) (fun y η ↦ b y η j k) (u k) x (h i j k).1 (h i j k).2
  have hbi (y : V) (j : J) (k : K) :
      Integrable (fun η ↦ (𝓕 (u k) : 𝓢(V, ℂ)) η * b y η j k) := by
    have hB0 : 0 ≤ B := by
      have hh := (norm_nonneg _).trans (hB j k 0 (Nat.zero_le _) 0 0)
      simpa using hh
    apply integrable_sourceIndependentOperator_symbol (fun y η ↦ b y η j k) (u k) y
      ((hb j k).continuous.comp (f := fun η ↦ (y, η)) (by fun_prop)) (B * 2 ^ (l - 1)) l
    intro η
    have hh : ‖b y η j k‖ ≤ B * (1 + ‖η‖) ^ l := by
      simpa only [norm_iteratedFDeriv_zero] using hB j k 0 (Nat.zero_le _) y η
    apply hh.trans
    calc
      _ ≤ B * (2 ^ (l - 1) * (1 + ‖η‖ ^ l)) := by
        apply mul_le_mul_of_nonneg_left _ hB0
        simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg η) l
      _ = _ := by ring
  have hfull := matrixFullAmplitudeOperator_eq_integral c (matrixSourceIndependentOperator b u) x
    (fun i j ξ ↦ by
      simp only [matrixSourceIndependentOperator, Finset.sum_mul]
      exact integrable_finsetSum _ (fun k _ ↦ (hi i j k).1 ξ))
    (fun i j ↦ by
      change Integrable (fun ξ ↦ sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j)
        (fun y ↦ ∑ k, sourceIndependentOperator (fun y η ↦ b y η j k) (u k) y) x ξ)
      have hs (ξ : V) := sourceAmplitudeTransform_sum (fun x y ξ ↦ c x y ξ i j)
        (fun k ↦ sourceIndependentOperator (fun y η ↦ b y η j k) (u k)) x ξ
        (fun k ↦ (hi i j k).1 ξ)
      simp_rw [hs]
      exact integrable_finsetSum _ (fun k _ ↦ (hi i j k).2))
  have hcomp (i : I) (k : K) : Integrable (fun η ↦ (𝓕 (u k) : 𝓢(V, ℂ)) η *
      matrixComposedSymbol c b x η i k) := by
    simp only [matrixComposedSymbol, Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ ↦ integrable_composedSymbol_test
      (fun x y ξ ↦ c x y ξ i j) (fun y η ↦ b y η j k) (u k) x (h i j k).2)
  simp_rw [← matrixSourceIndependentOperator_eq_integral b u _ (hbi _)]
  rw [← hfull, matrixFullAmplitudeOperator_comp_of_sourceSymbolBounds a b χ u x m l
    hχ hχc ha hb B C hB hC]
  exact matrixSourceIndependentOperator_eq_integral _ u x hcomp
/-- `app:ch_regular_base:thm:actual-calculus`: exact composition of actual
Bochner integrals on finite-dimensional vector-valued Schwartz data. -/
theorem matrixComposition_integral_schwartz_of_sourceSymbolBounds
    (a : V → V → V → Matrix I J ℂ) (b : V → V → Matrix J K ℂ)
    (χ : V → ℂ) (u : 𝓢(V, K → ℂ)) (x : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ∀ i j, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1 i j))
    (hb : ∀ j k, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ b p.1 p.2 j k))
    (B C : ℝ)
    (hB : ∀ j k d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y η,
      ‖iteratedFDeriv ℝ d (fun z ↦ b z η j k) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ i j d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ d (fun z ↦ a x z ξ i j) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    (∫ ξ, Real.fourierChar ⟪ξ, x⟫ • ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
      (χ y • a x y ξ).mulVec
        (∫ η, Real.fourierChar ⟪η, y⟫ • (b y η).mulVec ((𝓕 u : 𝓢(V, K → ℂ)) η))) =
    ∫ η, Real.fourierChar ⟪η, x⟫ •
      (matrixComposedSymbol (fun x y ξ ↦ χ y • a x y ξ) b x η).mulVec
        ((𝓕 u : 𝓢(V, K → ℂ)) η) := by
  have h := matrixComposition_integral_of_sourceSymbolBounds a b χ (matrixSchwartzCoordinates u)
    x m l hχ hχc ha hb B C hB hC
  simpa only [fourier_matrixSchwartzCoordinates] using h
/-- `app:ch_regular_base:thm:actual-calculus`: exact matrix composition on
vector Schwartz data from separate primitive Frobenius matrix jet bounds.
The conversion to entries costs only a fixed matrix dimension constant, and
uses the same source derivative reserve `m + dim V + 1`. -/
theorem matrixComposition_integral_schwartz_of_frobeniusBounds
    (a : V → V → V → Matrix I J ℂ) (b : V → V → Matrix J K ℂ)
    (χ : V → ℂ) (u : 𝓢(V, K → ℂ)) (x : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1))
    (hb : ContDiff ℝ (m + Module.finrank ℝ V + 1) (Function.uncurry b))
    (B C : ℝ)
    (hB : ∀ d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y η,
      ‖iteratedFDeriv ℝ d (fun z ↦ b z η) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ d, d ≤ m + Module.finrank ℝ V + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ d (fun z ↦ a x z ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    (∫ ξ, Real.fourierChar ⟪ξ, x⟫ • ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
      (χ y • a x y ξ).mulVec
        (∫ η, Real.fourierChar ⟪η, y⟫ • (b y η).mulVec ((𝓕 u : 𝓢(V, K → ℂ)) η))) =
    ∫ η, Real.fourierChar ⟪η, x⟫ •
      (matrixComposedSymbol (fun x y ξ ↦ χ y • a x y ξ) b x η).mulVec
        ((𝓕 u : 𝓢(V, K → ℂ)) η) := by
  apply matrixComposition_integral_schwartz_of_sourceSymbolBounds a b χ u x m l hχ hχc
    (fun i j ↦ (matrixEntryCLM i j).contDiff.comp ha)
    (fun j k ↦ (matrixEntryCLM j k).contDiff.comp hb)
    (matrixEntryBound J K * B) (matrixEntryBound I J * C)
  · intro j k d hd y η
    have hs := hb.comp (f := fun z : V ↦ (z, η)) (by fun_prop)
    apply (norm_iteratedFDeriv_matrix_entry_le (fun z ↦ b z η) _ d hd hs y j k).trans
    exact (mul_le_mul_of_nonneg_left (hB d hd y η) matrixEntryBound_nonneg).trans_eq (by ring)
  · intro i j d hd y ξ
    have hs := ha.comp (f := fun z : V ↦ (ξ, z)) (by fun_prop)
    apply (norm_iteratedFDeriv_matrix_entry_le (fun z ↦ a x z ξ) _ d hd hs y i j).trans
    exact (mul_le_mul_of_nonneg_left (hC d hd y ξ) matrixEntryBound_nonneg).trans_eq (by ring)
end JanetCartan.Pseudodifferential
