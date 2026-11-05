module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets.Derivatives

/-!
# Joint order-zero symbol bounds for actual source coefficients

The estimate `|a_k|_(0,μ) ≤ C_N decayWeight N k |A|_(0,μ+N)` from
`app:ch_regular_base:thm:actual-calculus`, Step 1, for the final source
operator-series assembly. Jets are actual ordered coordinate derivatives;
source derivatives and all original source cutoffs remain inside `A`.
The covector weight is the equivalent bracket `1 + ‖η‖`, in physical units.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}

/-- The order-zero symbol weight counts only physical covector derivatives,
not output or source derivatives (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def coefficientCovectorWeight (is : List (Fin n ⊕ Fin n)) (η : Euclidean n) : ℝ :=
  (1 + ‖η‖) ^ (is.filter Sum.isRight).length

/-- Positivity of the physical covector weight in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem coefficientCovectorWeight_pos (is : List (Fin n ⊕ Fin n)) (η : Euclidean n) :
    0 < coefficientCovectorWeight is η := by
  unfold coefficientCovectorWeight
  positivity

/-- Primitive mixed derivative budget for the full amplitude, including
source derivatives and the derivatives of all cutoffs already in `A`.
Consumed by `hasCoefficientSymbolBound_matrixCoefficient` in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def HasFullSourceSymbolBound (A : FullAmplitude n r) (μ : ℕ) (B : ℝ) : Prop :=
  ∀ (is : List (Fin n ⊕ Fin n)) (js : List (Fin n)), is.length + js.length ≤ μ →
    ∀ x y η, coefficientCovectorWeight is η *
      ‖matrixAmplitudeCoordinateDerivList js (fun z ↦ fullAmplitudeParameterJet is A x z η) y‖ ≤ B

/-- Uniform joint order-zero symbol bound for a source-independent matrix
amplitude (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def HasCoefficientSymbolBound
    (a : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ) (μ : ℕ) (B : ℝ) : Prop :=
  ∀ is, is.length ≤ μ → ∀ x η,
    coefficientCovectorWeight is η * ‖matrixCoefficientJet is a x η‖ ≤ B

private theorem frobenius_le_entry_sum (M : Matrix (Fin r) (Fin r) ℂ) :
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ i, (∑ j, ‖M i j‖) ^ 2 := Finset.sum_le_sum fun i _ ↦
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ by positivity)

/-- Joint coefficient decay with exactly `μ + N` primitive mixed derivatives.
The proof differentiates the actual integral, retains uniform source support,
and then applies source integration by parts entrywise in Frobenius norm.
No coefficient identities or bounds are hypotheses
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem hasCoefficientSymbolBound_matrixCoefficient (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (μ N : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + N) B)
    (k : Fin n → ℤ) :
    HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ
      ((r : ℝ) ^ 2 * coefficientConstant n N ℓ * B * decayWeight N k) := by
  unfold HasFullSourceSymbolBound at hb
  intro is hi x η
  rw [matrixCoefficientJet_matrixCoefficient A hA]
  have hw := coefficientCovectorWeight_pos is η
  have he (i j : Fin r) :
      ‖matrixCoefficient ℓ (fullAmplitudeParameterJet is A) k x η i j‖ ≤
        coefficientConstant n N ℓ * (B / coefficientCovectorWeight is η) * decayWeight N k := by
    apply norm_scalarCoefficient_le hn hℓ hR
      (supportedInCenteredBox_fullAmplitudeParameterJet A hs is x η i j)
      (contDiff_fullAmplitudeParameterJet_entry A hA is x η i j) N
    · intro y
      apply (norm_matrixEntry_le_frobenius _ i j).trans
      apply (le_div_iff₀ hw).mpr
      have h := hb is [] (by simp only [List.length_nil, add_zero]; omega) x y η
      change coefficientCovectorWeight is η * ‖fullAmplitudeParameterJet is A x y η‖ ≤ B at h
      rwa [mul_comm] at h
    · intro a y
      apply (norm_matrixEntry_le_frobenius
        (matrixAmplitudeCoordinateDerivList (List.replicate N a)
          (fun z ↦ fullAmplitudeParameterJet is A x z η) y) i j).trans
      apply (le_div_iff₀ hw).mpr
      have h := hb is (List.replicate N a) (by simp only [List.length_replicate]; omega) x y η
      rwa [mul_comm] at h
  have hm : ‖matrixCoefficient ℓ (fullAmplitudeParameterJet is A) k x η‖ ≤
      (r : ℝ) ^ 2 * coefficientConstant n N ℓ *
        (B / coefficientCovectorWeight is η) * decayWeight N k := by
    calc
      _ ≤ ∑ i, ∑ j, ‖matrixCoefficient ℓ (fullAmplitudeParameterJet is A) k x η i j‖ :=
        frobenius_le_entry_sum _
      _ ≤ ∑ _i : Fin r, ∑ _j : Fin r,
          coefficientConstant n N ℓ * (B / coefficientCovectorWeight is η) * decayWeight N k :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ he i j
      _ = _ := by simp; ring
  calc
    _ ≤ coefficientCovectorWeight is η * ((r : ℝ) ^ 2 * coefficientConstant n N ℓ *
        (B / coefficientCovectorWeight is η) * decayWeight N k) :=
      mul_le_mul_of_nonneg_left hm hw.le
    _ = _ := by field_simp

/-- The source reserve `n + 2` is fixed independently of the requested
output/covector order `μ`, as used by the low operator-series estimate in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem hasCoefficientSymbolBound_matrixCoefficient_lowReserve
    (hn : 0 < n) {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (k : Fin n → ℤ) :
    HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ
      ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ * B * decayWeight (lowReserve n) k) :=
  hasCoefficientSymbolBound_matrixCoefficient hn hℓ hR A hs hA μ (lowReserve n) hb k

/-- Joint order-zero seminorm of a source-independent matrix amplitude.
As with real `sSup`, estimates use a finite primitive bound to certify
boundedness (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def coefficientSymbolSeminorm
    (a : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ) (μ : ℕ) : ℝ :=
  sSup (insert 0 {b | ∃ is, is.length ≤ μ ∧ ∃ x η,
    b = coefficientCovectorWeight is η * ‖matrixCoefficientJet is a x η‖})

/-- The full total-order seminorm, counting source, output, and physical
covector derivatives together (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def fullSourceSymbolSeminorm (A : FullAmplitude n r) (μ : ℕ) : ℝ :=
  sSup (insert 0 {b | ∃ is js, is.length + js.length ≤ μ ∧ ∃ x y η,
    b = coefficientCovectorWeight is η *
      ‖matrixAmplitudeCoordinateDerivList js (fun z ↦ fullAmplitudeParameterJet is A x z η) y‖})

private theorem full_bound_nonneg {A : FullAmplitude n r} {μ : ℕ} {B : ℝ}
    (hb : HasFullSourceSymbolBound A μ B) : 0 ≤ B :=
  (mul_nonneg (coefficientCovectorWeight_pos [] (0 : Euclidean n)).le (norm_nonneg _)).trans
    (hb [] [] (by simp) 0 0 0)

/-- A finite primitive bound makes the actual full seminorm a bound for
every allowed mixed derivative; consumed by the coefficient seminorm estimate
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem hasFullSourceSymbolBound_seminorm {A : FullAmplitude n r} {μ : ℕ} {B : ℝ}
    (hb : HasFullSourceSymbolBound A μ B) :
    HasFullSourceSymbolBound A μ (fullSourceSymbolSeminorm A μ) := by
  intro is js hij x y η
  apply le_csSup
  · refine ⟨B, ?_⟩
    intro b hb'
    rcases hb' with rfl | ⟨is, js, hij, x, y, η, rfl⟩
    · exact full_bound_nonneg hb
    · exact hb is js hij x y η
  · exact Set.mem_insert_of_mem _ ⟨is, js, hij, x, y, η, rfl⟩

/-- Uniform weighted bounds imply the same bound for the actual coefficient
seminorm (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem coefficientSymbolSeminorm_le_of_bound
    {a : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ} {μ : ℕ} {B : ℝ}
    (hb : HasCoefficientSymbolBound a μ B) : coefficientSymbolSeminorm a μ ≤ B := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro b hb'
  rcases hb' with rfl | ⟨is, hi, x, η, rfl⟩
  · exact (mul_nonneg (coefficientCovectorWeight_pos [] (0 : Euclidean n)).le
      (norm_nonneg _)).trans (hb [] (by simp) 0 0)
  · exact hb is hi x η

/-- The joint order-zero symbol estimate for actual source coefficients:
`|a_k|_(0,μ) ≤ C_N decayWeight N k |A|_(0,μ+N)`.
The finite bound is on primitive mixed derivatives of `A`, not on coefficients;
`C_N = r² * coefficientConstant n N ℓ` is independent of `μ`.
Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem coefficientSymbolSeminorm_matrixCoefficient_le
    (hn : 0 < n) {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (μ N : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + N) B)
    (k : Fin n → ℤ) :
    coefficientSymbolSeminorm (matrixCoefficient ℓ A k) μ ≤
      ((r : ℝ) ^ 2 * coefficientConstant n N ℓ) * decayWeight N k *
        fullSourceSymbolSeminorm A (μ + N) := by
  have h := coefficientSymbolSeminorm_le_of_bound
    (hasCoefficientSymbolBound_matrixCoefficient hn hℓ hR A hs hA μ N
      (hasFullSourceSymbolBound_seminorm hb) k)
  convert h using 1
  ring

end JanetCartan.FourierIntegral.SourceExpansion
