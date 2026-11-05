module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction

/-!
# Frobenius matrix assembly of the real characteristic columns

The literal complex amplitudes have entries `W₀ᵢⱼ=(w₀ⱼ)ᵢ` and
`W₁ᵢⱼ=i(w₁ⱼ)ᵢ`. Finite column assembly costs only a dimension constant,
with no derivative loss or product of high norms. These are the matrix
inputs of `EvolutionIntegral.SymbolBudgets` in
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

variable {n : ℕ}

/-- Insert a real column into a complex matrix with its Frobenius norm
(`app:ch_regular_base:lem:characteristic-kernel`, matrix amplitude assembly). -/
def complexColumnInjection (j : Fin n) : (Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)).smulRight (Matrix.single i j 1)

/-- Entry formula for the fixed column injection. -/
theorem complexColumnInjection_apply (j : Fin n) (v : Fin n → ℝ) (i k : Fin n) :
    complexColumnInjection j v i k = if k = j then (v i : ℂ) else 0 := by
  by_cases h : k = j
  · simp [complexColumnInjection, _root_.sum_apply, Matrix.sum_apply, Matrix.single_apply,
      h]
  · simp [complexColumnInjection, _root_.sum_apply, Matrix.sum_apply, h, Ne.symm h]

/-- Explicit Frobenius comparison with the sup norm of a real column.
The coarse dimension constant suffices for the fixed-shift symbol budgets. -/
theorem norm_complexColumnInjection_le (j : Fin n) (v : Fin n → ℝ) :
    ‖complexColumnInjection j v‖ ≤ (n : ℝ) * ‖v‖ := by
  have he (i : Fin n) : ‖(Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := by
    simp [Matrix.frobenius_norm_def, Matrix.single_apply, ite_and, apply_ite]
  calc
    ‖complexColumnInjection j v‖ ≤ ∑ i : Fin n, ‖(v i : ℂ) • (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ)‖ := by
      simpa only [complexColumnInjection, _root_.sum_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply] using
          norm_sum_le (s := Finset.univ)
            (f := fun i : Fin n ↦ (v i : ℂ) • (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ))
    _ = ∑ i : Fin n, ‖v i‖ := by simp only [norm_smul, he, mul_one, Complex.norm_real]
    _ ≤ ∑ _i : Fin n, ‖v‖ := Finset.sum_le_sum fun i _ ↦ norm_le_pi_norm v i
    _ = (n : ℝ) * ‖v‖ := by simp

/-- The same dimension cost controls the continuous linear injection. -/
theorem norm_complexColumnInjection (j : Fin n) : ‖complexColumnInjection j‖ ≤ (n : ℝ) :=
  (complexColumnInjection j).opNorm_le_bound (Nat.cast_nonneg n) (norm_complexColumnInjection_le j)

/-- Literal complex matrix whose columns are the given real columns. -/
def complexColumnMatrix (v : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (v j i : ℂ)

/-- Matrix assembly is a finite sum of fixed linear injections. -/
theorem complexColumnMatrix_eq_sum (v : Fin n → Fin n → ℝ) :
    complexColumnMatrix v = ∑ j, complexColumnInjection j (v j) := by
  ext i k
  simp [complexColumnMatrix, Matrix.sum_apply, complexColumnInjection_apply]

/-- Explicit Frobenius bound for the finite matrix assembly. -/
theorem norm_complexColumnMatrix_le (v : Fin n → Fin n → ℝ) :
    ‖complexColumnMatrix v‖ ≤ (n : ℝ) * ∑ j, ‖v j‖ := by
  rw [complexColumnMatrix_eq_sum, Finset.mul_sum]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ ↦ norm_complexColumnInjection_le j (v j))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cNorm_columnInjection_le {K : Set E} (hK : IsCompact K) (m : ℕ)
    (j : Fin n) {v : E → Fin n → ℝ} (hv : ∀ x ∈ K, ContDiffAt ℝ m v x) :
    cNorm K m (complexColumnInjection j ∘ v) ≤ (n : ℝ) * cNorm K m v := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds (fun i _ ↦ mul_nonneg (Nat.cast_nonneg n)
    (sSup_norm_iteratedFDeriv_nonneg K i v))
  intro i hi x hx
  apply ((complexColumnInjection j).norm_iteratedFDeriv_comp_left (hv x hx)
    (by exact_mod_cast hi)).trans
  exact (mul_le_mul_of_nonneg_right (norm_complexColumnInjection j) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hv hi) (mem_image_of_mem _ hx))
      (Nat.cast_nonneg n))

/-- Joint smoothness of the actual complex matrix assembled from its real
columns (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_complexColumnMatrix {U : Set E} {v : Fin n → E → Fin n → ℝ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U) :
    ContDiffOn ℝ ∞ (fun x ↦ complexColumnMatrix (fun j ↦ v j x)) U := by
  simp only [complexColumnMatrix_eq_sum]
  exact ContDiffOn.sum fun j _ ↦ (complexColumnInjection j).contDiff.comp_contDiffOn (hv j)

/-- No derivative reserve is lost when passing the column estimates to the
Frobenius matrix norm. In particular a common bound `D` becomes `n² D`.
This is the finite-dimensional conversion needed by `EvolutionIntegral.SymbolBudgets`. -/
theorem cNorm_complexColumnMatrix_le {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) {v : Fin n → E → Fin n → ℝ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U) (m : ℕ) :
    cNorm K m (fun x ↦ complexColumnMatrix (fun j ↦ v j x)) ≤
      (n : ℝ) * ∑ j, cNorm K m (v j) := by
  have hat (j : Fin n) : ∀ x ∈ K, ContDiffAt ℝ m (v j) x :=
    fun x hx ↦ ((hv j).contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp)
  simp only [complexColumnMatrix_eq_sum, Finset.mul_sum]
  apply (cNorm_sum_le_of_contDiffAt Finset.univ hK
    (fun j _ x hx ↦ (complexColumnInjection j).contDiff.contDiffAt.comp x (hat j x hx))).trans
  exact Finset.sum_le_sum fun j _ ↦ cNorm_columnInjection_le hK m j (hat j)

/-- A common column budget produces a dimension-only Frobenius matrix budget
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem cNorm_complexColumnMatrix_le_uniform {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) {v : Fin n → E → Fin n → ℝ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U) (m : ℕ) {D : ℝ}
    (hD : ∀ j, cNorm K m (v j) ≤ D) :
    cNorm K m (fun x ↦ complexColumnMatrix (fun j ↦ v j x)) ≤ (n : ℝ) ^ 2 * D := by
  apply (cNorm_complexColumnMatrix_le hK hU hKU hv m).trans
  calc
    (n : ℝ) * ∑ j, cNorm K m (v j) ≤ (n : ℝ) * ∑ _j : Fin n, D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hD j) (Nat.cast_nonneg n)
    _ = (n : ℝ) ^ 2 * D := by simp; ring

/-- Multiplication by `i` preserves the joint Frobenius norm of every jet.
This retains the literal factor in `W₁=i b₋₁PW₀` and `PW₁`
(`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem cNorm_I_smul_matrix {K U : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    cNorm K m (fun x ↦ Complex.I • f x) = cNorm K m f := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  apply Set.image_congr
  intro x hx
  have hs := (hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le
    (show (j : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDeriv_const_smul_apply' (a := Complex.I) hs]
  simp only [norm_smul, Complex.norm_I, one_mul]

variable {d : ℕ}

/-- The literal order-zero matrix `W₀`, with its finite real leading columns
complexified (`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilLeadingComplexMatrix (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (q : TwoTimePoint (Euclidean d)) :
    Matrix (Fin n) (Fin n) ℂ :=
  complexColumnMatrix (fun j ↦ pencilLeadingColumn e Q B h Φ C r c σ j q)

/-- The literal correction matrix `W₁=i b₋₁PW₀`, including its factor `i`
(`app:ch_regular_base:eq:two-term-null-identity`). -/
def pencilCorrectionComplexMatrix (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (q : TwoTimePoint (Euclidean d)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • complexColumnMatrix (fun j ↦ pencilCorrectionColumn e Q B h Φ C r c σ j q)

/-- The full physical correction residual `PW₁`, obtained by complexifying
the real physical action on each correction column and retaining `i`.
The exact physical directions keep source time and initial covector fixed
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def pencilCorrectionResidualComplexMatrix (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (q : TwoTimePoint (Euclidean d)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • complexColumnMatrix (fun j ↦
    adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c σ j) q)

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
