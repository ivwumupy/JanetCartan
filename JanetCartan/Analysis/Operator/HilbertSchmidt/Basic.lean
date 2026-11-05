module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert–Schmidt sums and positive traces

The operator facts used in `app:ch_waves:thm:sampling`. The real-valued sums below
are used with their summability hypotheses; a divergent real `tsum` is not a trace.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Parseval in squared-norm form, used in `app:ch_waves:thm:sampling`. -/
theorem hilbertBasis_hasSum_sq_inner (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i ↦ ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (b.hasSum_inner_mul_inner x x).mapL (RCLike.reCLM : 𝕜 →L[ℝ] ℝ)
  convert h using 1
  · ext i
    simp only [RCLike.reCLM_apply]
    rw [← inner_conj_symm (b i) x, RCLike.mul_conj]
    simpa using norm_inner_symm (𝕜 := 𝕜) (b i) x
  · simp [inner_self_eq_norm_sq_to_K]

variable [CompleteSpace E] [CompleteSpace F]
/-- Squared Hilbert–Schmidt sum in a Hilbert basis (`app:ch_waves:thm:sampling`).
Use together with `IsHilbertSchmidt` to exclude divergent sums. -/
def hilbertSchmidtSq (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) : ℝ :=
  ∑' i, ‖T (b i)‖ ^ 2

/-- Summability of squared images of a Hilbert basis (`app:ch_waves:thm:sampling`). -/
def IsHilbertSchmidt (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) : Prop :=
  Summable (fun i ↦ ‖T (b i)‖ ^ 2)

/-- Diagonal sum for a positive operator (`app:ch_waves:thm:sampling`).
Positivity and summability must be supplied when using this as a finite trace. -/
def positiveTrace (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] F) : ℝ :=
  ∑' i, RCLike.re (inner 𝕜 (b i) (A (b i)))

/-- The diagonal sum of `TT*` is the squared Hilbert–Schmidt sum of `T*`
(`app:ch_waves:thm:sampling`). -/
theorem positiveTrace_normal (b : HilbertBasis ι 𝕜 F) (T : E →L[𝕜] F) :
    positiveTrace b (T ∘L T.adjoint) = hilbertSchmidtSq b T.adjoint := by
  simp only [positiveTrace, hilbertSchmidtSq, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Taking adjoints preserves the Hilbert–Schmidt sum, with independently chosen
input and output bases (`app:ch_waves:thm:sampling`). -/
theorem isHilbertSchmidt_adjoint (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) (T : E →L[𝕜] F) (hT : IsHilbertSchmidt b T) :
    IsHilbertSchmidt c T.adjoint ∧
      hilbertSchmidtSq c T.adjoint = hilbertSchmidtSq b T := by
  let f : ι × κ → ℝ := fun p ↦ ‖inner 𝕜 (c p.2) (T (b p.1))‖ ^ 2
  have hf : Summable f := (summable_prod_of_nonneg (fun _ ↦ sq_nonneg _)).mpr
    ⟨fun i ↦ (hilbertBasis_hasSum_sq_inner c (T (b i))).summable,
     by simpa only [IsHilbertSchmidt, (hilbertBasis_hasSum_sq_inner c _).tsum_eq] using hT⟩
  have heq (j : κ) : (∑' i, f (i, j)) = ‖T.adjoint (c j)‖ ^ 2 := by
    simp only [f, ← T.adjoint_inner_left, norm_inner_symm]
    exact (hilbertBasis_hasSum_sq_inner b _).tsum_eq
  constructor
  · have hf' : Summable (fun j ↦ ∑' i, f (i, j)) :=
      ((summable_prod_of_nonneg (fun p : κ × ι ↦ sq_nonneg (‖inner 𝕜 (c p.1) (T (b p.2))‖))).mp hf.prod_symm).2
    simpa only [IsHilbertSchmidt, heq] using hf'
  · unfold hilbertSchmidtSq
    calc
      (∑' j, ‖T.adjoint (c j)‖ ^ 2) = ∑' j, ∑' i, f (i, j) := by simp only [heq]
      _ = ∑' i, ∑' j, f (i, j) := hf.tsum_comm
      _ = ∑' i, ‖T (b i)‖ ^ 2 := by
        simp only [f, (hilbertBasis_hasSum_sq_inner c _).tsum_eq]

end JanetCartan

namespace JanetCartan

variable {𝕜 E F G ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Postcomposition bounds the Hilbert–Schmidt sum (`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.comp_left {b : HilbertBasis ι 𝕜 E} {T : E →L[𝕜] F}
    (hT : IsHilbertSchmidt b T) (S : F →L[𝕜] G) :
    IsHilbertSchmidt b (S ∘L T) ∧
      hilbertSchmidtSq b (S ∘L T) ≤ ‖S‖ ^ 2 * hilbertSchmidtSq b T := by
  have h (i : ι) : ‖(S ∘L T) (b i)‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖T (b i)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.comp_apply, mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm (T (b i))) 2
  have hs : IsHilbertSchmidt b (S ∘L T) :=
    (hT.mul_left (‖S‖ ^ 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _) h
  exact ⟨hs, (hs.tsum_le_tsum h (hT.mul_left _)).trans_eq (tsum_mul_left)⟩

/-- Basis independence of the Hilbert–Schmidt sum (`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.change_basis {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) (c : HilbertBasis κ 𝕜 E) :
    IsHilbertSchmidt c T ∧ hilbertSchmidtSq c T = hilbertSchmidtSq b T := by
  obtain ⟨w, d, _⟩ := exists_hilbertBasis 𝕜 F
  obtain ⟨hA, heq⟩ := isHilbertSchmidt_adjoint b d T hT
  obtain ⟨hB, heq'⟩ := isHilbertSchmidt_adjoint d c T.adjoint hA
  rw [ContinuousLinearMap.adjoint_adjoint] at hB heq'
  exact ⟨hB, heq'.trans heq⟩

/-- Pointwise adjoint bound from the Hilbert–Schmidt sum
(`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.adjoint_apply_norm_sq_le {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) (y : F) :
    ‖T.adjoint y‖ ^ 2 ≤ hilbertSchmidtSq b T * ‖y‖ ^ 2 := by
  have h (i : ι) : ‖inner 𝕜 (b i) (T.adjoint y)‖ ^ 2 ≤ ‖T (b i)‖ ^ 2 * ‖y‖ ^ 2 := by
    rw [T.adjoint_inner_right]
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := 𝕜) (T (b i)) y) 2
  calc
    ‖T.adjoint y‖ ^ 2 = ∑' i, ‖inner 𝕜 (b i) (T.adjoint y)‖ ^ 2 :=
      (hilbertBasis_hasSum_sq_inner b _).tsum_eq.symm
    _ ≤ ∑' i, ‖T (b i)‖ ^ 2 * ‖y‖ ^ 2 :=
      (hilbertBasis_hasSum_sq_inner b _).summable.tsum_le_tsum h (hT.mul_right _)
    _ = hilbertSchmidtSq b T * ‖y‖ ^ 2 := tsum_mul_right

/-- Operator norm is at most Hilbert–Schmidt norm (`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.opNorm_le {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) :
    ‖T‖ ≤ Real.sqrt (hilbertSchmidtSq b T) := by
  have hp : 0 ≤ hilbertSchmidtSq b T := tsum_nonneg (fun _ ↦ sq_nonneg _)
  have h := T.adjoint.opNorm_le_bound (Real.sqrt_nonneg (hilbertSchmidtSq b T)) (fun y ↦ ?_)
  · simpa using h
  · have hsq := hT.adjoint_apply_norm_sq_le y
    have hroot := Real.sq_sqrt hp
    nlinarith [norm_nonneg (T.adjoint y), norm_nonneg y,
      mul_nonneg (Real.sqrt_nonneg (hilbertSchmidtSq b T)) (norm_nonneg y)]

end JanetCartan
