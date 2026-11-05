module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Branches

/-!
# Joint seminorm bounds for the exact differentiation branches

The primitive hypotheses here are joint derivatives of the original
frequency-free phase and amplitude. They retain the low reserve: differentiating
a branch does not replace that reserve by a budget depending on the physical
order. These bounds feed the normalized SingleChannel input jets in
`app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds

/-- Explicit coefficient of a branch's joint jet, depending only on primitive
jet constants, never on frequency or history scale
(`app:ch_waves:eq:individual-raw-slice`). -/
def sliceDerivativeJetConstant (a p : ℕ → ℝ) :
    {s : ℕ} → SliceDerivativeBranch s → ℕ → ℝ
  | 0, _, k => a k
  | _ + 1, (b, t), k =>
      if b then ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * p (i + 1) * sliceDerivativeJetConstant a p t (k - i)
      else sliceDerivativeJetConstant a p t (k + 1)

/-- The coefficient uses amplitude orders at most `s+k` and positive phase
orders at most `s+k`, with no infinite profile dependence
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceDerivativeJetConstant_nonneg {a p : ℕ → ℝ} {s : ℕ}
    (b : SliceDerivativeBranch s) (k : ℕ)
    (ha : ∀ j ≤ s + k, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + k → 0 ≤ p j) :
    0 ≤ sliceDerivativeJetConstant a p b k := by
  induction s generalizing k with
  | zero => exact ha k (by omega)
  | succ s ih =>
    rcases b with ⟨b, t⟩
    cases b
    · exact ih t (k + 1) (fun j hj ↦ ha j (by omega))
        (fun j hj hj' ↦ hp j hj (by omega))
    · simp only [sliceDerivativeJetConstant, ↓reduceIte]
      apply Finset.sum_nonneg
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp (i + 1) (by omega) (by omega)))
        (ih t (k - i) (fun j hj ↦ ha j (by omega))
          (fun j hj hj' ↦ hp j hj (by omega)))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem norm_iteratedFDeriv_direction_le {U : Set E} (hU : IsOpen U)
    {A : E → F} (hA : ContDiffOn ℝ ∞ A U) {x : E} (hx : x ∈ U)
    {v : E} (hv : ‖v‖ ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ A y v) x‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) A x‖ := by
  have hd := (hA.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
  apply (norm_iteratedFDeriv_clm_apply_const hd (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact (mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans_eq (one_mul _)

private theorem norm_iteratedFDeriv_phaseFactor_le {U : Set E} (hU : IsOpen U)
    {φ : E → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) {x : E} (hx : x ∈ U)
    {v : E} (hv : ‖v‖ ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ Complex.I * (fderiv ℝ φ y v : ℂ)) x‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) φ x‖ := by
  let T : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro t
    simp [T]
  have hd := ((hφ.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := v))).contDiffAt (hU.mem_nhds hx)
  apply (T.norm_iteratedFDeriv_comp_left hd (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  apply (mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans
  rw [one_mul]
  have hd' := (hφ.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
  apply (norm_iteratedFDeriv_clm_apply_const hd' (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact (mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans_eq (one_mul _)

/-- Joint jets of the actual branches follow from primitive phase and amplitude
grades. The exponent is the one-high excess `s-q+k-R`, with a single fixed
reserve `R`; in particular extra slice derivatives are not charged separately
to every phase factor (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_sliceDerivativeAmplitude_le
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {A : E → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    {s k R : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s)
    (hv : ∀ i, ‖v i‖ ≤ 1) {L : ℝ} (hL : 1 ≤ L) {a p : ℕ → ℝ}
    (ha : ∀ j ≤ s + k, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + k → 0 ≤ p j)
    {x : E} (hx : x ∈ U)
    (hAj : ∀ j ≤ s + k, ‖iteratedFDeriv ℝ j A x‖ ≤ a j * L ^ (j - R))
    (hφj : ∀ j, 1 ≤ j → j ≤ s + k →
      ‖iteratedFDeriv ℝ j φ x‖ ≤ p j * L ^ (j - 1 - R)) :
    ‖iteratedFDeriv ℝ k (sliceDerivativeAmplitude φ A v b) x‖ ≤
      sliceDerivativeJetConstant a p b k * L ^ (s - b.phaseCount + k - R) := by
  induction s generalizing k with
  | zero => simpa [sliceDerivativeAmplitude, sliceDerivativeJetConstant,
      SliceDerivativeBranch.phaseCount] using hAj k (by omega)
  | succ s ih =>
    rcases b with ⟨b, t⟩
    have ht := contDiffOn_sliceDerivativeAmplitude hU hφ hA (Fin.tail v) t
    have htail : ∀ i, ‖Fin.tail v i‖ ≤ 1 := fun i ↦ hv i.succ
    have hq := t.phaseCount_le
    cases b
    · apply (norm_iteratedFDeriv_direction_le hU ht hx (hv 0) k).trans
      have hh := ih (k := k + 1) (Fin.tail v) t htail
        (fun j hj ↦ ha j (by omega)) (fun j hj hj' ↦ hp j hj (by omega))
        (fun j hj ↦ hAj j (by omega)) (fun j hj hj' ↦ hφj j hj (by omega))
      convert hh using 1
      simp only [sliceDerivativeJetConstant, SliceDerivativeBranch.phaseCount,
        Bool.toNat_false, Bool.false_eq_true, ↓reduceIte, zero_add]
      congr 2
      omega
    · have hf : ContDiffOn ℝ ∞
          (fun y ↦ Complex.I * (fderiv ℝ φ y (v 0) : ℂ)) U :=
        contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
          ((hφ.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const))
      have hb := norm_iteratedFDerivWithin_smul_le hf ht hU.uniqueDiffOn hx
        (by simp : (k : ℕ∞ω) ≤ ∞)
      simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at hb
      apply hb.trans
      change _ ≤ (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * p (i + 1) * sliceDerivativeJetConstant a p t (k - i)) *
          L ^ (s + 1 - (1 + t.phaseCount) + k - R)
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hpi := hp (i + 1) (by omega) (by omega)
      have hc := sliceDerivativeJetConstant_nonneg t (k - i)
        (fun j hj ↦ ha j (by omega)) (fun j hj hj' ↦ hp j hj (by omega))
      have hphase := (norm_iteratedFDeriv_phaseFactor_le hU hφ hx (hv 0) i).trans
        (hφj (i + 1) (by omega) (by omega))
      have hamp := ih (k := k - i) (Fin.tail v) t htail
        (fun j hj ↦ ha j (by omega)) (fun j hj hj' ↦ hp j hj (by omega))
        (fun j hj ↦ hAj j (by omega)) (fun j hj hj' ↦ hφj j hj (by omega))
      calc
        _ ≤ (k.choose i : ℝ) * (p (i + 1) * L ^ (i - R)) *
            (sliceDerivativeJetConstant a p t (k - i) *
              L ^ (s - t.phaseCount + (k - i) - R)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hphase (Nat.cast_nonneg _))
            hamp (norm_nonneg _) (by positivity)
        _ = ((k.choose i : ℝ) * p (i + 1) * sliceDerivativeJetConstant a p t (k - i)) *
            L ^ ((i - R) + (s - t.phaseCount + (k - i) - R)) := by
          rw [pow_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (by omega)) (by positivity)

/-- The manuscript's fixed low slice order (`app:ch_waves:thm:wkb`). -/
def rawSliceJetOrder (n : ℕ) : ℕ := 20 * (n + 1)

/-- The fixed parameter order `r_par=M+3` (`app:ch_waves:thm:wkb`). -/
def rawSliceParameterOrder (n : ℕ) : ℕ := rawSliceJetOrder n + 3

/-- The fixed coefficient reserve, independent of the requested physical
order (`app:ch_waves:thm:wkb`). -/
def rawSlicePrimitiveReserve (n Dpr : ℕ) : ℕ := Dpr + rawSliceParameterOrder n + 2

/-- The same fixed reserve pays for every extra slice jet and its parameter
derivative. The finite primitive orders are at most `s+M+1`; the actual
WKB/history producer must supply those primitive grades from coefficient
orders through the corresponding fixed construction shift
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_sliceDerivativeAmplitude_le_fixedReserve
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {A : E → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    {n Dpr s k : ℕ} (hk : k ≤ rawSliceJetOrder n + 1)
    (v : Fin s → E) (b : SliceDerivativeBranch s) (hv : ∀ i, ‖v i‖ ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) {a p : ℕ → ℝ}
    (ha : ∀ j ≤ s + k, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + k → 0 ≤ p j)
    {x : E} (hx : x ∈ U)
    (hAj : ∀ j ≤ s + k, ‖iteratedFDeriv ℝ j A x‖ ≤
      a j * L ^ (j + Dpr - rawSlicePrimitiveReserve n Dpr))
    (hφj : ∀ j, 1 ≤ j → j ≤ s + k → ‖iteratedFDeriv ℝ j φ x‖ ≤
      p j * L ^ (j - 1 + Dpr - rawSlicePrimitiveReserve n Dpr)) :
    ‖iteratedFDeriv ℝ k (sliceDerivativeAmplitude φ A v b) x‖ ≤
      sliceDerivativeJetConstant a p b k * L ^ (s - b.phaseCount) := by
  have hb := norm_iteratedFDeriv_sliceDerivativeAmplitude_le hU hφ hA
    (R := rawSliceParameterOrder n + 2) v b hv hL ha hp hx
    (fun j hj ↦ by simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left,
      ← Nat.sub_sub] using hAj j hj)
    (fun j hj hj' ↦ by simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left,
      ← Nat.sub_sub] using hφj j hj hj')
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (sliceDerivativeJetConstant_nonneg b k ha hp)
  apply pow_le_pow_right₀ hL
  simp only [rawSliceParameterOrder] at *
  omega

/-- At `L=1`, bounded primitive joint jets through exactly `s+k` control a
branch's `k` additional jets. Taking `k≤M+1` includes the parameter derivative
in the finite-order alternative of `app:ch_waves:eq:individual-raw-slice`.
This finite bounded-jet alternative does not replace the fixed history reserve. -/
theorem norm_iteratedFDeriv_sliceDerivativeAmplitude_le_of_bounded_jets
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {A : E → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    {s k : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s)
    (hv : ∀ i, ‖v i‖ ≤ 1) {a p : ℕ → ℝ}
    (ha : ∀ j ≤ s + k, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + k → 0 ≤ p j)
    {x : E} (hx : x ∈ U)
    (hAj : ∀ j ≤ s + k, ‖iteratedFDeriv ℝ j A x‖ ≤ a j)
    (hφj : ∀ j, 1 ≤ j → j ≤ s + k → ‖iteratedFDeriv ℝ j φ x‖ ≤ p j) :
    ‖iteratedFDeriv ℝ k (sliceDerivativeAmplitude φ A v b) x‖ ≤
      sliceDerivativeJetConstant a p b k := by
  simpa only [one_pow, mul_one] using norm_iteratedFDeriv_sliceDerivativeAmplitude_le
    hU hφ hA (R := 0) v b hv (L := 1) le_rfl ha hp hx
    (fun j hj ↦ by simpa only [one_pow, mul_one] using hAj j hj)
    (fun j hj hj' ↦ by simpa only [one_pow, mul_one] using hφj j hj hj')

end JanetCartan.RawPrimary.SliceBounds
