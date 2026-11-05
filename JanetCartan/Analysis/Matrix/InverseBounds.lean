module

public import JanetCartan.Analysis.Matrix.InverseBounds.Algebra
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite derivative budgets for matrix inversion

The inversion step of `app:lem:elementary-interpolation-jets`, in the Frobenius
norm. A uniform bound on the inverse is the quantitative gap hypothesis.
The coefficient bound is factorial. Polynomial finite-order bounds hold on
arbitrary compact working sets; the one-high tame bounds on positive-radius
closed balls use the proved scalar interpolation theorem. Taking `k = r` gives
no derivative loss, while `k = r + c` permits any fixed finite loss. Smooth
fields on the ambient space represent the extensions used on buffered charts.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:elementary-interpolation-jets`: inversion is smooth at each
nonsingular matrix, in the Frobenius topology. -/
theorem contDiffAt_matrix_inv {a : Matrix ι ι ℝ} (ha : IsUnit a) {N : ℕ∞ω} :
    ContDiffAt ℝ N (fun b : Matrix ι ι ℝ ↦ b⁻¹) a := by
  rcases ha with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using (contDiffAt_ringInverse ℝ u)

/-- `app:lem:elementary-interpolation-jets`: smoothness of a nonsingular matrix
field's inverse, with exactly the same derivative budget. -/
theorem contDiffOn_matrix_inv {f : E → Matrix ι ι ℝ} {s : Set E} {N : ℕ∞ω}
    (hf : ContDiffOn ℝ N f s) (hu : ∀ x ∈ s, IsUnit (f x)) :
    ContDiffOn ℝ N (fun x ↦ (f x)⁻¹) s := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
    (contDiffOn_ringInverse_units.comp hf hu)

/-- `app:lem:elementary-interpolation-jets`: the matrix inversion coefficient has
order-`r` derivative bounded by `r! ‖A⁻¹‖^(r+1)` in the Frobenius norm. -/
theorem norm_iteratedFDeriv_matrix_inv_le (r : ℕ) {a : Matrix ι ι ℝ}
    (ha : IsUnit a) :
    ‖iteratedFDeriv ℝ r (fun b : Matrix ι ι ℝ ↦ b⁻¹) a‖ ≤
      (r.factorial : ℝ) * ‖a⁻¹‖ ^ (r + 1) := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    norm_iteratedFDeriv_ringInverse_le r ha

/-- `app:lem:elementary-interpolation-jets`: one uniform bound for all inversion
coefficient derivatives through order `r`, suitable for composition estimates. -/
theorem norm_iteratedFDeriv_matrix_inv_le_uniform {r i : ℕ} (hi : i ≤ r)
    {a : Matrix ι ι ℝ} (ha : IsUnit a) {B : ℝ} (hB : ‖a⁻¹‖ ≤ B) :
    ‖iteratedFDeriv ℝ i (fun b : Matrix ι ι ℝ ↦ b⁻¹) a‖ ≤
      (r.factorial : ℝ) * max 1 B ^ (r + 1) := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    norm_iteratedFDeriv_ringInverse_le_uniform hi ha
      (by simpa only [Matrix.nonsing_inv_eq_ringInverse] using hB)

/-- `app:lem:elementary-interpolation-jets`: the ordered first derivative of
inversion is the map `H ↦ -A⁻¹ H A⁻¹`. -/
theorem hasFDerivAt_matrix_inv {a : Matrix ι ι ℝ} (ha : IsUnit a) :
    HasFDerivAt (fun b : Matrix ι ι ℝ ↦ b⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℝ) a⁻¹ a⁻¹) a := by
  rcases ha with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

/-- `app:lem:elementary-interpolation-jets`: an explicit inversion budget for
matrix fields, using only derivatives through order `r`. -/
def matrixInverseDerivativeBound (r : ℕ) (B D : ℝ) : ℝ :=
  (r.factorial : ℝ) * ((r.factorial : ℝ) * max 1 B ^ (r + 1)) * D ^ r

/-- `app:lem:elementary-interpolation-jets`: quantitative inversion on any domain
with unique derivatives, assuming a bound for the inverse and the input jets. -/
theorem norm_iteratedFDerivWithin_matrix_inv_le {f : E → Matrix ι ι ℝ} {s : Set E}
    {r : ℕ} (hf : ContDiffOn ℝ r f s) (hs : UniqueDiffOn ℝ s)
    (hu : ∀ x ∈ s, IsUnit (f x)) {x : E} (hx : x ∈ s)
    {B D : ℝ} (hB : ‖(f x)⁻¹‖ ≤ B)
    (hD : ∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin ℝ r (fun y ↦ (f y)⁻¹) s x‖ ≤
      matrixInverseDerivativeBound r B D := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse, matrixInverseDerivativeBound] using
    norm_iteratedFDerivWithin_ringInverse_comp_le hf hs hu hx
      (by simpa only [Matrix.nonsing_inv_eq_ringInverse] using hB) hD

/-- `app:lem:elementary-interpolation-jets`: the field estimate in terms of
ordinary derivatives on an open working domain. -/
theorem norm_iteratedFDeriv_matrix_field_inv_le {f : E → Matrix ι ι ℝ} {s : Set E}
    {r : ℕ} (hf : ContDiffOn ℝ r f s) (hs : IsOpen s)
    (hu : ∀ x ∈ s, IsUnit (f x)) {x : E} (hx : x ∈ s)
    {B D : ℝ} (hB : ‖(f x)⁻¹‖ ≤ B)
    (hD : ∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ r (fun y ↦ (f y)⁻¹) x‖ ≤
      matrixInverseDerivativeBound r B D := by
  rw [← iteratedFDerivWithin_of_isOpen r hs hx]
  apply norm_iteratedFDerivWithin_matrix_inv_le hf hs.uniqueDiffOn hu hx hB
  intro i hi hir
  rw [iteratedFDerivWithin_of_isOpen i hs hx]
  exact hD i hi hir

/-- `app:lem:elementary-interpolation-jets`: a uniform finite-jet bound in the
project's `cNorm`. No derivative beyond order `r` is needed. -/
theorem cNorm_matrix_inv_le {f : E → Matrix ι ι ℝ} {s K : Set E} {r : ℕ}
    (hf : ContDiffOn ℝ r f s) (hs : IsOpen s) (hKs : K ⊆ s)
    (hu : ∀ x ∈ s, IsUnit (f x)) {B D : ℝ} (hD0 : 0 ≤ D)
    (hB : ∀ x ∈ K, ‖(f x)⁻¹‖ ≤ B)
    (hD : ∀ x ∈ K, ∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    cNorm K r (fun x ↦ (f x)⁻¹) ≤
      ∑ i ∈ Finset.range (r + 1), matrixInverseDerivativeBound i B D := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp only [cNorm, Set.image_empty, Real.sSup_empty, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun i _ ↦ by unfold matrixInverseDerivativeBound; positivity
  apply Finset.sum_le_sum
  intro i hi
  apply csSup_le (hK.image _)
  rintro _ ⟨x, hx, rfl⟩
  have hir : i ≤ r := Finset.mem_range_succ_iff.mp hi
  exact norm_iteratedFDeriv_matrix_field_inv_le (hf.of_le (by exact_mod_cast hir)) hs hu
    (hKs hx) (hB x hx) (fun j hj hji ↦ hD x hx j hj (hji.trans hir))

/-- `app:lem:elementary-interpolation-jets`: on a compact subset of an open working
domain, the inverse has an explicit polynomial bound in the input `C^r` seminorm.
The input and output orders are both `r`. -/
theorem cNorm_matrix_inv_le_of_compact {f : E → Matrix ι ι ℝ} {s K : Set E} {r : ℕ}
    (hf : ContDiffOn ℝ r f s) (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hu : ∀ x ∈ s, IsUnit (f x)) {B : ℝ} (hB : ∀ x ∈ K, ‖(f x)⁻¹‖ ≤ B) :
    cNorm K r (fun x ↦ (f x)⁻¹) ≤ ∑ i ∈ Finset.range (r + 1),
      matrixInverseDerivativeBound i B (max 1 (cNorm K r f)) := by
  apply cNorm_matrix_inv_le hf hs hKs hu (le_trans zero_le_one (le_max_left _ _)) hB
  intro x hx i hi hir
  have hc : ContinuousOn (iteratedFDeriv ℝ i f) K :=
    ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hir) hs.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen i hs).symm).mono hKs
  have hpoint : ‖iteratedFDeriv ℝ i f x‖ ≤ cNorm K r f := by
    apply (le_csSup (hK.bddAbove_image hc.norm) (mem_image_of_mem _ hx)).trans
    apply Finset.single_le_sum _ (Finset.mem_range_succ_iff.mpr hir)
    intro j _
    exact Real.sSup_nonneg (by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg _)
  exact (hpoint.trans (le_max_right _ _)).trans
    (le_self_pow₀ (le_max_left _ _) (by omega))

/-- `app:lem:elementary-interpolation-jets`: the ordered rational operation
`A⁻¹ Q`. Its two arguments are never commuted. -/
def matrixInvMul (f g : E → Matrix ι ι ℝ) : E → Matrix ι ι ℝ :=
  fun x ↦ (f x)⁻¹ * g x

/-- `app:lem:elementary-interpolation-jets`: ordered inverse multiplication
preserves the finite smoothness order. -/
theorem contDiffOn_matrixInvMul {f g : E → Matrix ι ι ℝ} {s : Set E} {N : ℕ∞ω}
    (hf : ContDiffOn ℝ N f s) (hg : ContDiffOn ℝ N g s)
    (hu : ∀ x ∈ s, IsUnit (f x)) : ContDiffOn ℝ N (matrixInvMul f g) s :=
  (contDiffOn_matrix_inv hf hu).mul hg

/-- `app:lem:elementary-interpolation-jets`: a Leibniz budget for the ordered
rational operation `A⁻¹ Q`, using only input jets through order `r`. -/
theorem norm_iteratedFDerivWithin_matrixInvMul_le {f g : E → Matrix ι ι ℝ}
    {s : Set E} {r : ℕ} (hf : ContDiffOn ℝ r f s) (hg : ContDiffOn ℝ r g s)
    (hs : UniqueDiffOn ℝ s) (hu : ∀ x ∈ s, IsUnit (f x)) {x : E} (hx : x ∈ s)
    {B D : ℝ} (hB : ‖(f x)⁻¹‖ ≤ B)
    (hD : ∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D ^ i)
    {q : ℕ → ℝ} (hq : ∀ i, i ≤ r → ‖iteratedFDerivWithin ℝ i g s x‖ ≤ q i) :
    ‖iteratedFDerivWithin ℝ r (matrixInvMul f g) s x‖ ≤
      ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) *
        matrixInverseDerivativeBound i B D * q (r - i) := by
  apply (norm_iteratedFDerivWithin_mul_le (contDiffOn_matrix_inv hf hu) hg hs hx le_rfl).trans
  apply Finset.sum_le_sum
  intro i hi
  have hir : i ≤ r := Finset.mem_range_succ_iff.mp hi
  have hinv := norm_iteratedFDerivWithin_matrix_inv_le
    (hf.of_le (by exact_mod_cast hir)) hs hu hx hB (fun j hj hji ↦ hD j hj (hji.trans hir))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity))
    (hq (r - i) (Nat.sub_le _ _)) (norm_nonneg _)
    (mul_nonneg (by positivity) ((norm_nonneg _).trans hinv))

/-- `app:lem:elementary-interpolation-jets`: the one-high inverse estimate on a
fixed chart ball. The constant is uniform over all fields with the stated low
bound and inverse bound. All coefficient estimates and interpolation premises
are discharged; only input derivatives through `k` occur, and `k = r` is allowed. -/
theorem exists_cNorm_matrix_inv_le_tame_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {r k : ℕ} (hrk : r ≤ k)
    {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → Matrix ι ι ℝ, ContDiff ℝ ∞ f →
      cNorm (Metric.closedBall x ρ) 0 f ≤ M →
      (∀ y ∈ Metric.closedBall x ρ, IsUnit (f y)) →
      (∀ y ∈ Metric.closedBall x ρ, ‖(f y)⁻¹‖ ≤ B) →
        cNorm (Metric.closedBall x ρ) r (fun y ↦ (f y)⁻¹) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) k f) := by
  obtain ⟨K, hK, hbound⟩ := exists_cNorm_comp_le_tame_closedBall
    (F := Matrix ι ι ℝ) (G := Matrix ι ι ℝ) x hρ hrk hM
  let D : ℝ := (r.factorial : ℝ) * max 1 B ^ (r + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + K * D, by positivity, ?_⟩
  intro f hf hfM hu hB
  have hcomp := hbound f hf hfM (fun a ↦ a⁻¹) D hD
    (fun y hy ↦ contDiffAt_matrix_inv (hu y hy))
    (fun j hj y hy ↦ norm_iteratedFDeriv_matrix_inv_le_uniform hj (hu y hy) (hB y hy))
  apply hcomp.trans
  exact mul_le_mul_of_nonneg_right (by linarith)
    (by linarith [CompositionBounds.cNorm_nonneg (Metric.closedBall x ρ) k f])

/-- `app:lem:elementary-interpolation-jets`: the coefficient map for the ordered
rational operation `A⁻¹ Q` is smooth wherever `A` is invertible. -/
theorem contDiffAt_matrix_inv_mul {p : Matrix ι ι ℝ × Matrix ι ι ℝ}
    (hp : IsUnit p.1) {N : ℕ∞ω} :
    ContDiffAt ℝ N (fun q : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ q.1⁻¹ * q.2) p :=
  ((contDiffAt_matrix_inv hp).comp p contDiffAt_fst).mul contDiffAt_snd

/-- `app:lem:elementary-interpolation-jets`: the ordered rational operation
`A⁻¹ Q` acts tamely on paired matrix fields whose values lie in a fixed compact
range with invertible first component. Compactness supplies both low bounds
and a uniform inverse gap. The bound uses only the input array's derivatives
through `k`, including the no-loss choice `k = r`. -/
theorem exists_cNorm_matrixInvMul_le_tame_closedBall_on_compact
    [FiniteDimensional ℝ E] (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (Matrix ι ι ℝ × Matrix ι ι ℝ)} (ht : IsCompact t)
    (hu : ∀ p ∈ t, IsUnit p.1) {r k : ℕ} (hrk : r ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : E → Matrix ι ι ℝ × Matrix ι ι ℝ,
      ContDiff ℝ ∞ U → MapsTo U (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r
          (matrixInvMul (fun y ↦ (U y).1) (fun y ↦ (U y).2)) ≤
            C * (1 + cNorm (Metric.closedBall x ρ) k U) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    x hρ ht hrk (fun p hp ↦ contDiffAt_matrix_inv_mul (N := r) (hu p hp))
  refine ⟨C, hC, ?_⟩
  intro U hU hUt
  exact hbound U hU hUt

end JanetCartan
