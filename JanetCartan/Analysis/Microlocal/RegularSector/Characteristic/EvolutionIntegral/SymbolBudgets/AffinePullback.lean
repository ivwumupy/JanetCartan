module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Coordinates
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local joint seminorms under the elapsed substitution

The fixed affine substitution in `app:ch_regular_base:eq:fixed-time-representation`
is a contraction. Thus its pullback costs no derivatives and no high power of
any variable symbol seminorm. Smoothness is required only on a buffered open
set containing the original joint variables.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget.Local

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Local affine chain rule bound, used for the two-time primitive jets in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_iteratedFDeriv_preAffine_le (L : E →L[ℝ] F) (b : F)
    {U : Set F} (hU : IsOpen U) {f : F → G} (hf : ContDiffOn ℝ ∞ f U)
    {x : E} (hx : L x + b ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f (L y + b)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (L x + b)‖ * ‖L‖ ^ j := by
  let V := (fun y : F ↦ y + b) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ (fun y ↦ f (y + b)) V :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy ↦ hy)
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hpre.uniqueDiffOn
    (show L x ∈ V from hx) (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hx,
    iteratedFDerivWithin_of_isOpen _ hV hx, iteratedFDeriv_comp_add_right] at he
  change ‖iteratedFDeriv ℝ j ((fun y ↦ f (y + b)) ∘ L) x‖ ≤ _
  rw [he]
  simpa using (iteratedFDeriv ℝ j f (L x + b)).norm_compContinuousLinearMap_le
    (fun _ ↦ L)

/-- A fixed affine contraction preserves the original joint `cNorm` budget.
The elapsed map is the intended consumer in the fixed-time representation. -/
theorem cNorm_preAffine_contraction_le (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (b : F)
    {K : Set E} {J U : Set F} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    {f : F → G} (hf : ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo (fun x ↦ L x + b) K J) (j : ℕ) :
    cNorm K j (fun x ↦ f (L x + b)) ≤ cNorm J j f := by
  apply cNorm_le_sum_of_bounds (fun k _ ↦ sSup_norm_iteratedFDeriv_nonneg J k f)
  intro k hk x hx
  have hpow : ‖L‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hL
  have hb := le_csSup
    (bddAbove_norm_iteratedFDeriv_of_contDiffAt hJ
      (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hJU hy))).of_le (by simp)) hk)
    (mem_image_of_mem (fun y ↦ ‖iteratedFDeriv ℝ k f y‖) (hmap hx))
  exact (norm_iteratedFDeriv_preAffine_le L b hU hf (hJU (hmap hx)) k).trans
    ((mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans (by simpa using hb))

/-- Every elapsed time uses the same original joint seminorm. The only
elapsed-time input is the buffered chart inclusion, supplied by geometry.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cNorm_comp_elapsedPoint_le {d : ℕ} {K : Set (Point (d + 1))}
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    {f : TwoTimePoint d → G} (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hmap : MapsTo (elapsedPoint r) K J) (j : ℕ) :
    cNorm K j (f ∘ elapsedPoint r) ≤ cNorm J j f :=
  cNorm_preAffine_contraction_le elapsedLinear norm_elapsedLinear_le
    (elapsedTranslation r) hJ hU hJU hf hmap j

/-- Local Leibniz bound for the complete masked amplitude. Only jets at the
original point occur on the right; this permits restriction to buffered
symbol charts in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_iteratedFDeriv_smul_on_open_le [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} {g : E → G}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ := by
  have h := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hx (n := k) (by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using h

/-- Local product estimate, linear in each differentiated factor. The masks
are fixed in its use for `app:ch_regular_base:eq:fixed-time-representation`.
Consequently their seminorm contributes only to the constant. -/
theorem cNorm_smul_on_open_le [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → ℂ} {g : E → G} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (j : ℕ) :
    cNorm K j (fun x ↦ f x • g x) ≤
      (j + 1 : ℝ) * 2 ^ j * cNorm K j f * cNorm K j g := by
  have hf' : ∀ x ∈ K, ContDiffAt ℝ j f x := fun x hx ↦ (hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le
    (show (j : ℕ∞ω) ≤ ∞ by simp)
  have hg' : ∀ x ∈ K, ContDiffAt ℝ j g x := fun x hx ↦ (hg.contDiffAt (hU.mem_nhds (hKU hx))).of_le
    (show (j : ℕ∞ω) ≤ ∞ by simp)
  have hb : ∀ k ≤ j, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun y ↦ f y • g y) x‖ ≤
        2 ^ j * cNorm K j f * cNorm K j g := by
    intro k hk x hx
    apply (norm_iteratedFDeriv_smul_on_open_le hU hf hg (hKU hx) k).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * cNorm K j f * cNorm K j g := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf' hx (hi'.trans hk))
            (Nat.cast_nonneg _))
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg' hx ((Nat.sub_le k i).trans hk))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      _ = 2 ^ k * cNorm K j f * cNorm K j g := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        norm_cast
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk)
          (cNorm_nonneg K j f)) (cNorm_nonneg K j g)
  have h := cNorm_le_sum_of_bounds
    (fun k (_ : k ≤ j) ↦ mul_nonneg
      (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j) (cNorm_nonneg K j f))
      (cNorm_nonneg K j g)) hb
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc] using h

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
