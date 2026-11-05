module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import Mathlib.Topology.Order.Compact

/-!
# Basic estimates for the derivative seminorm

These are the direct norm bounds used in Appendix B, especially
`app:lem:elementary-interpolation-jets`. The seminorm is the sum of derivative
suprema defined in `Norm`, with the ambient (not within-set) iterated derivatives.
Compactness and smoothness near the set ensure that these suprema bound the
derivatives. No interpolation theorem is used.

The variants with pointwise `ContDiffAt` hypotheses apply to functions smooth on
an open neighborhood of the compact set. Global `ContDiff` variants are also
provided. No finite-dimensionality or nonemptiness assumption is needed.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s t : Set E} {r k j : ℕ} {f g : E → F}

/-- `app:sec:elementary-interpolation`: each derivative supremum is nonnegative, including on the
empty set. -/
theorem sSup_norm_iteratedFDeriv_nonneg (s : Set E) (j : ℕ) (f : E → F) :
    0 ≤ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s) :=
  Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg _)

/-- `app:sec:elementary-interpolation`: the derivative seminorm is nonnegative. -/
theorem cNorm_nonneg (s : Set E) (r : ℕ) (f : E → F) : 0 ≤ cNorm s r f :=
  Finset.sum_nonneg fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg s j f

/-- `app:sec:elementary-interpolation`: the derivative seminorm on the empty set vanishes. -/
@[simp] theorem cNorm_empty (r : ℕ) (f : E → F) : cNorm ∅ r f = 0 := by
  simp [cNorm, Real.sSup_empty]

/-- `app:sec:elementary-interpolation`: the zero function has zero derivative seminorm. -/
@[simp] theorem cNorm_zero (s : Set E) (r : ℕ) : cNorm s r (0 : E → F) = 0 := by
  apply le_antisymm _ (cNorm_nonneg s r 0)
  apply Finset.sum_nonpos
  intro j _
  apply Real.sSup_le _ le_rfl
  rintro _ ⟨x, _, rfl⟩
  simp [iteratedFDeriv_zero]

/-- `app:sec:elementary-interpolation`: order zero is the supremum of the function's norm. -/
theorem cNorm_order_zero (s : Set E) (f : E → F) :
    cNorm s 0 f = sSup ((fun x ↦ ‖f x‖) '' s) := by
  simp [cNorm, norm_iteratedFDeriv_zero]

/-- `app:sec:elementary-interpolation`: adjoining one derivative adds its supremum. -/
theorem cNorm_succ (s : Set E) (r : ℕ) (f : E → F) :
    cNorm s (r + 1) f = cNorm s r f +
      sSup ((fun x ↦ ‖iteratedFDeriv ℝ (r + 1) f x‖) '' s) := by
  exact Finset.sum_range_succ _ _

/-- `app:lem:elementary-interpolation-jets`: the direct bound between derivative orders. -/
theorem cNorm_mono_order (hrk : r ≤ k) : cNorm s r f ≤ cNorm s k f := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hrk 1))
    (fun j _ _ ↦ sSup_norm_iteratedFDeriv_nonneg s j f)

/-- `app:sec:elementary-interpolation`: continuity of each derivative norm under local finite-order
smoothness. -/
theorem continuousOn_norm_iteratedFDeriv_of_contDiffAt
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x) (hj : j ≤ r) :
    ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) s := by
  intro x hx
  exact ((hf x hx).continuousAt_iteratedFDeriv (by exact_mod_cast hj)).norm.continuousWithinAt

/-- `app:sec:elementary-interpolation`: compactness makes the image of each derivative norm bounded
above. -/
theorem bddAbove_norm_iteratedFDeriv_of_contDiffAt (hs : IsCompact s)
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x) (hj : j ≤ r) :
    BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s) :=
  hs.bddAbove_image (continuousOn_norm_iteratedFDeriv_of_contDiffAt hf hj)

/-- `app:sec:elementary-interpolation`: globally `C^r` functions have bounded derivatives on compact
sets. -/
theorem bddAbove_norm_iteratedFDeriv (hs : IsCompact s) (hf : ContDiff ℝ r f)
    (hj : j ≤ r) : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s) :=
  bddAbove_norm_iteratedFDeriv_of_contDiffAt hs (fun _ _ ↦ hf.contDiffAt) hj

/-- `app:sec:elementary-interpolation`: a bounded derivative is controlled pointwise by the
derivative seminorm. -/
theorem norm_iteratedFDeriv_le_cNorm_of_bddAbove
    (hb : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s))
    {x : E} (hx : x ∈ s) (hj : j ≤ r) : ‖iteratedFDeriv ℝ j f x‖ ≤ cNorm s r f := by
  exact (le_csSup hb (Set.mem_image_of_mem _ hx)).trans
    (Finset.single_le_sum (fun i _ ↦ sSup_norm_iteratedFDeriv_nonneg s i f)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

/-- `app:sec:elementary-interpolation`: compact-set seminorms control every derivative through their
order. -/
theorem norm_iteratedFDeriv_le_cNorm_of_contDiffAt (hs : IsCompact s)
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x) {x : E} (hx : x ∈ s) (hj : j ≤ r) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ cNorm s r f :=
  norm_iteratedFDeriv_le_cNorm_of_bddAbove
    (bddAbove_norm_iteratedFDeriv_of_contDiffAt hs hf hj) hx hj

/-- `app:sec:elementary-interpolation`: the pointwise derivative bound for globally `C^r` functions.
-/
theorem norm_iteratedFDeriv_le_cNorm (hs : IsCompact s) (hf : ContDiff ℝ r f)
    {x : E} (hx : x ∈ s) (hj : j ≤ r) : ‖iteratedFDeriv ℝ j f x‖ ≤ cNorm s r f :=
  norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs (fun _ _ ↦ hf.contDiffAt) hx hj

/-- `app:sec:elementary-interpolation`: the seminorm controls the function itself. -/
theorem norm_le_cNorm (hs : IsCompact s) (hf : ContDiff ℝ r f)
    {x : E} (hx : x ∈ s) : ‖f x‖ ≤ cNorm s r f := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_cNorm hs hf hx (Nat.zero_le r)

/-- `app:sec:elementary-interpolation`: all derivatives through a fixed order have a common finite
bound. -/
theorem exists_bound_norm_iteratedFDeriv (hs : IsCompact s) (hf : ContDiff ℝ r f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ C :=
  ⟨cNorm s r f, cNorm_nonneg s r f,
    fun _ hj _ hx ↦ norm_iteratedFDeriv_le_cNorm hs hf hx hj⟩

/-- `app:sec:elementary-interpolation`: pointwise bounds for the derivatives give a bound for the
seminorm. -/
theorem cNorm_le_sum_of_bounds {C : ℕ → ℝ}
    (hC : ∀ j ≤ r, 0 ≤ C j)
    (hf : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ C j) :
    cNorm s r f ≤ ∑ j ∈ Finset.range (r + 1), C j := by
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact Real.sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hf j hjr x hx) (hC j hjr)

/-- `app:sec:elementary-interpolation`: restricting the set decreases the seminorm when the larger
images are bounded. -/
theorem cNorm_mono_set_of_bddAbove (hst : s ⊆ t)
    (hb : ∀ j ≤ r, BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' t)) :
    cNorm s r f ≤ cNorm t r f := by
  apply cNorm_le_sum_of_bounds (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg t j f)
  intro j hj x hx
  exact le_csSup (hb j hj) (Set.mem_image_of_mem _ (hst hx))

/-- `app:sec:elementary-interpolation`: restriction to any subset of a compact set decreases the
seminorm. -/
theorem cNorm_mono_set_of_contDiffAt (hst : s ⊆ t) (ht : IsCompact t)
    (hf : ∀ x ∈ t, ContDiffAt ℝ r f x) : cNorm s r f ≤ cNorm t r f :=
  cNorm_mono_set_of_bddAbove hst
    (fun _ hj ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt ht hf hj)

/-- `app:sec:elementary-interpolation`: set monotonicity for globally `C^r` functions. -/
theorem cNorm_mono_set (hst : s ⊆ t) (ht : IsCompact t) (hf : ContDiff ℝ r f) :
    cNorm s r f ≤ cNorm t r f :=
  cNorm_mono_set_of_contDiffAt hst ht (fun _ _ ↦ hf.contDiffAt)

/-- `app:sec:elementary-interpolation`: triangle inequality under smoothness near the compact set.
-/
theorem cNorm_add_le_of_contDiffAt (hs : IsCompact s)
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x) (hg : ∀ x ∈ s, ContDiffAt ℝ r g x) :
    cNorm s r (f + g) ≤ cNorm s r f + cNorm s r g := by
  simp only [cNorm, ← Finset.sum_add_distrib]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ add_nonneg (sSup_norm_iteratedFDeriv_nonneg s j f)
      (sSup_norm_iteratedFDeriv_nonneg s j g))
  intro j hj x hx
  rw [iteratedFDeriv_add_apply ((hf x hx).of_le (by exact_mod_cast hj))
    ((hg x hx).of_le (by exact_mod_cast hj))]
  exact (norm_add_le _ _).trans (add_le_add
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hs hf hj)
      (Set.mem_image_of_mem _ hx))
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hs hg hj)
      (Set.mem_image_of_mem _ hx)))

/-- `app:sec:elementary-interpolation`: triangle inequality for globally `C^r` functions. -/
theorem cNorm_add_le (hs : IsCompact s) (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (f + g) ≤ cNorm s r f + cNorm s r g :=
  cNorm_add_le_of_contDiffAt hs (fun _ _ ↦ hf.contDiffAt) (fun _ _ ↦ hg.contDiffAt)

/-- `app:sec:elementary-interpolation`: negating a function preserves its derivative seminorm. -/
@[simp] theorem cNorm_neg (s : Set E) (r : ℕ) (f : E → F) :
    cNorm s r (-f) = cNorm s r f := by
  simp only [cNorm, iteratedFDeriv_neg_apply, norm_neg]

/-- `app:sec:elementary-interpolation`: the difference estimate on a compact set. -/
theorem cNorm_sub_le (hs : IsCompact s) (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (f - g) ≤ cNorm s r f + cNorm s r g := by
  have hneg : ContDiff ℝ r (-g) := hg.neg
  simpa only [sub_eq_add_neg, cNorm_neg] using cNorm_add_le hs hf hneg

/-- `app:sec:elementary-interpolation`: real scalar homogeneity, assuming smoothness near the set.
-/
theorem cNorm_smul_of_contDiffAt (a : ℝ)
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x) :
    cNorm s r (a • f) = ‖a‖ * cNorm s r f := by
  unfold cNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have himage : (fun x ↦ ‖iteratedFDeriv ℝ j (a • f) x‖) '' s =
      (fun b : ℝ ↦ ‖a‖ • b) '' ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro x hx
    simp only [iteratedFDeriv_const_smul_apply ((hf x hx).of_le (by exact_mod_cast hjr)),
      norm_smul, smul_eq_mul]
  rw [himage, Set.image_smul, Real.sSup_smul_of_nonneg (norm_nonneg a), smul_eq_mul]

/-- `app:sec:elementary-interpolation`: real scalar homogeneity for globally `C^r` functions. -/
theorem cNorm_smul (a : ℝ) (hf : ContDiff ℝ r f) :
    cNorm s r (a • f) = ‖a‖ * cNorm s r f :=
  cNorm_smul_of_contDiffAt a (fun _ _ ↦ hf.contDiffAt)

/-- `app:sec:elementary-interpolation`: finite sums satisfy the triangle bound under local
smoothness. -/
theorem cNorm_sum_le_of_contDiffAt {ι : Type*} (u : Finset ι) {f : ι → E → F}
    (hs : IsCompact s) (hf : ∀ i ∈ u, ∀ x ∈ s, ContDiffAt ℝ r (f i) x) :
    cNorm s r (fun x ↦ ∑ i ∈ u, f i x) ≤ ∑ i ∈ u, cNorm s r (f i) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_of_eq (cNorm_zero s r)
  | @insert i u hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    simp only [Finset.sum_insert hi]
    exact (cNorm_add_le_of_contDiffAt hs hf.1
      (fun x hx ↦ ContDiffAt.sum (fun i hi ↦ hf.2 i hi x hx))).trans
      (add_le_add le_rfl (ih hf.2))

/-- `app:sec:elementary-interpolation`: finite sums of globally `C^r` functions satisfy the triangle
bound. -/
theorem cNorm_sum_le {ι : Type*} (u : Finset ι) {f : ι → E → F}
    (hs : IsCompact s) (hf : ∀ i ∈ u, ContDiff ℝ r (f i)) :
    cNorm s r (fun x ↦ ∑ i ∈ u, f i x) ≤ ∑ i ∈ u, cNorm s r (f i) :=
  cNorm_sum_le_of_contDiffAt u hs (fun i hi _ _ ↦ (hf i hi).contDiffAt)

/-- `app:sec:elementary-interpolation`: the seminorm of a finite real linear combination. -/
theorem cNorm_sum_smul_le {ι : Type*} (u : Finset ι) (a : ι → ℝ) {f : ι → E → F}
    (hs : IsCompact s) (hf : ∀ i ∈ u, ContDiff ℝ r (f i)) :
    cNorm s r (fun x ↦ ∑ i ∈ u, a i • f i x) ≤
      ∑ i ∈ u, ‖a i‖ * cNorm s r (f i) := by
  calc
    _ ≤ ∑ i ∈ u, cNorm s r (a i • f i) :=
      cNorm_sum_le u hs (fun i hi ↦ (hf i hi).const_smul (a i))
    _ = _ := Finset.sum_congr rfl (fun i hi ↦ cNorm_smul (a i) (hf i hi))

/-- `app:sec:elementary-interpolation`: the reverse triangle inequality for the derivative seminorm.
-/
theorem abs_cNorm_sub_le (hs : IsCompact s) (hf : ContDiff ℝ r f)
    (hg : ContDiff ℝ r g) : |cNorm s r f - cNorm s r g| ≤ cNorm s r (f - g) := by
  have hfg := cNorm_add_le hs (show ContDiff ℝ r (f - g) from hf.sub hg) hg
  have hgf := cNorm_add_le hs (show ContDiff ℝ r (g - f) from hg.sub hf) hf
  have hsymm : cNorm s r (g - f) = cNorm s r (f - g) := by
    rw [← neg_sub f g, cNorm_neg]
  simp only [sub_add_cancel] at hfg hgf
  rw [hsymm] at hgf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `app:sec:elementary-interpolation`: continuity of the seminorm in a parameter follows from joint
continuity of its derivatives on the parameter space times the ambient coordinate space. -/
theorem continuous_cNorm {P : Type*} [TopologicalSpace P] {f : P → E → F}
    (hs : IsCompact s)
    (hf : ∀ j ≤ r, Continuous (fun p : P × E ↦ iteratedFDeriv ℝ j (f p.1) p.2)) :
    Continuous (fun p ↦ cNorm s r (f p)) := by
  apply continuous_finsetSum
  intro j hj
  exact hs.continuous_sSup (hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).norm

/-- `app:sec:elementary-interpolation`: a jointly continuous family of derivatives has uniformly
bounded seminorms when both the parameter set and the coordinate set are compact. -/
theorem bddAbove_cNorm_of_continuous_iteratedFDeriv
    {P : Type*} [TopologicalSpace P] {K : Set P} {f : P → E → F}
    (hK : IsCompact K) (hs : IsCompact s)
    (hf : ∀ j ≤ r, Continuous (fun p : P × E ↦ iteratedFDeriv ℝ j (f p.1) p.2)) :
    BddAbove ((fun p ↦ cNorm s r (f p)) '' K) :=
  hK.bddAbove_image (continuous_cNorm hs hf).continuousOn

/-- `app:sec:elementary-interpolation`: finite linear combinations of fixed `C^r` functions have
continuously varying seminorms when their real coefficients vary continuously. -/
theorem continuous_cNorm_sum_smul {P ι : Type*} [TopologicalSpace P]
    (u : Finset ι) {a : P → ι → ℝ} {f : ι → E → F}
    (hs : IsCompact s) (ha : ∀ i ∈ u, Continuous (fun p ↦ a p i))
    (hf : ∀ i ∈ u, ContDiff ℝ r (f i)) :
    Continuous (fun p ↦ cNorm s r (fun x ↦ ∑ i ∈ u, a p i • f i x)) := by
  apply continuous_cNorm hs
  intro j hj
  have heq : (fun p : P × E ↦
      iteratedFDeriv ℝ j (fun x ↦ ∑ i ∈ u, a p.1 i • f i x) p.2) =
      (fun p : P × E ↦ ∑ i ∈ u, a p.1 i • iteratedFDeriv ℝ j (f i) p.2) := by
    funext p
    rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦
      ((hf i hi).of_le (by exact_mod_cast hj)).contDiffAt.const_smul (a p.1 i))]
    apply Finset.sum_congr rfl
    intro i hi
    exact iteratedFDeriv_const_smul_apply'
      ((hf i hi).of_le (by exact_mod_cast hj)).contDiffAt
  rw [heq]
  apply continuous_finsetSum
  intro i hi
  exact ((ha i hi).comp continuous_fst).smul
    (((hf i hi).continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd)

end JanetCartan
