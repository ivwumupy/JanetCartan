module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.Basic
public import JanetCartan.Analysis.Matrix.InverseBounds.Algebra

/-!
# Reserve arithmetic for the near-carrier primitive jets

The consumers are `NearCarrierSymbol.hasFullSourceSymbolBound_of_expression`
and `app:ch_response:eq:direct-envelope-profile`. The reserve is subtracted
in the natural numbers. The product and partition estimates below spend one
total derivative budget. Their constants depend only on finite primitive jet
constants, and are defined before choosing the scale or the functions.

For the paper's notation take `R = Rstar - 2`, with `2 ≤ Rstar`.
These are local analytic deductions; the response geometry must produce the
primitive phase/frame profiles and the zeroth-order inverse gap.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff BigOperators

namespace JanetCartan.ResponseTransfer.GradedPrimitives

/-- Conversion to the exact exponent consumed by the low calculus in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem reserve_exponent {Rstar : ℕ} (hR : 2 ≤ Rstar) (j : ℕ) :
    j - (Rstar - 2) = j + 2 - Rstar := by omega

/-- A finite product spends one derivative budget, including orders below
the reserve (`app:ch_response:eq:direct-envelope-profile`). -/
theorem sum_sub_reserve_le {ι : Type*} (s : Finset ι) (d : ι → ℕ) (R : ℕ) :
    ∑ i ∈ s, (d i - R) ≤ (∑ i ∈ s, d i) - R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    omega

/-- The inverse chain rule retains the primitive reserve, rather than
replacing each factor by its largest derivative order
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem partition_sub_reserve_le {k : ℕ} (p : OrderedFinpartition k) (R : ℕ) :
    ∑ i, (p.partSize i - R) ≤ k - R := by
  simpa only [CompositionBounds.sum_partSize] using
    sum_sub_reserve_le Finset.univ p.partSize R

/-- Finite chain-rule constant for the coefficient compositions in
`app:ch_response:eq:direct-envelope-profile`. -/
def compositionConstant (A B : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ p : OrderedFinpartition k, A p.length * ∏ i, B (p.partSize i)

/-- Nonnegativity of the finite chain-rule constant. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem compositionConstant_nonneg {A B : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (k : ℕ) :
    0 ≤ compositionConstant A B k :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hA _) (Finset.prod_nonneg fun _ _ ↦ hB _)

variable {X E F G : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A fixed smooth operation applied to reserve-graded primitives preserves
their reserve. This is the inversion step of
`app:ch_response:eq:direct-envelope-profile`; only primitive derivatives
through the requested order are used. -/
theorem norm_jet_comp_fixed_outer_le {f : X → E} {g : E → F} {x : X} {N k : ℕ}
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x)) (hk : k ≤ N)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {L : ℝ} (hL : 1 ≤ L) (R : ℕ)
    (hgjet : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A j)
    (hfjet : ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B j * L ^ (j - R)) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ compositionConstant A B k * L ^ (k - R) := by
  apply (CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum hg hf hk).trans
  rw [compositionConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  have hp : (∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f x‖) ≤
      ∏ i, (B (p.partSize i) * L ^ (p.partSize i - R)) :=
    Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      (fun i _ ↦ hfjet _ (p.partSize_pos i) (p.partSize_le i))
  calc
    _ ≤ A p.length * ∏ i, (B (p.partSize i) * L ^ (p.partSize i - R)) :=
      mul_le_mul (hgjet _ p.length_le) hp (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (hA _)
    _ = (A p.length * ∏ i, B (p.partSize i)) * L ^ (∑ i, (p.partSize i - R)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (partition_sub_reserve_le p R))
      (mul_nonneg (hA _) (Finset.prod_nonneg fun _ _ ↦ hB _))

/-- Composition with a fixed carrier or chart preserves the primitive
reserve (`app:ch_response:eq:direct-envelope-profile`). Both physical
positions and the compact parameter can be retained in `X`. -/
theorem norm_jet_comp_fixed_inner_le {f : X → E} {g : E → F} {x : X} {N k : ℕ}
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x)) (hk : k ≤ N)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {L : ℝ} (hL : 1 ≤ L) (R : ℕ)
    (hgjet : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A j * L ^ (j - R))
    (hfjet : ∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ compositionConstant A B k * L ^ (k - R) := by
  apply (CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum hg hf hk).trans
  rw [compositionConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  calc
    _ ≤ (A p.length * L ^ (p.length - R)) * ∏ i, B (p.partSize i) :=
      mul_le_mul (hgjet _ p.length_le)
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun i _ ↦ hfjet _ (p.partSize_pos i) (p.partSize_le i)))
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (mul_nonneg (hA _) (pow_nonneg (zero_le_one.trans hL) _))
    _ = (A p.length * ∏ i, B (p.partSize i)) * L ^ (p.length - R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (Nat.sub_le_sub_right p.length_le R))
      (mul_nonneg (hA _) (Finset.prod_nonneg fun _ _ ↦ hB _))

/-- Finite Leibniz constant for the selected amplitude and signed reverse
coefficient (`app:ch_response:eq:direct-envelope-profile`). -/
def bilinearConstant (T : E →L[ℝ] F →L[ℝ] G) (A B : ℕ → ℝ) (k : ℕ) : ℝ :=
  ‖T‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)

/-- A bilinear product preserves one reserve, with the total order split
between its factors (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_bilinear_le (T : E →L[ℝ] F →L[ℝ] G)
    {f : X → E} {g : X → F} {U : Set X} (hU : IsOpen U) {N k : ℕ}
    (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U) (hk : k ≤ N)
    {x : X} (hx : x ∈ U) (A B : ℕ → ℝ)
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {L : ℝ} (hL : 1 ≤ L) (R : ℕ)
    (hfjet : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * L ^ (j - R))
    (hgjet : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g x‖ ≤ B j * L ^ (j - R)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ T (f y) (g y)) x‖ ≤
      bilinearConstant T A B k * L ^ (k - R) := by
  have h := T.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx
    (n := k) (by exact_mod_cast hk)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  apply h.trans
  rw [bilinearConstant, mul_assoc ‖T‖, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
  calc
    _ ≤ (k.choose i : ℝ) * (A i * L ^ (i - R)) *
        (B (k - i) * L ^ (k - i - R)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfjet i hik) (Nat.cast_nonneg _))
        (hgjet _ (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (hA _) (pow_nonneg (zero_le_one.trans hL) _)))
    _ = ((k.choose i : ℝ) * A i * B (k - i)) * L ^ ((i - R) + (k - i - R)) := by
      rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA _)) (hB _))

/-- The fixed-gap inverse constant for
`app:ch_response:eq:direct-envelope-profile`. No frequency or scale occurs. -/
def inverseConstant (M : ℝ) (B : ℕ → ℝ) (k : ℕ) : ℝ :=
  compositionConstant (fun j ↦ (j.factorial : ℝ) * max 1 M ^ (j + 1)) B k

/-- Inversion of a primitive matrix/operator profile retains the natural
subtraction reserve. Only the value of the inverse is bounded as input;
all positive-order inverse bounds are conclusions. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_inverse_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [HasSummableGeomSeries A] {f : X → A} {x : X} {N k : ℕ}
    (hf : ContDiffAt ℝ N f x) (hk : k ≤ N) (hu : IsUnit (f x))
    {M : ℝ} (hM : ‖Ring.inverse (f x)‖ ≤ M)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) {L : ℝ} (hL : 1 ≤ L) (R : ℕ)
    (hfjet : ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B j * L ^ (j - R)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ Ring.inverse (f y)) x‖ ≤
      inverseConstant M B k * L ^ (k - R) := by
  have hg : ContDiffAt ℝ N (Ring.inverse : A → A) (f x) :=
    contDiffOn_ringInverse_units.contDiffAt (Units.isOpen.mem_nhds hu)
  exact norm_jet_comp_fixed_outer_le hf hg hk _ B
    (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left 1 M)) _)) hB hL R
    (fun j _ ↦ (norm_iteratedFDeriv_ringInverse_le j hu).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hM.trans (le_max_right _ _)) _)
        (Nat.cast_nonneg _))) hfjet

end JanetCartan.ResponseTransfer.GradedPrimitives
