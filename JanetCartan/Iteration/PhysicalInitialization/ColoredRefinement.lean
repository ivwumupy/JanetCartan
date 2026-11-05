module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Family
public import JanetCartan.Geometry.IsometricEmbedding.Reference.RadialSeparation
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Color refinement without replacing the protected geometry

For `app:defn:exhaustive-pair-groups` and
`app:rem:exhaustive-signed-pairs`, refine the retained groups by the finite
sampling colors. The old carrier family and protected open angular set remain
fixed. Same-color terms are positive multiples of old signed terms; cross-color
terms are made close to a signed old carrier by finite radial separation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set Metric
namespace JanetCartan.PhysicalInitialization.ColoredRefinement
open SignedPairs

/-- Each original carrier direction already occurs among the signed directions,
as the sum with identical parameters. No single-carrier menu is chosen. -/
theorem carrier_direction_mem {n : ℕ} {I X Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (x : X) (i : I) (z : S i) :
    NormedSpace.normalize (f x i z) ∈ directionSet f S := by
  refine ⟨x, Pair.sum i z z, ?_⟩
  change NormedSpace.normalize (f x i z) =
    NormedSpace.normalize (f x i z + f x i z)
  rw [← two_smul ℝ (f x i z),
    NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Quantitative signed-pair bounds give the individual annulus at half the
pair constants, by applying them to the repeated-parameter sum. -/
theorem carrier_norm_bounds {n : ℕ} {I X Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n) (a A : ℝ)
    (hpair : ∀ x (q : Pair I Z S),
      a * q.beat ≤ ‖q.vector (f x)‖ ∧ ‖q.vector (f x)‖ ≤ A * q.beat)
    (x : X) (i : I) (z : S i) :
    a / 2 ≤ ‖f x i z‖ ∧ ‖f x i z‖ ≤ A / 2 := by
  have h := hpair x (Pair.sum i z z)
  have hnorm : ‖f x i z + f x i z‖ = 2 * ‖f x i z‖ := by
    rw [← two_smul ℝ (f x i z), norm_smul]
    norm_num
  simp only [Pair.vector, Pair.beat, mul_one, hnorm] at h
  constructor <;> linarith [h.1, h.2]

/-- The old signed-direction closure is compact in the actual finite-dimensional
physical covector space, including a possibly empty family. -/
theorem isCompact_signed_direction_closure {n : ℕ} {I X Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (hnz : ∀ x (q : Pair I Z S), q.vector (f x) ≠ 0) :
    IsCompact (closure (directionSet f S)) := by
  apply (isCompact_closedBall (0 : Euclidean n) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  rintro v ⟨x, q, rfl⟩
  simpa only [mem_closedBall, dist_zero_right, NormedSpace.norm_normalize (hnz x q)]
    using (le_refl (1 : ℝ))

/-- Negation preserves the interior of a symmetric protected set. -/
theorem neg_mem_protected_interior {n : ℕ} {Ω : Set (Euclidean n)}
    (hsym : ∀ v ∈ Ω, -v ∈ Ω) {v : Euclidean n} (hv : v ∈ interior Ω) :
    -v ∈ interior Ω := by
  have hpre : (fun w : Euclidean n ↦ -w) ⁻¹' Ω = Ω := by
    ext w
    constructor
    · intro hw
      simpa only [neg_neg] using hsym (-w) hw
    · exact hsym w
  rw [mem_interior_iff_mem_nhds] at hv ⊢
  have ht : Filter.Tendsto (fun w : Euclidean n ↦ -w)
      (nhds (-v)) (nhds v) := by
    simpa only [neg_neg] using (continuous_neg.tendsto (-v))
  have hmem := Filter.mem_map.mp (ht hv)
  simpa only [hpre] using hmem

/-- Keep the existing protected set. Compactness and its symmetry supply a
positive CLOSED tube around all signed old carrier directions. -/
theorem exists_protected_direction_tube {n : ℕ} {I X Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (hnz : ∀ x (q : Pair I Z S), q.vector (f x) ≠ 0)
    (Ω : Set (Euclidean n)) (hsym : ∀ v ∈ Ω, -v ∈ Ω)
    (hprotect : closure (directionSet f S) ⊆ interior Ω) :
    ∃ ε : ℝ, 0 < ε ∧
      cthickening ε (closure (directionSet f S) ∪
        (fun v : Euclidean n ↦ -v) '' closure (directionSet f S)) ⊆ interior Ω := by
  have hcompact := isCompact_signed_direction_closure S f hnz
  apply (hcompact.union (hcompact.image continuous_neg)).exists_cthickening_subset_open
    isOpen_interior
  rintro v (hv | ⟨w, hw, rfl⟩)
  · exact hprotect hv
  · exact neg_mem_protected_interior hsym (hprotect hw)

/-- Finite color multipliers can retain the OLD radial labels, make every
product label distinct, and satisfy any requested color separation. This is
not a new protected-family or initializer selection. -/
theorem exists_refining_scales (I C : Type*) [Finite I] [Finite C]
    (R : I → ℝ) (hR : ∀ i, 1 ≤ R i) (hinj : Function.Injective R) (K : ℝ) :
    ∃ k : C → ℝ, (∀ c, 1 ≤ k c) ∧ Function.Injective k ∧
      (∀ ic : I × C, 1 ≤ k ic.2 * R ic.1) ∧
      Function.Injective (fun ic : I × C ↦ k ic.2 * R ic.1) ∧
      ∀ c d, k c < k d → K * k c ≤ k d := by
  classical
  let := Fintype.ofFinite I
  let M : ℝ := 1 + ∑ i : I, R i
  have hRM (i : I) : R i ≤ M := by
    have hsum : R i ≤ ∑ j : I, R j := Finset.single_le_sum
      (fun j _ ↦ le_trans zero_le_one (hR j)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  obtain ⟨k, hk, hkinj, hsep⟩ := exists_radial_labels C (max K (M+1))
  have hkpos (c : C) : 0 < k c := lt_of_lt_of_le zero_lt_one (hk c)
  have hprod_lt (c d : C) (hcd : k c < k d) (i j : I) :
      k c * R i < k d * R j := by
    calc
      k c * R i ≤ k c * M := mul_le_mul_of_nonneg_left (hRM i) (hkpos c).le
      _ < k c * (M+1) := mul_lt_mul_of_pos_left (by linarith) (hkpos c)
      _ ≤ k c * max K (M+1) := mul_le_mul_of_nonneg_left (le_max_right _ _) (hkpos c).le
      _ = max K (M+1) * k c := mul_comm _ _
      _ ≤ k d := hsep c d hcd
      _ ≤ k d * R j := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hR j) (hkpos d).le
  refine ⟨k, hk, hkinj, ?_, ?_, ?_⟩
  · intro ic
    simpa only [one_mul] using mul_le_mul (hk ic.2) (hR ic.1)
      zero_le_one (hkpos ic.2).le
  · rintro ⟨i,c⟩ ⟨j,d⟩ heq
    change k c * R i = k d * R j at heq
    by_cases hcd : c = d
    · subst d
      have hij : i = j := hinj (mul_left_cancel₀ (hkpos c).ne' heq)
      exact Prod.ext hij rfl
    · have hne : k c ≠ k d := fun h ↦ hcd (hkinj h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact False.elim ((ne_of_lt (hprod_lt c d hlt i j)) heq)
      · exact False.elim ((ne_of_lt (hprod_lt d c hgt j i)) heq.symm)
  · intro c d hcd
    exact (mul_le_mul_of_nonneg_right (le_max_left K (M+1)) (hkpos c).le).trans
      (hsep c d hcd)

/-- Embed an old signed pair in one color, retaining the entire original
parameter pair, its signs and its nonzero-difference condition. -/
def liftPair {I C Z : Type*} {S : I → Set Z} (c : C) :
    Pair I Z S → Pair (I × C) Z (fun ic ↦ S ic.1)
  | .difference i z w hne => .difference (i,c) z w hne
  | .sum i z w => .sum (i,c) z w
  | .cross i j hne z w s t hs ht =>
    .cross (i,c) (j,c) (fun h ↦ hne (congrArg Prod.fst h)) z w s t hs ht

/-- The true beat is unchanged within a color, including arbitrarily short
nonzero differences. -/
theorem liftPair_beat {I C Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S : I → Set Z} (c : C) (q : Pair I Z S) :
    (liftPair c q).beat = q.beat := by
  cases q <;> rfl

/-- A same-color vector is exactly a positive scalar multiple of the OLD
vector; no carrier chart or original radial label is replaced. -/
theorem liftPair_vector {n : ℕ} {I C Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {S : I → Set Z}
    (k : C → ℝ) (f : I → Z → Euclidean n) (c : C) (q : Pair I Z S) :
    (liftPair c q).vector (fun ic z ↦ k ic.2 • f ic.1 z) = k c • q.vector f := by
  cases q <;> simp [liftPair, Pair.vector, smul_add, smul_sub, smul_smul, mul_comm]

/-- The normalized same-color direction is literally its old direction. -/
theorem liftPair_direction {n : ℕ} {I C Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {S : I → Set Z}
    (k : C → ℝ) (f : I → Z → Euclidean n) (c : C) (hk : 0 < k c)
    (q : Pair I Z S) :
    NormedSpace.normalize ((liftPair c q).vector (fun ic z ↦ k ic.2 • f ic.1 z)) =
      NormedSpace.normalize (q.vector f) := by
  rw [liftPair_vector, NormedSpace.normalize_smul_of_pos hk]

/-- The native dominant-radius estimate, with its numeric separation obtained
from the retained color ratio and with zero carrier perturbations. -/
theorem separated_color_pair_estimates {E C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : C → ℝ) (hk : ∀ c, 1 ≤ k c) {a b η K : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hη : 0 < η) (hηq : η ≤ 1/4)
    (hK : (b+a)/(η*a) ≤ K) {c d : C}
    (hcd : k c < k d) (hsep : K*k c ≤ k d)
    (x y : E) (hx : ‖x‖ ≤ b) (hy : a ≤ ‖y‖) (hyb : ‖y‖ ≤ b)
    (s t : ℝ) (hs : |s| = 1) (ht : |t| = 1) :
    a/2*k d ≤ ‖s • (k c • x) + t • (k d • y)‖ ∧
      ‖s • (k c • x) + t • (k d • y)‖ ≤ 2*(b+a)*k d ∧
      ‖NormedSpace.normalize (s • (k c • x) + t • (k d • y)) -
        NormedSpace.normalize (t • y)‖ ≤ 4*η := by
  have hc : 0 < k c := lt_of_lt_of_le zero_lt_one (hk c)
  have hd : 0 < k d := lt_of_lt_of_le zero_lt_one (hk d)
  have hcoef : b+a ≤ K*(η*a) := (div_le_iff₀ (mul_pos hη ha)).mp hK
  have hdom : k c * (b+a) ≤ η*a*k d := by
    calc
      k c*(b+a) ≤ k c*(K*(η*a)) := mul_le_mul_of_nonneg_left hcoef hc.le
      _ = (η*a)*(K*k c) := by ring
      _ ≤ (η*a)*k d := mul_le_mul_of_nonneg_left hsep (mul_pos hη ha).le
  exact radial_pair_estimates ha hb hη hηq hc.le hd hcd.le hdom hx hy hyb
    (by simpa only [sub_self, norm_zero] using (mul_pos hη ha).le)
    (by simpa only [sub_self, norm_zero] using (mul_pos hη ha).le) hs ht

/-- Both signs of an old carrier belong to the fixed symmetric closure used by
the tube argument. The positive direction comes from the old doubled sum. -/
theorem signed_carrier_direction_mem {n : ℕ} {I X Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (x : X) (i : I) (z : S i) (s : ℝ) (hs : |s| = 1) :
    NormedSpace.normalize (s • f x i z) ∈
      closure (directionSet f S) ∪
        (fun v : Euclidean n ↦ -v) '' closure (directionSet f S) := by
  have hmem := subset_closure (carrier_direction_mem S f x i z)
  by_cases hsn : 0 ≤ s
  · have hp : s = 1 := by simpa only [abs_of_nonneg hsn] using hs
    subst s
    simpa only [one_smul, Set.mem_union] using Or.inl (b :=
      NormedSpace.normalize (f x i z) ∈
        (fun v : Euclidean n ↦ -v) '' closure (directionSet f S)) hmem
  · have hm : s = -1 := by
      rw [abs_of_neg (lt_of_not_ge hsn)] at hs
      linarith
    subst s
    simp only [neg_one_smul, NormedSpace.normalize_neg]
    exact Or.inr ⟨NormedSpace.normalize (f x i z), hmem, rfl⟩

/-- Refine the groups by finite colors WITHOUT replacing the protected set or
old carrier family. The full result retains the chosen ratio certificate so
quantitative projected/norm bounds can be derived for THIS SAME color map.
All choices precede the arbitrary family index `x`; in the actual application
that index contains the complete permitted immersion and physical point. -/
theorem exists_refined_angular_packet {n : ℕ} {I C X Z : Type*}
    [Finite I] [Finite C] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (R : I → ℝ) (hR : ∀ i, 1 ≤ R i) (hRinj : Function.Injective R)
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A)
    (hpair : ∀ x (q : Pair I Z S),
      a*q.beat ≤ ‖q.vector (f x)‖ ∧ ‖q.vector (f x)‖ ≤ A*q.beat)
    (Ω : Set (Euclidean n)) (hsym : ∀ v ∈ Ω, -v ∈ Ω)
    (hprotect : closure (directionSet f S) ⊆ interior Ω) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ ∃ k : C → ℝ,
      (∀ c, 1 ≤ k c) ∧ Function.Injective k ∧
      (∀ ic : I × C, 1 ≤ k ic.2 * R ic.1) ∧
      Function.Injective (fun ic : I × C ↦ k ic.2 * R ic.1) ∧
      (∀ c d, k c < k d → ((A/2+a/2)/(η*(a/2)))*k c ≤ k d) ∧
      closure (directionSet (fun x (ic : I × C) z ↦ k ic.2 • f x ic.1 z)
        (fun ic ↦ S ic.1)) ⊆ interior Ω := by
  have hnz (x : X) (q : Pair I Z S) : q.vector (f x) ≠ 0 :=
    norm_pos_iff.mp ((mul_pos ha q.beat_pos).trans_le (hpair x q).1)
  obtain ⟨ε, hε, htube⟩ := exists_protected_direction_tube S f hnz Ω hsym hprotect
  let η : ℝ := min (1/4) (ε/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηq : η ≤ 1/4 := min_le_left _ _
  have hηε : 4*η ≤ ε := by
    have h := min_le_right (1/4 : ℝ) (ε/4)
    change η ≤ ε/4 at h
    linarith
  let K : ℝ := (A/2+a/2)/(η*(a/2))
  obtain ⟨k, hk, hki, hRp, hRpi, hsep⟩ := exists_refining_scales I C R hR hRinj K
  have hkpos (c : C) : 0 < k c := lt_of_lt_of_le zero_lt_one (hk c)
  let B : Set (Euclidean n) := closure (directionSet f S) ∪
    (fun v : Euclidean n ↦ -v) '' closure (directionSet f S)
  change cthickening ε B ⊆ interior Ω at htube
  have hold (x : X) (q : Pair I Z S) (c : C) :
      NormedSpace.normalize (k c • q.vector (f x)) ∈ cthickening ε B := by
    rw [NormedSpace.normalize_smul_of_pos (hkpos c)]
    have hm : NormedSpace.normalize (q.vector (f x)) ∈ B :=
      Or.inl (subset_closure ⟨x, q, rfl⟩)
    exact mem_cthickening_of_dist_le _ _ ε B hm (by simpa only [dist_self] using hε.le)
  refine ⟨η, hη, hηq, k, hk, hki, hRp, hRpi, hsep, ?_⟩
  apply (closure_minimal ?_ isClosed_cthickening).trans htube
  rintro v ⟨x, q, rfl⟩
  cases q with
  | difference g z w hne =>
    simpa only [Pair.vector, smul_sub] using hold x (Pair.difference g.1 z w hne) g.2
  | sum g z w =>
    simpa only [Pair.vector, smul_add] using hold x (Pair.sum g.1 z w) g.2
  | cross g h hne z w s t hs ht =>
    by_cases hc : g.2 = h.2
    · have hij : g.1 ≠ h.1 := fun he ↦ hne (Prod.ext he hc)
      simpa only [Pair.vector, smul_add, smul_smul, hc, mul_comm] using
        hold x (Pair.cross g.1 h.1 hij z w s t hs ht) g.2
    · have hkn : k g.2 ≠ k h.2 := fun he ↦ hc (hki he)
      have hx := carrier_norm_bounds S f a A hpair x g.1 z
      have hy := carrier_norm_bounds S f a A hpair x h.1 w
      rcases lt_or_gt_of_ne hkn with hlt | hgt
      · have hh := separated_color_pair_estimates k hk (half_pos ha) (half_pos hA).le
          hη hηq (le_refl K) hlt (hsep _ _ hlt)
          (f x g.1 z) (f x h.1 w) hx.2 hy.1 hy.2 s t hs ht
        have hm : NormedSpace.normalize (t • f x h.1 w) ∈ B :=
          signed_carrier_direction_mem S f x h.1 w t ht
        apply mem_cthickening_of_dist_le _ _ ε B hm
        rw [dist_eq_norm]
        exact hh.2.2.trans hηε
      · have hh := separated_color_pair_estimates k hk (half_pos ha) (half_pos hA).le
          hη hηq (le_refl K) hgt (hsep _ _ hgt)
          (f x h.1 w) (f x g.1 z) hy.2 hx.1 hx.2 t s ht hs
        have hm : NormedSpace.normalize (s • f x g.1 z) ∈ B :=
          signed_carrier_direction_mem S f x g.1 z s hs
        apply mem_cthickening_of_dist_le _ _ ε B hm
        rw [dist_eq_norm]
        simpa only [Pair.vector, add_comm] using hh.2.2.trans hηε

end JanetCartan.PhysicalInitialization.ColoredRefinement
end
