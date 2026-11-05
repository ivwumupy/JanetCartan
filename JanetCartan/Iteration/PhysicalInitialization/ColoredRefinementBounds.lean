module

public import JanetCartan.Iteration.PhysicalInitialization.ColoredRefinement

/-!
# Quantitative bounds for the retained colored signed family

This supplies the true-beat/projected bounds needed by
`app:defn:exhaustive-pair-groups` and `app:rem:exhaustive-signed-pairs`.
The color map is the SAME map selected by `exists_refined_angular_packet`.
No geometry, phase or radial labels are selected here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set Metric
namespace JanetCartan.PhysicalInitialization.ColoredRefinement
open SignedPairs

/-- A fixed finite color constant, chosen before all histories/family indices. -/
def colorTotal {C : Type*} [Fintype C] (k : C → ℝ) : ℝ := 1 + ∑ c, k c

theorem colorTotal_pos {C : Type*} [Fintype C] (k : C → ℝ) (hk : ∀ c, 1 ≤ k c) :
    0 < colorTotal k := by
  have hsum : 0 ≤ ∑ c, k c := Finset.sum_nonneg (fun c _ ↦ le_trans zero_le_one (hk c))
  dsimp [colorTotal]
  linarith

theorem color_le_total {C : Type*} [Fintype C] (k : C → ℝ) (hk : ∀ c, 1 ≤ k c)
    (c : C) : k c ≤ colorTotal k := by
  classical
  have hsum : k c ≤ ∑ d, k d := Finset.single_le_sum
    (fun d _ ↦ le_trans zero_le_one (hk d)) (Finset.mem_univ c)
  dsimp [colorTotal]
  linarith

/-- The true-beat bounds for every colored pair. The old difference/sum/cross
pair is retained in the same-color case. The dominant-radius native estimate
handles different colors, including two colors of the SAME old group. -/
theorem refined_pair_norm_bounds {n : ℕ} {I C X Z : Type*} [Fintype C]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A)
    (hpair : ∀ x (q : Pair I Z S),
      a*q.beat ≤ ‖q.vector (f x)‖ ∧ ‖q.vector (f x)‖ ≤ A*q.beat)
    (k : C → ℝ) (hk : ∀ c, 1 ≤ k c) (hki : Function.Injective k)
    (η : ℝ) (hη : 0 < η) (hηq : η ≤ 1/4)
    (hsep : ∀ c d, k c < k d → ((A/2+a/2)/(η*(a/2)))*k c ≤ k d)
    (x : X) (q : Pair (I × C) Z (fun ic ↦ S ic.1)) :
    (a/4)*q.beat ≤ ‖q.vector (fun ic z ↦ k ic.2 • f x ic.1 z)‖ ∧
      ‖q.vector (fun ic z ↦ k ic.2 • f x ic.1 z)‖ ≤
        ((2*A+a)*colorTotal k)*q.beat := by
  have hkpos (c : C) : 0 < k c := lt_of_lt_of_le zero_lt_one (hk c)
  have hAtotal (c : C) : A*k c ≤ (2*A+a)*colorTotal k := by
    calc
      A*k c ≤ (2*A+a)*k c := mul_le_mul_of_nonneg_right (by linarith) (hkpos c).le
      _ ≤ (2*A+a)*colorTotal k := mul_le_mul_of_nonneg_left
        (color_le_total k hk c) (by positivity)
  have hold (q₀ : Pair I Z S) (c : C) :
      (a/4)*q₀.beat ≤ ‖k c • q₀.vector (f x)‖ ∧
        ‖k c • q₀.vector (f x)‖ ≤ ((2*A+a)*colorTotal k)*q₀.beat := by
    rw [norm_smul, Real.norm_of_nonneg (hkpos c).le]
    constructor
    · calc
        (a/4)*q₀.beat ≤ a*q₀.beat := mul_le_mul_of_nonneg_right
          (by linarith) q₀.beat_pos.le
        _ ≤ ‖q₀.vector (f x)‖ := (hpair x q₀).1
        _ ≤ k c*‖q₀.vector (f x)‖ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hk c) (norm_nonneg _)
    · calc
        k c*‖q₀.vector (f x)‖ ≤ k c*(A*q₀.beat) :=
          mul_le_mul_of_nonneg_left (hpair x q₀).2 (hkpos c).le
        _ = (A*k c)*q₀.beat := by ring
        _ ≤ ((2*A+a)*colorTotal k)*q₀.beat :=
          mul_le_mul_of_nonneg_right (hAtotal c) q₀.beat_pos.le
  have hcross (c d : C) (hcd : k c < k d) (v w : Euclidean n)
      (hv : ‖v‖ ≤ A/2) (hw : a/2 ≤ ‖w‖) (hwb : ‖w‖ ≤ A/2)
      (s t : ℝ) (hs : |s| = 1) (ht : |t| = 1) :
      a/4 ≤ ‖s • (k c • v) + t • (k d • w)‖ ∧
        ‖s • (k c • v) + t • (k d • w)‖ ≤ (2*A+a)*colorTotal k := by
    have h := separated_color_pair_estimates k hk (half_pos ha) (half_pos hA).le
      hη hηq (le_refl ((A/2+a/2)/(η*(a/2)))) hcd (hsep c d hcd)
      v w hv hw hwb s t hs ht
    constructor
    · calc
        a/4 = (a/2)/2*1 := by ring
        _ ≤ (a/2)/2*k d := mul_le_mul_of_nonneg_left (hk d) (by positivity)
        _ ≤ ‖s • (k c • v) + t • (k d • w)‖ := h.1
    · calc
        ‖s • (k c • v) + t • (k d • w)‖ ≤ 2*(A/2+a/2)*k d := h.2.1
        _ ≤ (2*A+a)*k d := mul_le_mul_of_nonneg_right (by linarith) (hkpos d).le
        _ ≤ (2*A+a)*colorTotal k := mul_le_mul_of_nonneg_left
          (color_le_total k hk d) (by positivity)
  cases q with
  | difference g z w hne =>
    simpa only [Pair.vector, Pair.beat, smul_sub] using
      hold (Pair.difference g.1 z w hne) g.2
  | sum g z w =>
    simpa only [Pair.vector, Pair.beat, smul_add] using hold (Pair.sum g.1 z w) g.2
  | cross g h hne z w s t hs ht =>
    by_cases hc : g.2 = h.2
    · have hij : g.1 ≠ h.1 := fun he ↦ hne (Prod.ext he hc)
      simpa only [Pair.vector, Pair.beat, smul_add, smul_smul, hc, mul_comm] using
        hold (Pair.cross g.1 h.1 hij z w s t hs ht) g.2
    · have hkn : k g.2 ≠ k h.2 := fun he ↦ hc (hki he)
      have hx := carrier_norm_bounds S f a A hpair x g.1 z
      have hy := carrier_norm_bounds S f a A hpair x h.1 w
      rcases lt_or_gt_of_ne hkn with hlt | hgt
      · simpa only [Pair.vector, Pair.beat, mul_one] using
          hcross g.2 h.2 hlt (f x g.1 z) (f x h.1 w) hx.2 hy.1 hy.2 s t hs ht
      · simpa only [Pair.vector, Pair.beat, mul_one, add_comm] using
          hcross h.2 g.2 hgt (f x h.1 w) (f x g.1 z) hy.2 hx.1 hx.2 t s ht hs

/-- Projection commutes with the literal signed vector, including its signs. -/
theorem projectAway_pair_vector {n : ℕ} {I Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {S : I → Set Z}
    (L : Submodule ℝ (Euclidean n)) (f : I → Z → Euclidean n) (q : Pair I Z S) :
    projectAway L (q.vector f) = q.vector (fun i z ↦ projectAway L (f i z)) := by
  cases q <;> simp [Pair.vector, map_add, map_sub, map_smul]

/-- Full native colored signed geometry with all true-frequency factors.
The only fixed numerical enlargement is the explicit finite color constant.
The projected lower bound is obtained from the SAME norm argument applied to
each old projection, not from an assumed colored noncharacteristicity claim. -/
theorem refined_signed_bounds {n : ℕ} {I C X Z : Type*} [Fintype C]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : I → Set Z) (f : X → I → Z → Euclidean n)
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A)
    (hpair : ∀ x (q : Pair I Z S),
      a*q.beat ≤ ‖q.vector (f x)‖ ∧ ‖q.vector (f x)‖ ≤ A*q.beat)
    (hproj : ∀ x (q : Pair I Z S) L, L ∈ cubeBadSubspaces n →
      a*q.beat ≤ ‖projectAway L (q.vector (f x))‖)
    (k : C → ℝ) (hk : ∀ c, 1 ≤ k c) (hki : Function.Injective k)
    (η : ℝ) (hη : 0 < η) (hηq : η ≤ 1/4)
    (hsep : ∀ c d, k c < k d → ((A/2+a/2)/(η*(a/2)))*k c ≤ k d) :
    0 < a/4 ∧ 0 < (2*A+a)*colorTotal k ∧
    ∀ x (q : Pair (I × C) Z (fun ic ↦ S ic.1)),
      (∀ L ∈ cubeBadSubspaces n,
        (a/4)*q.beat ≤ ‖projectAway L (q.vector (fun ic z ↦ k ic.2 • f x ic.1 z))‖) ∧
      q.vector (fun ic z ↦ k ic.2 • f x ic.1 z) ≠ 0 ∧
      ∀ lam : ℝ, 0 ≤ lam →
        (a/4)*(lam*q.beat) ≤ ‖lam • q.vector (fun ic z ↦ k ic.2 • f x ic.1 z)‖ ∧
        ‖lam • q.vector (fun ic z ↦ k ic.2 • f x ic.1 z)‖ ≤
          ((2*A+a)*colorTotal k)*(lam*q.beat) := by
  have ha4 : 0 < a/4 := by positivity
  refine ⟨ha4, mul_pos (by positivity) (colorTotal_pos k hk), ?_⟩
  intro x q
  have hnorm := refined_pair_norm_bounds S f a A ha hA hpair k hk hki η hη hηq hsep x q
  refine ⟨?_, norm_pos_iff.mp ((mul_pos ha4 q.beat_pos).trans_le hnorm.1), ?_⟩
  · intro L hL
    have hLpair (y : X) (q₀ : Pair I Z S) :
        a*q₀.beat ≤ ‖q₀.vector (fun i z ↦ projectAway L (f y i z))‖ ∧
          ‖q₀.vector (fun i z ↦ projectAway L (f y i z))‖ ≤ A*q₀.beat := by
      rw [← projectAway_pair_vector]
      exact ⟨hproj y q₀ L hL, (norm_projectAway_le L _).trans (hpair y q₀).2⟩
    have hbound := refined_pair_norm_bounds S (fun y i z ↦ projectAway L (f y i z))
      a A ha hA hLpair k hk hki η hη hηq hsep x q
    simpa only [projectAway_pair_vector, map_smul] using hbound.1
  · intro lam hlam
    rw [norm_smul, Real.norm_of_nonneg hlam]
    constructor
    · calc
        (a/4)*(lam*q.beat) = lam*((a/4)*q.beat) := by ring
        _ ≤ lam*‖q.vector (fun ic z ↦ k ic.2 • f x ic.1 z)‖ :=
          mul_le_mul_of_nonneg_left hnorm.1 hlam
    · calc
        lam*‖q.vector (fun ic z ↦ k ic.2 • f x ic.1 z)‖ ≤
            lam*(((2*A+a)*colorTotal k)*q.beat) := mul_le_mul_of_nonneg_left hnorm.2 hlam
        _ = ((2*A+a)*colorTotal k)*(lam*q.beat) := by ring

end JanetCartan.PhysicalInitialization.ColoredRefinement
end
