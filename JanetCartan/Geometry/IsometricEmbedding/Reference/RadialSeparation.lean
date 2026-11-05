module

public import Mathlib.Analysis.Normed.Module.Normalize

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite radial separation of carrier groups

The elementary radial-domination argument in Step 4 of
Proposition `app:ch_seed:prop:seed-frozen-menu` of `paper.tex`, with the literal
indices of Definition `app:defn:exhaustive-pair-groups`.

Geometric labels are chosen on an arbitrary finite index type. They depend only
on the common norm bounds and a direction tolerance, before any choice of sample
parameters. The estimates hold in any real normed space and for both signs, even
when different indices specify identical carrier maps. Small uniform perturbations
preserve the bounds and the proximity to the signed dominant carrier direction.

These are elementary norm estimates. The regularity gap of the carrier directions
and the detecting-carrier construction are separate geometric inputs.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- Proposition `app:ch_seed:prop:seed-frozen-menu`, Step 4: a finite index type
admits distinct positive geometric labels with any prescribed successive ratio.
The indices are not quotiented by their carrier specifications; see
Definition `app:defn:exhaustive-pair-groups`. -/
theorem exists_radial_labels (ι : Type*) [Finite ι] (K : ℝ) :
    ∃ R : ι → ℝ, (∀ i, 1 ≤ R i) ∧ Function.Injective R ∧
      ∀ i j, R i < R j → K * R i ≤ R j := by
  let := Fintype.ofFinite ι
  let q : ℝ := max K 1 + 1
  have hq : 1 < q := by dsimp [q]; linarith [le_max_right K 1]
  let e : ι → ℕ := fun i ↦ (Fintype.equivFin ι i).val
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin ι).injective
  refine ⟨fun i ↦ q ^ e i, fun _ ↦ one_le_pow₀ hq.le,
    (pow_right_strictMono₀ hq).injective.comp he, ?_⟩
  intro i j hij
  have heij : e i < e j := (pow_right_strictMono₀ hq).lt_iff_lt.mp hij
  calc
    K * q ^ e i ≤ q * q ^ e i := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (le_max_left K 1).trans (by dsimp [q]; linarith)
    _ = q ^ (e i + 1) := by rw [pow_succ, mul_comm]
    _ ≤ q ^ e j := pow_le_pow_right₀ hq.le heij

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalization estimate used in the radial-label argument of
Proposition `app:ch_seed:prop:seed-frozen-menu`. It is valid even at zero, with
Mathlib's convention `normalize 0 = 0`. -/
theorem norm_mul_normalize_sub_le (u v : E) :
    ‖v‖ * ‖NormedSpace.normalize u - NormedSpace.normalize v‖ ≤ 2 * ‖u - v‖ := by
  have hn : ‖NormedSpace.normalize u‖ ≤ 1 := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (NormedSpace.norm_normalize hu).le
  have hid : ‖v‖ • (NormedSpace.normalize u - NormedSpace.normalize v) =
      (‖v‖ - ‖u‖) • NormedSpace.normalize u + (u - v) := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  calc
    ‖v‖ * ‖NormedSpace.normalize u - NormedSpace.normalize v‖ =
        ‖‖v‖ • (NormedSpace.normalize u - NormedSpace.normalize v)‖ := by
      simp [norm_smul]
    _ ≤ |‖v‖ - ‖u‖| * ‖NormedSpace.normalize u‖ + ‖u - v‖ := by
      rw [hid]
      simpa [norm_smul] using norm_add_le
        ((‖v‖ - ‖u‖) • NormedSpace.normalize u) (u - v)
    _ ≤ |‖v‖ - ‖u‖| + ‖u - v‖ := by nlinarith [abs_nonneg (‖v‖ - ‖u‖)]
    _ ≤ 2 * ‖u - v‖ := by
      have h := abs_norm_sub_norm_le v u
      rw [norm_sub_rev] at h
      linarith

/-- Proposition `app:ch_seed:prop:seed-frozen-menu`, Step 4: a dominant radius
protects the norm and normalized direction of a signed pair after perturbing both
carriers by at most `η * a`. The signs are arbitrary real scalars of absolute value
one; the reference direction is the signed, unperturbed dominant carrier. -/
theorem radial_pair_estimates {a b η r R s t : ℝ} {x y x' y' : E}
    (ha : 0 < a) (hb : 0 ≤ b) (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hr : 0 ≤ r) (hR : 0 < R) (hrR : r ≤ R)
    (hdom : r * (b + a) ≤ η * a * R)
    (hx : ‖x‖ ≤ b) (hy : a ≤ ‖y‖) (hyb : ‖y‖ ≤ b)
    (hx' : ‖x' - x‖ ≤ η * a) (hy' : ‖y' - y‖ ≤ η * a)
    (hs : |s| = 1) (ht : |t| = 1) :
    a / 2 * R ≤ ‖s • (r • x') + t • (R • y')‖ ∧
    ‖s • (r • x') + t • (R • y')‖ ≤ 2 * (b + a) * R ∧
    ‖NormedSpace.normalize (s • (r • x') + t • (R • y')) -
      NormedSpace.normalize (t • y)‖ ≤ 4 * η := by
  have hηa : η * a ≤ a := by nlinarith
  have hxp : ‖x'‖ ≤ b + a := by linarith [norm_sub_norm_le x' x]
  have hyp : ‖y'‖ ≤ b + a := by linarith [norm_sub_norm_le y' y]
  let w := s • (r • x') + t • (R • y')
  let v := t • (R • y)
  have hsmall : ‖s • (r • x')‖ ≤ r * (b + a) := by
    simpa [norm_smul, hs, abs_of_nonneg hr] using mul_le_mul_of_nonneg_left hxp hr
  have hlarge : ‖t • (R • y')‖ ≤ R * (b + a) := by
    simpa [norm_smul, ht, abs_of_pos hR] using mul_le_mul_of_nonneg_left hyp hR.le
  have hv : ‖v‖ = R * ‖y‖ := by simp [v, norm_smul, ht, abs_of_pos hR]
  have hv_lower : a * R ≤ ‖v‖ := by rw [hv]; nlinarith
  have herr : ‖w - v‖ ≤ 2 * η * a * R := by
    have hid : w - v = s • (r • x') + t • (R • (y' - y)) := by
      simp [w, v, smul_sub, add_sub_assoc]
    rw [hid]
    have hpert : ‖t • (R • (y' - y))‖ ≤ R * (η * a) := by
      simpa [norm_smul, ht, abs_of_pos hR] using
        mul_le_mul_of_nonneg_left hy' hR.le
    calc
      _ ≤ r * (b + a) + R * (η * a) := norm_add_le_of_le hsmall hpert
      _ ≤ 2 * η * a * R := by nlinarith [hdom]
  have hlower : a / 2 * R ≤ ‖w‖ := by
    have hrev := norm_sub_norm_le v w
    rw [norm_sub_rev] at hrev
    have hmargin : 2 * η * a * R ≤ a / 2 * R := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - 2 * η by linarith) (mul_pos ha hR).le]
    linarith
  refine ⟨hlower, ?_, ?_⟩
  · calc
      ‖w‖ ≤ r * (b + a) + R * (b + a) := norm_add_le_of_le hsmall hlarge
      _ ≤ 2 * (b + a) * R := by nlinarith
  · have hnorm := norm_mul_normalize_sub_le w v
    have hnonneg := norm_nonneg (NormedSpace.normalize w - NormedSpace.normalize v)
    have hmul : a * R * ‖NormedSpace.normalize w - NormedSpace.normalize v‖ ≤
        a * R * (4 * η) := by
      calc
        _ ≤ ‖v‖ * ‖NormedSpace.normalize w - NormedSpace.normalize v‖ :=
          mul_le_mul_of_nonneg_right hv_lower hnonneg
        _ ≤ 2 * ‖w - v‖ := hnorm
        _ ≤ a * R * (4 * η) := by nlinarith [herr]
    have hbound := (mul_le_mul_iff_right₀ (mul_pos ha hR)).mp hmul
    have hvnorm : NormedSpace.normalize v = NormedSpace.normalize (t • y) := by
      dsimp [v]
      rw [smul_comm t R y, NormedSpace.normalize_smul_of_pos hR]
    simpa only [hvnorm] using hbound

/-- Proposition `app:ch_seed:prop:seed-frozen-menu`, Step 4: fix radial labels
before sampling so that all signed pairs from distinct groups have quantitative
norm bounds and lie within any specified positive tolerance of the signed dominant
carrier direction. The same labels work for every carrier in the norm annulus
`[a, b]` and all perturbations of size at most `δ`. -/
theorem exists_stable_radial_separation (ι : Type*) [Finite ι]
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ (R : ι → ℝ) (δ : ℝ), (∀ i, 1 ≤ R i) ∧ Function.Injective R ∧ 0 < δ ∧
      ∀ (i j : ι), i ≠ j → ∀ (x y x' y' : E) (s t : ℝ),
        a ≤ ‖x‖ → ‖x‖ ≤ b → a ≤ ‖y‖ → ‖y‖ ≤ b →
        ‖x' - x‖ ≤ δ → ‖y' - y‖ ≤ δ → |s| = 1 → |t| = 1 →
        a / 2 * max (R i) (R j) ≤ ‖s • (R i • x') + t • (R j • y')‖ ∧
        ‖s • (R i • x') + t • (R j • y')‖ ≤ 2 * (b + a) * max (R i) (R j) ∧
        (R i < R j → ‖NormedSpace.normalize (s • (R i • x') + t • (R j • y')) -
          NormedSpace.normalize (t • y)‖ ≤ ε) ∧
        (R j < R i → ‖NormedSpace.normalize (s • (R i • x') + t • (R j • y')) -
          NormedSpace.normalize (s • x)‖ ≤ ε) := by
  let η : ℝ := min (1 / 4) (ε / 4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη' : η ≤ 1 / 4 := min_le_left _ _
  have hηε : 4 * η ≤ ε := by
    have := min_le_right (1 / 4 : ℝ) (ε / 4)
    linarith
  obtain ⟨R, hR, hinj, hratio⟩ := exists_radial_labels ι ((b + a) / (η * a))
  have hRpos (i : ι) : 0 < R i := lt_of_lt_of_le zero_lt_one (hR i)
  have hdom (i j : ι) (hij : R i < R j) : R i * (b + a) ≤ η * a * R j := by
    have h := hratio i j hij
    have h' : R i * (b + a) / (η * a) ≤ R j := by
      simpa only [div_mul_eq_mul_div, mul_comm (b + a)] using h
    have := (div_le_iff₀ (mul_pos hη ha)).mp h'
    nlinarith
  refine ⟨R, η * a, hR, hinj, mul_pos hη ha, ?_⟩
  intro i j hij x y x' y' s t hxa hxb hya hyb hx' hy' hs ht
  rcases lt_or_gt_of_ne (hinj.ne hij) with hij' | hji'
  · obtain ⟨hl, hu, hd⟩ := radial_pair_estimates ha hb hη hη' (hRpos i).le
      (hRpos j) hij'.le (hdom i j hij') hxb hya hyb hx' hy' hs ht
    rw [max_eq_right hij'.le]
    exact ⟨hl, hu, fun _ ↦ hd.trans hηε, fun h ↦ (not_lt_of_ge hij'.le h).elim⟩
  · obtain ⟨hl, hu, hd⟩ := radial_pair_estimates ha hb hη hη' (hRpos j).le
      (hRpos i) hji'.le (hdom j i hji') hyb hxa hxb hy' hx' ht hs
    rw [max_eq_left hji'.le]
    rw [add_comm] at hl hu hd
    exact ⟨hl, hu, fun h ↦ (not_lt_of_ge hji'.le h).elim, fun _ ↦ hd.trans hηε⟩

/-- Proposition `app:ch_seed:prop:seed-frozen-menu` and
Definition `app:defn:exhaustive-pair-groups`: uniform positive lower and upper bounds
for both inter-group differences and sums, stable under a uniform perturbation of
the carrier family. The parameter types may be infinite and may depend on the
group. No injectivity of the carrier specifications or of their values is assumed,
so duplicate specifications at distinct indices receive distinct labels.
Taking `ξ' = ξ` gives the frozen-family conclusion. -/
theorem exists_radial_carrier_separation {ι : Type*} [Finite ι]
    {Z : ι → Type*} (ξ : (i : ι) → Z i → E) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hξ : ∀ i z, a ≤ ‖ξ i z‖ ∧ ‖ξ i z‖ ≤ b) :
    ∃ (R : ι → ℝ) (δ c C : ℝ),
      (∀ i, 1 ≤ R i) ∧ Function.Injective R ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (ξ' : (i : ι) → Z i → E), (∀ i z, ‖ξ' i z - ξ i z‖ ≤ δ) →
        ∀ i j, i ≠ j → ∀ (z : Z i) (w : Z j),
          c ≤ ‖R i • ξ' i z - R j • ξ' j w‖ ∧
          ‖R i • ξ' i z - R j • ξ' j w‖ ≤ C ∧
          c ≤ ‖R i • ξ' i z + R j • ξ' j w‖ ∧
          ‖R i • ξ' i z + R j • ξ' j w‖ ≤ C := by
  obtain ⟨R, δ, hR, hinj, hδ, hsep⟩ :=
    exists_stable_radial_separation (E := E) ι ha hb zero_lt_one
  obtain ⟨M, hM⟩ := Finite.exists_le R
  refine ⟨R, δ, a / 2, 2 * (b + a) * max M 1, hR, hinj, hδ,
    by positivity, mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right M 1)), ?_⟩
  intro ξ' hξ' i j hij z w
  have hmin : a / 2 ≤ a / 2 * max (R i) (R j) := by
    have := (hR i).trans (le_max_left (R i) (R j))
    nlinarith
  have hmax : 2 * (b + a) * max (R i) (R j) ≤ 2 * (b + a) * max M 1 :=
    mul_le_mul_of_nonneg_left
      (max_le ((hM i).trans (le_max_left M 1)) ((hM j).trans (le_max_left M 1)))
      (by positivity)
  have hm := hsep i j hij (ξ i z) (ξ j w) (ξ' i z) (ξ' j w) 1 (-1)
    (hξ i z).1 (hξ i z).2 (hξ j w).1 (hξ j w).2 (hξ' i z) (hξ' j w)
    (by norm_num) (by norm_num)
  have hp := hsep i j hij (ξ i z) (ξ j w) (ξ' i z) (ξ' j w) 1 1
    (hξ i z).1 (hξ i z).2 (hξ j w).1 (hξ j w).2 (hξ' i z) (hξ' j w)
    (by norm_num) (by norm_num)
  simpa only [one_smul, neg_smul, sub_eq_add_neg] using
    And.intro (hmin.trans hm.1) (And.intro (hm.2.1.trans hmax)
      (And.intro (hmin.trans hp.1) (hp.2.1.trans hmax)))

end JanetCartan
