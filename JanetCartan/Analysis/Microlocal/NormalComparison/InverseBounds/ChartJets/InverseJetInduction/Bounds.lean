module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Bounds for a differential equation along a graph

The finite induction used in implicit differentiation in Step 1 of
`app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.NormalComparison.InverseChartJet
variable {S E V : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positive jets of a linear map, used for the fixed coordinate projections
in `app:ch_osc:prop:osc-normal`. -/
theorem norm_iteratedFDeriv_linear_pos_le (L : S →L[ℝ] E) (z : S)
    {k : ℕ} (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k L z‖ ≤ ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ (L : S → E) = fun _ ↦ L := funext fun _ ↦ L.fderiv
  rw [he]
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]

/-- A smooth differential equation `Dg = H ∘ (Q + Lg)` with bounded
coefficient jets controls all finite jets of `g`. Constants precede the
functions; this is the induction in `app:ch_osc:prop:osc-normal`, Step 1. -/
theorem exists_jet_bound_of_fderiv_eq_comp
    (Q : S →L[ℝ] S) (L : E →L[ℝ] S) (N : ℕ) (A M : ℝ) :
    ∃ K > 0, ∀ (g : S → E) (H : S → S →L[ℝ] E) (U W : Set S),
      IsOpen U → IsOpen W → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ H W →
      MapsTo (fun z ↦ Q z + L (g z)) U W →
      (∀ z ∈ U, fderiv ℝ g z = H (Q z + L (g z))) →
      (∀ z ∈ U, ‖g z‖ ≤ A) →
      (∀ z ∈ W, ∀ k ≤ N, ‖iteratedFDeriv ℝ k H z‖ ≤ M) →
      ∀ z ∈ U, ∀ k ≤ N, ‖iteratedFDeriv ℝ k g z‖ ≤ K := by
  induction N with
  | zero =>
    refine ⟨max 1 A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro g H U W hU hW hg hH hmap heq hA hM z hz k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa only [norm_iteratedFDeriv_zero] using (hA z hz).trans (le_max_right 1 A)
  | succ N ih =>
    obtain ⟨K, hK, hbound⟩ := ih
    let D := max 1 (‖Q‖ + ‖L‖ * K)
    let R := (N.factorial : ℝ) * max 1 M * D ^ N
    refine ⟨max K R, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
    intro g H U W hU hW hg hH hmap heq hA hM z hz k hk
    have hprev := hbound g H U W hU hW hg hH hmap heq hA
      (fun z hz i hi ↦ hM z hz i (by omega))
    by_cases hkN : k ≤ N
    · exact (hprev z hz k hkN).trans (le_max_left _ _)
    have hk' : k = N + 1 := by omega
    subst k
    let T : S → S := fun z ↦ Q z + L (g z)
    have hT : ContDiffOn ℝ ∞ T U := Q.contDiff.contDiffOn.add (L.contDiff.comp_contDiffOn hg)
    have hD (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
        ‖iteratedFDerivWithin ℝ i T U z‖ ≤ D ^ i := by
      rw [iteratedFDerivWithin_of_isOpen _ hU hz]
      have hgz := hg.contDiffAt (hU.mem_nhds hz)
      rw [show T = fun z ↦ Q z + (L ∘ g) z from rfl,
        fun_iteratedFDeriv_add_apply ((Q.contDiff (n := i)).contDiffAt)
          (((L.contDiff (n := i)).contDiffAt.comp z (hgz.of_le (by simp))))]
      apply (norm_add_le _ _).trans
      apply (add_le_add (norm_iteratedFDeriv_linear_pos_le Q z hi)
        ((L.norm_iteratedFDeriv_comp_left hgz (by simp)).trans
          (mul_le_mul_of_nonneg_left (hprev z hz i hiN) (norm_nonneg L)))).trans
      exact (le_max_right 1 _).trans (le_self_pow₀ (le_max_left 1 _) (by omega))
    have hb := norm_iteratedFDerivWithin_comp_le hH hT (n := N) (by simp)
      hW.uniqueDiffOn hU.uniqueDiffOn hmap hz
      (fun i hi ↦ by
        rw [iteratedFDerivWithin_of_isOpen _ hW (hmap hz)]
        exact (hM _ (hmap hz) i (by omega)).trans (le_max_right 1 M)) hD
    rw [iteratedFDerivWithin_of_isOpen _ hU hz] at hb
    have heqjet := iteratedFDerivWithin_congr (𝕜 := ℝ) (show EqOn (fderiv ℝ g) (H ∘ T) U from heq) hz N
    rw [iteratedFDerivWithin_of_isOpen _ hU hz,
      iteratedFDerivWithin_of_isOpen _ hU hz] at heqjet
    rw [← norm_iteratedFDeriv_fderiv, heqjet]
    exact hb.trans (le_max_right K R)

/-- The bilinear product estimate on an open set, with constant jet bounds,
used for the inverse differential in `app:ch_osc:prop:osc-normal`. -/
theorem norm_iteratedFDeriv_bilinear_on_open_le
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (b : E →L[ℝ] V →L[ℝ] T) (hb : ‖b‖ ≤ 1)
    {f : S → E} {g : S → V} {U : Set S} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {A B : ℝ} (hA : 0 ≤ A) {z : S} (hz : z ∈ U) (k : ℕ)
    (hfjet : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f z‖ ≤ A)
    (hgjet : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g z‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun q ↦ b (f q) (g q)) z‖ ≤ (2 : ℝ)^k * A * B := by
  have h := b.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf hg hU.uniqueDiffOn hz
    (n := k) (by simp) hb
  simp only [iteratedFDerivWithin_of_isOpen _ hU hz] at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfjet i hik) (by positivity))
        (hgjet (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (by positivity) hA)
    _ = (2 : ℝ)^k * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

/-- Jets of the coefficient in the implicit differential formula depend only
on forward jets and inverse-Jacobian jets (`app:ch_osc:prop:osc-normal`). -/
theorem norm_iteratedFDeriv_implicitCoefficient_le
    (P : S →L[ℝ] E) (Q : S →L[ℝ] S) {f : S → E} {a : S → E →L[ℝ] E}
    {W : Set S} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (ha : ContDiffOn ℝ ∞ a W) {N : ℕ} {B J : ℝ}
    (hfjet : ∀ z ∈ W, ∀ i ≤ N + 1, ‖iteratedFDeriv ℝ i f z‖ ≤ B)
    (hajet : ∀ z ∈ W, ∀ i ≤ N, ‖iteratedFDeriv ℝ i a z‖ ≤ J)
    {z : S} (hz : z ∈ W) {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun q ↦ a q ∘L (P - fderiv ℝ f q ∘L Q)) z‖ ≤
      (2 : ℝ)^N * max 0 J * (‖P‖ + ‖Q‖ * max 0 B) := by
  let R : (S →L[ℝ] E) →L[ℝ] (S →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ S S E).flip Q
  have hR : ‖R‖ ≤ ‖Q‖ := by
    apply R.opNorm_le_bound (norm_nonneg Q)
    intro A
    exact (ContinuousLinearMap.opNorm_comp_le A Q).trans_eq (mul_comm _ _)
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) W := hf.fderiv_of_isOpen hW (by simp)
  have hcoeff : ContDiffOn ℝ ∞ (fun q ↦ P - fderiv ℝ f q ∘L Q) W :=
    contDiffOn_const.sub (hdf.clm_comp contDiffOn_const)
  have hcoeffjet (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun q ↦ P - fderiv ℝ f q ∘L Q) z‖ ≤ ‖P‖ + ‖Q‖ * max 0 B := by
    have hconst : ‖iteratedFDeriv ℝ i (fun _ : S ↦ P) z‖ ≤ ‖P‖ := by
      cases i with
      | zero => simp
      | succ i => simp [iteratedFDeriv_succ_const]
    have hzdf := hdf.contDiffAt (hW.mem_nhds hz)
    have hlin := R.norm_iteratedFDeriv_comp_left hzdf (n := i) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at hlin
    have hj : ‖iteratedFDeriv ℝ i (R ∘ fderiv ℝ f) z‖ ≤ ‖Q‖ * max 0 B :=
      hlin.trans (mul_le_mul hR ((hfjet z hz (i + 1) (by omega)).trans (le_max_right 0 B))
        (norm_nonneg _) (norm_nonneg Q))
    change ‖iteratedFDeriv ℝ i (fun q ↦ P - (R ∘ fderiv ℝ f) q) z‖ ≤ _
    rw [fun_iteratedFDeriv_sub_apply contDiffAt_const
      ((R.contDiff (n := i)).contDiffAt.comp z (hzdf.of_le (by simp))) ]
    exact (norm_sub_le _ _).trans (add_le_add hconst hj)
  have hb := norm_iteratedFDeriv_bilinear_on_open_le (ContinuousLinearMap.compL ℝ S E E)
    (ContinuousLinearMap.norm_compL_le ℝ S E E) hW ha hcoeff
    (le_max_left 0 J) hz k
    (fun i hi ↦ (hajet z hz i (hi.trans hk)).trans (le_max_right 0 J)) hcoeffjet
  exact hb.trans (by gcongr; norm_num)

end JanetCartan.NormalComparison.InverseChartJet
