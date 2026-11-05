module

public import JanetCartan.Iteration.PhysicalMean.CrossLeibniz
public import JanetCartan.Analysis.Sobolev.Local.Cutoff.Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lossless jet budgets for the differentiated lower cross factor

The exact lower derivative word from the Hermitian Leibniz formula consumes
only its actual additional derivative order. Applying this to the SAME
full individual inverse field at order `ell+t` gives `H^ell(∂^t Dνv)`;
no Sobolev embedding or extra source derivative is introduced
(`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open BallExtension

private theorem word_smooth {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f) (ds : List (Fin n)) :
    ContDiff ℝ ∞ (cartesianCoordinateDerivList ds f) :=
  contDiffOn_univ.mp (contDiffOn_cartesianCoordinateDerivList isOpen_univ hf.contDiffOn ds)

/-- A physical derivative word followed by `j` Frechet derivatives costs
exactly `j + length(word)` actual derivatives, with constant one. -/
theorem norm_iteratedFDeriv_cartesianWord_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin n)) (j : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f) x‖ ≤
      ‖iteratedFDeriv ℝ (j+ds.length) f x‖ := by
  induction ds generalizing j with
  | nil => simp only [cartesianCoordinateDerivList, List.length_nil, Nat.add_zero, le_refl]
  | cons i ds ih =>
    have hs := (word_smooth hf ds).fderiv_right (m := ∞) (by simp)
    have hb := norm_iteratedFDeriv_clm_apply_const (hs.contDiffAt (x := x))
      (show (j : ℕ∞ω) ≤ ∞ by simp) (c := EuclideanSpace.basisFun (Fin n) ℝ i)
    have he : ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ = 1 := by
      simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single]
    rw [he, one_mul, norm_iteratedFDeriv_fderiv] at hb
    have heq : j+1+ds.length = j+(i::ds).length := by simp only [List.length_cons]; omega
    have hii := ih (j+1)
    rw [heq] at hii
    exact hb.trans hii

/-- A differentiated lower factor has the exact same-order L² jet budget.
Membership is retained before real-valued Lp norms are taken. The harmless
factor `s+1` counts physical jet orders only, never samples or frequency bands. -/
theorem cartesianWord_jet_L2_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin n)) (s : ℕ)
    (hmem : ∀ j ≤ s+ds.length, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f)) 2 volume) ∧
      (∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f)) 2 volume) ≤
        ((s : ℝ)+1) * ∑ k ∈ Finset.range (s+ds.length+1), lpNorm (iteratedFDeriv ℝ k f) 2 volume := by
  have hnorm (j : ℕ) (hj : j ≤ s) :
      MemLp (iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f)) 2 volume ∧
      lpNorm (iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f)) 2 volume ≤
        lpNorm (iteratedFDeriv ℝ (j+ds.length) f) 2 volume := by
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f)) volume :=
      ((word_smooth hf ds).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    have hi := hmem (j+ds.length) (by omega)
    have hpoint (x : Euclidean n) :
        ‖iteratedFDeriv ℝ j (cartesianCoordinateDerivList ds f) x‖ ≤
          1 * ‖iteratedFDeriv ℝ (j+ds.length) f x‖ := by
      simpa only [one_mul] using norm_iteratedFDeriv_cartesianWord_le hf ds j x
    refine ⟨hi.of_le_mul hmeas (Filter.Eventually.of_forall hpoint), ?_⟩
    simpa only [toReal_eLpNorm, one_mul] using
      LocalSobolev.eLpNorm_toReal_le_mul_of_bound hmeas hi zero_le_one hpoint
  refine ⟨fun j hj ↦ (hnorm j hj).1, ?_⟩
  calc
    _ ≤ ∑ _j ∈ Finset.range (s+1),
        ∑ k ∈ Finset.range (s+ds.length+1), lpNorm (iteratedFDeriv ℝ k f) 2 volume := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact ((hnorm j hj').2).trans
        (Finset.single_le_sum (fun k _ ↦ lpNorm_nonneg)
          (show j+ds.length ∈ Finset.range (s+ds.length+1) by simp only [Finset.mem_range]; omega))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- Coefficient words preserve the exact total derivative order in the
modified amplitude. Only this genuine coefficient uses a C-norm; the
source-dependent lower field uses the L² theorem above. -/
theorem cNorm_cartesianWord_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f)
    {K : Set (Euclidean n)} (hK : IsCompact K) (ds : List (Fin n)) (s : ℕ) :
    cNorm K s (cartesianCoordinateDerivList ds f) ≤
      ((s : ℝ)+1)*cNorm K (s+ds.length) f := by
  have hb := cNorm_le_sum_of_bounds (r := s) (C := fun _ ↦ cNorm K (s+ds.length) f)
    (fun _ _ ↦ cNorm_nonneg K (s+ds.length) f)
    (fun j hj x hx ↦ (norm_iteratedFDeriv_cartesianWord_le hf ds j x).trans
      (norm_iteratedFDeriv_le_cNorm hK (hf.of_le (by simp)) hx (by omega)))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hb

/-- The measurement coefficient pays the scalar tester's `ell` reserve
exactly once. A word of length `c` leaves `T^(c-s0)` after its full C^ell
amplitude norm; the constant is a finite fixed derivative-profile sum. -/
theorem cNorm_cartesianWord_le_reserve {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f)
    (K : Set (Euclidean n)) (ds : List (Fin n)) (ell s₀ : ℕ)
    {T : ℝ} (hT : 1 ≤ T) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hjet : ∀ x ∈ K, ∀ j ≤ ell+ds.length,
      ‖iteratedFDeriv ℝ j f x‖ ≤ a j*T^(j-(s₀+ell))) :
    cNorm K ell (cartesianCoordinateDerivList ds f) ≤
      (∑ j ∈ Finset.range (ell+1), a (j+ds.length))*T^(ds.length-s₀) := by
  have hb := cNorm_le_sum_of_bounds (r := ell)
    (C := fun j ↦ a (j+ds.length)*T^(ds.length-s₀))
    (fun j _ ↦ mul_nonneg (ha _) (pow_nonneg (zero_le_one.trans hT) _))
    (fun j hj x hx ↦ ((norm_iteratedFDeriv_cartesianWord_le hf ds j x).trans
      (hjet x hx (j+ds.length) (by omega))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (ha _)))
  simpa only [Finset.sum_mul] using hb

end JanetCartan.PhysicalMean
