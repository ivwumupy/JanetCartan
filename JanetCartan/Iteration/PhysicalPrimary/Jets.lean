module

public import JanetCartan.Iteration.PhysicalPrimary.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Physical jet norms of the unchanged compact cutoff

Paper-v2 `main:eq:primary-fixed-scales`: a fixed physical cutoff preserves
an order-r local jet bound at that SAME order. All derivatives are ambient
real derivatives and their L² norms use Euclidean volume. There is no torus
norm or periodization. Constants precede the input field, domain, amplitude,
and frequency. Only the original buffered domain around the support is needed.

Consumer: the sharp physical sampled-primary and completed-mean profiles,
followed by `PhysicalSobolev.exists_physicalWeightedNorm_le_jetL2`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalPrimary

open UniformStep

private theorem l2Norm_le_of_compact_bound {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] {f : Euclidean n → V}
    (hf : AEStronglyMeasurable f volume) {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : Function.support f ⊆ K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ K, ‖f x‖ ≤ M) :
    (eLpNorm f 2 volume).toReal ≤ M * (volume K).toReal ^ (1 / 2 : ℝ) := by
  classical
  have hg : MemLp (K.indicator (fun _ : Euclidean n ↦ M)) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet M (Or.inr hK.measure_lt_top.ne)
  have he : eLpNorm f 2 volume ≤ eLpNorm (K.indicator (fun _ : Euclidean n ↦ M)) 2 volume := by
    apply eLpNorm_mono_real hf
    intro x
    by_cases hx : x ∈ K
    · simpa only [indicator_of_mem hx] using hb x hx
    · have hz : f x = 0 := by
        by_contra hz
        exact hx (hs hz)
      simp only [hz, norm_zero, indicator_of_notMem hx, le_refl]
  apply (ENNReal.toReal_mono hg.eLpNorm_ne_top he).trans_eq
  rw [eLpNorm_indicator_const hK.measurableSet.nullMeasurableSet (by norm_num) (by norm_num),
    ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg hM, ENNReal.toReal_rpow]
  norm_num

/-- Every actual order-q jet of the fixed cutoff is bounded by an order-r
local norm, for `q ≤ r`, with no derivative reserve. The original input
field need be smooth only on a buffered open set containing the unchanged
cutoff support (`main:thm:step`, `main:eq:mean-normal-field`). -/
theorem norm_iteratedFDeriv_cutSchwartzOfSupport_le {n N : ℕ} (D : LocalDomain)
    (f : Euclidean n → Euclidean N) {U : Set (Euclidean n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hsU : tsupport (physicalCutoff (n := n) D) ⊆ U)
    (r q : ℕ) (hqr : q ≤ r) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ q (cutSchwartzOfSupport D f hU hf hsU) x‖ ≤
      (2 : ℝ) ^ r * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
        r (physicalCutoff (n := n) D) *
      cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) r f := by
  let K := closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut
  have hKU : K ⊆ U := by simpa only [(physicalCutoff (n := n) D).tsupport_eq] using hsU
  have hs : tsupport (cutSchwartzOfSupport D f hU hf hsU : Euclidean n → Euclidean N) ⊆
      tsupport (physicalCutoff (n := n) D) := by
    change tsupport (fun x ↦ physicalCutoff D x • f x) ⊆ tsupport (physicalCutoff (n := n) D)
    exact tsupport_smul_subset_left (physicalCutoff (n := n) D) f
  by_cases hx : x ∈ tsupport (physicalCutoff (n := n) D)
  · have hxK : x ∈ K := by simpa only [(physicalCutoff (n := n) D).tsupport_eq] using hx
    have hxU := hKU hxK
    let B : ℝ →L[ℝ] Euclidean N →L[ℝ] Euclidean N := ContinuousLinearMap.lsmul ℝ ℝ
    have hjet := B.norm_iteratedFDerivWithin_le_of_bilinear
      (physicalCutoff D).contDiff.contDiffOn hf hU.uniqueDiffOn hxU (n := q) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hjet
    have hχb (i : ℕ) (hi : i ≤ r) :
        ‖iteratedFDeriv ℝ i (physicalCutoff (n := n) D) x‖ ≤ cNorm K r (physicalCutoff (n := n) D) :=
      norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        (physicalCutoff D).contDiff hxK hi
    have hfb (i : ℕ) (hi : i ≤ r) : ‖iteratedFDeriv ℝ i f x‖ ≤ cNorm K r f :=
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp)) hxK hi
    change ‖iteratedFDeriv ℝ q (fun y ↦ B (physicalCutoff D y) (f y)) x‖ ≤ _
    apply hjet.trans
    calc
      _ ≤ 1 * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          cNorm K r (physicalCutoff (n := n) D) * cNorm K r f := by
        apply mul_le_mul ContinuousLinearMap.opNorm_lsmul_le _ (by positivity) zero_le_one
        apply Finset.sum_le_sum
        intro i hi
        have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hχb i hir) (Nat.cast_nonneg _))
          (hfb (q-i) ((Nat.sub_le _ _).trans hqr)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      _ = (2 : ℝ) ^ q * cNorm K r (physicalCutoff (n := n) D) * cNorm K r f := by
        rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose q
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hqr)
          (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  · have hz : iteratedFDeriv ℝ q (cutSchwartzOfSupport D f hU hf hsU) x = 0 := by
      by_contra hz
      exact hx (hs (support_iteratedFDeriv_subset q hz))
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)

/-- The actual compact real cutoff has an order-r sum of L² jet norms
controlled by the SAME order-r local norm. Constants precede fields, buffered
source domains, and frequencies (`main:eq:primary-fixed-scales`). -/
theorem exists_cutSchwartzOfSupport_jetL2_bound {n N : ℕ} (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euclidean n → Euclidean N)
      {U : Set (Euclidean n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
      (hsU : tsupport (physicalCutoff (n := n) D) ⊆ U),
      (∑ j ∈ Finset.range (r + 1),
        (eLpNorm (iteratedFDeriv ℝ j (cutSchwartzOfSupport D f hU hf hsU)) 2 volume).toReal) ≤
        C * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) r f := by
  let K := closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut
  let A := (2 : ℝ) ^ r * cNorm K r (physicalCutoff (n := n) D)
  let v := (volume K).toReal ^ (1 / 2 : ℝ)
  have hA : 0 ≤ A := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  refine ⟨((r + 1 : ℕ) : ℝ) * A * v, by positivity, ?_⟩
  intro f U hU hf hsU
  have hb (j : ℕ) (hj : j ≤ r) :
      (eLpNorm (iteratedFDeriv ℝ j (cutSchwartzOfSupport D f hU hf hsU)) 2 volume).toReal ≤
        A * cNorm K r f * v := by
    have hcont := ((cutSchwartzOfSupport D f hU hf hsU).smooth ⊤).continuous_iteratedFDeriv
      (m := j) (by simp)
    apply l2Norm_le_of_compact_bound hcont.aestronglyMeasurable
      (isCompact_closedBall _ _) (fun x hx ↦ ?_) (mul_nonneg hA (cNorm_nonneg _ _ _))
      (fun x _ ↦ norm_iteratedFDeriv_cutSchwartzOfSupport_le D f hU hf hsU r j hj x)
    have hs : tsupport (cutSchwartzOfSupport D f hU hf hsU : Euclidean n → Euclidean N) ⊆
        tsupport (physicalCutoff (n := n) D) := by
      change tsupport (fun x ↦ physicalCutoff D x • f x) ⊆ tsupport (physicalCutoff (n := n) D)
      exact tsupport_smul_subset_left (physicalCutoff (n := n) D) f
    have hx' := hs (support_iteratedFDeriv_subset j hx)
    simpa only [(physicalCutoff (n := n) D).tsupport_eq] using hx'
  calc
    _ ≤ ∑ _j ∈ Finset.range (r + 1), A * cNorm K r f * v :=
      Finset.sum_le_sum fun j hj ↦ hb j (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Chart-specialized version for the literal physical primary, with the
same constant and no extra smoothness beyond its actual chart. -/
theorem exists_cutSchwartz_jetL2_bound {n N : ℕ} (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euclidean n → Euclidean N)
      (hf : ContDiffOn ℝ ∞ f (D.chart n)),
      (∑ j ∈ Finset.range (r + 1), (eLpNorm (iteratedFDeriv ℝ j (cutSchwartz D f hf)) 2 volume).toReal) ≤
        C * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) r f := by
  obtain ⟨C, hC, hcut⟩ := exists_cutSchwartzOfSupport_jetL2_bound (n := n) (N := N) D r
  refine ⟨C, hC, fun f hf ↦ ?_⟩
  exact hcut f isOpen_ball hf (physicalCutoff_properties (n := n) D).2.1

end JanetCartan.PhysicalPrimary
