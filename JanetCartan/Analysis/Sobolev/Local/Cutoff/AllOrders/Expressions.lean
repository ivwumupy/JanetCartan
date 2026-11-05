module

public import JanetCartan.Analysis.Sobolev.Local.Cutoff.Product
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection

/-!
# Finite expressions for cutoff jets

For `app:ch_regular:eq:one-gain-tame`, differentiation of a cutoff jet is
implemented as a finite sum of smooth scalar coefficients times fixed linear
images of the original weak jet. These expressions record actual formulas,
not regularity assumptions. The consumer is the all-order cutoff construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped ContDiff

namespace JanetCartan.LocalSobolev.CutoffJet

variable {n : ℕ} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Finite linear differential expressions used to construct the product jet in
`app:ch_regular:eq:one-gain-tame`. Every coefficient is smooth and compactly supported. -/
inductive Expr (n : ℕ) (F G : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  | zero : Expr n F G
  | atom (k : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (smooth : ContDiff ℝ ∞ φ) (compact : HasCompactSupport φ)
      (A : ((EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F) →L[ℝ] G) : Expr n F G
  | add : Expr n F G → Expr n F G → Expr n F G

namespace Expr

/-- Evaluation on the original weak jet (`app:ch_regular:eq:one-gain-tame`). -/
def eval (J : (k : ℕ) → EuclideanSpace ℝ (Fin n) →
    (EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F) : Expr n F G → EuclideanSpace ℝ (Fin n) → G
  | .zero => fun _ ↦ 0
  | .atom k φ _ _ A => fun x ↦ φ x • A (J k x)
  | .add a b => fun x ↦ a.eval J x + b.eval J x

/-- Largest input derivative order in an expression (`app:ch_regular:eq:one-gain-tame`). -/
def order : Expr n F G → ℕ
  | .zero => 0
  | .atom k _ _ _ _ => k
  | .add a b => max a.order b.order

/-- Apply a fixed linear map to a cutoff expression (`app:ch_regular:eq:one-gain-tame`). -/
def map (L : G →L[ℝ] H) : Expr n F G → Expr n F H
  | .zero => .zero
  | .atom k φ hs hc A => .atom k φ hs hc (L.comp A)
  | .add a b => .add (a.map L) (b.map L)

/-- Fixed linear maps commute with evaluation (`app:ch_regular:eq:one-gain-tame`). -/
theorem eval_map (a : Expr n F G) (L : G →L[ℝ] H) (J) (x) :
    (a.map L).eval J x = L (a.eval J x) := by
  induction a with
  | zero => simp [map, eval]
  | atom => simp [map, eval]
  | add a b ha hb => simp [map, eval, ha, hb]

/-- A fixed linear map does not increase the input order
(`app:ch_regular:eq:one-gain-tame`). -/
theorem order_map (a : Expr n F G) (L : G →L[ℝ] H) : (a.map L).order = a.order := by
  induction a with
  | zero => rfl
  | atom => rfl
  | add a b ha hb => simp [map, order, ha, hb]

/-- Finite addition of cutoff expressions (`app:ch_regular:eq:one-gain-tame`). -/
def sum (l : List (Expr n F G)) : Expr n F G := l.foldr .add .zero

/-- Evaluation commutes with finite addition (`app:ch_regular:eq:one-gain-tame`). -/
theorem eval_sum (l : List (Expr n F G)) (J) (x) :
    (sum l).eval J x = (l.map (fun a ↦ a.eval J x)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa only [sum, List.foldr_cons, eval, List.map_cons, List.sum_cons] using
      (congrArg (fun z ↦ a.eval J x + z) ih)

/-- A finite sum uses only the input orders of its summands
(`app:ch_regular:eq:one-gain-tame`). -/
theorem order_sum_le (l : List (Expr n F G)) {s : ℕ}
    (h : ∀ a ∈ l, a.order ≤ s) : (sum l).order ≤ s := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (h a (by simp)) (ih (fun b hb ↦ h b (by simp [hb])))

/-- Differentiate each explicit term by the scalar weak Leibniz rule. The
coordinate sum expands the derivative of its scalar coefficient; the last
term differentiates the original jet (`app:ch_regular:eq:one-gain-tame`). -/
def deriv : Expr n F G → Expr n F (EuclideanSpace ℝ (Fin n) →L[ℝ] G)
  | .zero => .zero
  | .add a b => .add a.deriv b.deriv
  | .atom k φ hs hc A =>
    .add (sum (List.ofFn fun i : Fin n ↦
      .atom k (fun x ↦ fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
        ((hs.fderiv_right (by simp)).clm_apply contDiff_const)
        ((hc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦
          L (EuclideanSpace.basisFun (Fin n) ℝ i)) rfl)
        (((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n)) G)
          (EuclideanSpace.proj i)).comp A)))
      (.atom (k + 1) φ hs hc
        (((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin n))
          ((EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F) G) A).comp
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (k + 1) ↦ EuclideanSpace ℝ (Fin n)) F).toContinuousLinearEquiv.toContinuousLinearMap))

/-- One differentiation increases the input order by at most one
(`app:ch_regular:eq:one-gain-tame`). -/
theorem order_deriv_le (a : Expr n F G) : a.deriv.order ≤ a.order + 1 := by
  induction a with
  | zero => exact Nat.zero_le _
  | atom k φ hs hc A =>
    apply max_le _ le_rfl
    apply order_sum_le
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.le_succ k
  | add a b ha hb =>
    exact max_le (ha.trans (Nat.add_le_add_right (le_max_left _ _) 1))
      (hb.trans (Nat.add_le_add_right (le_max_right _ _) 1))

/-- The coordinate expansion used by `deriv` is exactly the differential of
the scalar coefficient (`app:ch_regular:eq:one-gain-tame`). -/
theorem eval_deriv_atom (k : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (A : ((EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F) →L[ℝ] G) (J) (x) :
    (atom k φ hs hc A).deriv.eval J x =
      (fderiv ℝ φ x).smulRight (A (J k x)) + φ x • A.comp
        ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) ↦ EuclideanSpace ℝ (Fin n)) F) (J (k + 1) x)) := by
  simp only [deriv, eval, eval_sum, List.map_ofFn, List.sum_ofFn,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
  congr 1
  ext v
  simp only [sum_apply, comp_apply, eval, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hv := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hd := congrArg (fderiv ℝ φ x) hv
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.coe_proj, smul_eq_mul, mul_comm] using hd

/-- Each explicit cutoff expression is L² when its input jet components are
L² (`app:ch_regular:eq:one-gain-tame`). -/
theorem memLp_eval (a : Expr n F G)
    (J : (k : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F)
    (hJ : ∀ k ≤ a.order, MemLp (J k) 2 volume) : MemLp (a.eval J) 2 volume := by
  induction a with
  | zero => exact MemLp.zero'
  | atom k φ hs hc A =>
    obtain ⟨B, hB⟩ := hs.continuous.bounded_above_of_compact_support hc
    exact memLp_bounded_smul (A.comp_memLp' (hJ k le_rfl)) hs.continuous hB
  | add a b ha hb =>
    exact (ha (fun k hk ↦ hJ k (hk.trans (le_max_left _ _)))).add
      (hb (fun k hk ↦ hJ k (hk.trans (le_max_right _ _))))

/-- Differentiating the finite expression gives its actual weak derivative,
using only the original weak-jet identities (`app:ch_regular:eq:one-gain-tame`). -/
theorem hasWeakFDerivOn_eval [CompleteSpace F] [CompleteSpace G]
    (a : Expr n F G) {f : EuclideanSpace ℝ (Fin n) → F}
    {J : (k : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F} {s : ℕ}
    (hw : Mollification.HasWeakJetOn volume f J univ s)
    (hJ : ∀ k ≤ s, MemLp (J k) 2 volume) (ha : a.order < s) :
    Mollification.HasWeakFDerivOn volume (a.eval J) (a.deriv.eval J) univ := by
  induction a with
  | zero =>
    convert Mollification.hasWeakFDerivOn_of_contDiff volume
      (contDiff_const : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin n) ↦ (0 : G))) univ using 1 <;> funext x <;> simp [eval, deriv]
  | add a b h₁ h₂ =>
    exact (h₁ ((le_max_left _ _).trans_lt ha)).add_univ
      (h₂ ((le_max_right _ _).trans_lt ha))
  | atom k φ hs hc A =>
    have hk : k < s := ha
    let L := continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k + 1) ↦ EuclideanSpace ℝ (Fin n)) F
    have hD : MemLp (L ∘ J (k + 1)) 2 volume :=
      (hJ (k + 1) hk).of_le_enorm
        (L.continuous.comp_aestronglyMeasurable (hJ (k + 1) hk).aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ (L.enorm_map _).le)
    obtain ⟨B₀, hB₀⟩ := hs.continuous.bounded_above_of_compact_support hc
    obtain ⟨B₁, hB₁⟩ := (hs.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (hc.fderiv ℝ)
    have h := ((hw.2 k hk).smooth_smul_univ (hJ k hk.le) hD hs hB₀ hB₁).comp_clm_univ A
    convert h using 1
    · ext x
      simp [eval]
    · ext x v
      rw [eval_deriv_atom]
      simp

/-- Each fixed expression has a constant chosen before the input jet, bounded
by the sum of its available L² jet norms (`app:ch_regular:eq:one-gain-tame`). -/
theorem exists_bound (a : Expr n F G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℕ)
      (J : (k : ℕ) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F),
      a.order ≤ s → (∀ k ≤ s, MemLp (J k) 2 volume) →
      (eLpNorm (a.eval J) 2 volume).toReal ≤
        C * ∑ k ∈ Finset.range (s + 1), (eLpNorm (J k) 2 volume).toReal := by
  induction a with
  | zero => exact ⟨0, le_rfl, fun s J _ _ ↦ by simp [eval]⟩
  | atom k φ hs hc A =>
    obtain ⟨B, hB⟩ := hs.continuous.bounded_above_of_compact_support hc
    have hB0 : 0 ≤ B := (norm_nonneg (φ 0)).trans (hB 0)
    refine ⟨B * ‖A‖, mul_nonneg hB0 (norm_nonneg A), fun s J hk hJ ↦ ?_⟩
    have hm := (atom k φ hs hc A).memLp_eval J (fun l hl ↦ hJ l (hl.trans hk))
    apply (eLpNorm_toReal_le_mul_of_bound hm.aestronglyMeasurable (hJ k hk)
      (mul_nonneg hB0 (norm_nonneg A)) (fun x ↦ ?_)).trans
    · exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun l ↦ (eLpNorm (J l) 2 volume).toReal)
          (fun l _ ↦ ENNReal.toReal_nonneg)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))) (mul_nonneg hB0 (norm_nonneg A))
    · dsimp [eval]
      rw [norm_smul, mul_assoc]
      exact mul_le_mul (hB x) (A.le_opNorm _) (norm_nonneg _) hB0
  | add a b ha hb =>
    obtain ⟨A, hA, hAb⟩ := ha
    obtain ⟨B, hB, hBb⟩ := hb
    refine ⟨A + B, add_nonneg hA hB, fun s J hab hJ ↦ ?_⟩
    have ha : a.order ≤ s := (le_max_left _ _).trans hab
    have hb : b.order ≤ s := (le_max_right _ _).trans hab
    have hma := a.memLp_eval J (fun k hk ↦ hJ k (hk.trans ha))
    have hmb := b.memLp_eval J (fun k hk ↦ hJ k (hk.trans hb))
    have hsum : (eLpNorm ((a.add b).eval J) 2 volume).toReal ≤
        (eLpNorm (a.eval J) 2 volume).toReal + (eLpNorm (b.eval J) 2 volume).toReal :=
      (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨hma.eLpNorm_ne_top, hmb.eLpNorm_ne_top⟩) (eLpNorm_add_le (by norm_num))).trans_eq
        (ENNReal.toReal_add hma.eLpNorm_ne_top hmb.eLpNorm_ne_top)
    exact hsum.trans (by simpa [add_mul] using add_le_add (hAb s J ha hJ) (hBb s J hb hJ))

end Expr
end JanetCartan.LocalSobolev.CutoffJet
