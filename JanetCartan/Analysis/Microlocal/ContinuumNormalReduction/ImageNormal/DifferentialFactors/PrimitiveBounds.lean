module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.PhysicalBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Primitive budgets for the differential remainder

Explicit finite physical derivative bounds for the image-normal paragraph of
`app:ch_background:prop:bg-frame`, Step 1. The consumer is the quantitative
remainder theorem in `DifferentialFactors`. Only the original coefficient and
cutoff jets are inputs; the source-product and affine coefficient budgets are
computed below. The measurement support gives the global estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.Pseudodifferential

private structure JetBudget {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : ℕ) (f : D → F) (x : D) (B : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  nonneg : 0 ≤ B
  bound : ∀ n ≤ N, ‖iteratedFDeriv ℝ n f x‖ ≤ B

private theorem JetBudget.mono {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ℕ} {f : D → F} {x : D} {B C : ℝ} (h : JetBudget N f x B) (hBC : B ≤ C) :
    JetBudget N f x C := ⟨h.smooth, h.nonneg.trans hBC, fun n hn ↦ (h.bound n hn).trans hBC⟩

private theorem JetBudget.mul {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedRing F] [NormedAlgebra ℝ F]
    {N : ℕ} {f g : D → F} {x : D} {B C : ℝ}
    (hf : JetBudget N f x B) (hg : JetBudget N g x C) :
    JetBudget N (fun y ↦ f y * g y) x ((2 : ℝ)^N * B * C) := by
  refine ⟨hf.smooth.mul hg.smooth, mul_nonneg (mul_nonneg (by positivity) hf.nonneg) hg.nonneg, ?_⟩
  intro n hn
  apply (norm_iteratedFDeriv_mul_le hf.smooth hg.smooth x (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hf.bound i hiN) (by positivity))
        (hg.bound (n-i) ((Nat.sub_le _ _).trans hn)) (norm_nonneg _)
        (mul_nonneg (by positivity) hf.nonneg)
    _ = (2 : ℝ)^n * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn)
        hf.nonneg) hg.nonneg

private theorem JetBudget.add {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ℕ} {f g : D → F} {x : D} {B C : ℝ}
    (hf : JetBudget N f x B) (hg : JetBudget N g x C) :
    JetBudget N (fun y ↦ f y + g y) x (B+C) := by
  refine ⟨hf.smooth.add hg.smooth, add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro n hn
  rw [fun_iteratedFDeriv_add_apply (hf.smooth.contDiffAt.of_le (by simp))
    (hg.smooth.contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound n hn) (hg.bound n hn))

private theorem JetBudget.sub {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ℕ} {f g : D → F} {x : D} {B C : ℝ}
    (hf : JetBudget N f x B) (hg : JetBudget N g x C) :
    JetBudget N (fun y ↦ f y - g y) x (B+C) := by
  refine ⟨hf.smooth.sub hg.smooth, add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro n hn
  rw [fun_iteratedFDeriv_sub_apply (hf.smooth.contDiffAt.of_le (by simp))
    (hg.smooth.contDiffAt.of_le (by simp))]
  exact (norm_sub_le _ _).trans (add_le_add (hf.bound n hn) (hg.bound n hn))

private theorem JetBudget.sum {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N d : ℕ} {f : Fin d → D → F} {x : D} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ j, JetBudget N (f j) x B) :
    JetBudget N (fun y ↦ ∑ j, f j y) x (d * B) := by
  refine ⟨ContDiff.sum (fun j _ ↦ (hf j).smooth), mul_nonneg (by positivity) hB, ?_⟩
  intro n hn
  rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hf j).smooth.contDiffAt.of_le (by simp))]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ ↦ (hf j).bound n hn)).trans_eq
    (by simp))

private theorem JetBudget.precomp {D F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {N : ℕ} {f : D → F} {L : G →L[ℝ] D} {x : G} {B : ℝ}
    (hf : JetBudget N f (L x) B) (hL : ‖L‖ ≤ 1) :
    JetBudget N (f ∘ L) x B := by
  refine ⟨hf.smooth.comp L.contDiff, hf.nonneg, ?_⟩
  intro n hn
  rw [L.iteratedFDeriv_comp_right hf.smooth x (by simp)]
  apply ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ B * (1 : ℝ)^n := mul_le_mul (hf.bound n hn)
      (pow_le_pow_left₀ (norm_nonneg _) hL _) (by positivity) hf.nonneg
    _ = B := by simp

private theorem JetBudget.ofReal {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {N : ℕ} {f : D → ℝ} {x : D} {B : ℝ} (hf : JetBudget N f x B) :
    JetBudget N (fun y ↦ (f y : ℂ)) x B := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hf.smooth, hf.nonneg, ?_⟩
  intro n hn
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ f) x‖ ≤ B
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.smooth.contDiffAt (by simp)]
  exact hf.bound n hn

private theorem JetBudget.imul {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {N : ℕ} {f : D → ℂ} {x : D} {B : ℝ} (hf : JetBudget N f x B) :
    JetBudget N (fun y ↦ Complex.I * f y) x B := by
  refine ⟨contDiff_const.mul hf.smooth, hf.nonneg, ?_⟩
  intro n hn
  change ‖iteratedFDeriv ℝ n (fun y ↦ Complex.I • f y) x‖ ≤ B
  rw [iteratedFDeriv_const_smul_apply' (hf.smooth.contDiffAt.of_le (by simp)),
    norm_smul, Complex.norm_I, one_mul]
  exact hf.bound n hn

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-- Budget for `C = χ²` through order `N+1`, including the derivative used in
`Q = A dC + ZC` (`app:ch_background:prop:bg-frame`, Step 1). -/
def differentialCutoffBudget (N : ℕ) (Bχ : ℝ) : ℝ := (2 : ℝ)^(N+1) * Bχ * Bχ

/-- Computed budget for `Q = A dC + ZC`, from the primitive entry budgets
(`app:ch_background:prop:bg-frame`, Step 1). -/
def differentialSourceBudget (d N : ℕ) (BA BZ Bχ : ℝ) : ℝ :=
  d * ((2 : ℝ)^N * BA * differentialCutoffBudget N Bχ) +
    (2 : ℝ)^N * BZ * differentialCutoffBudget N Bχ

/-- Computed uniform budget for every affine remainder coefficient
(`app:ch_background:prop:bg-frame`, Step 1). -/
def differentialAffineBudget (d N : ℕ) (BA BZ Bμ Bχ : ℝ) : ℝ :=
  let T := (2 : ℝ)^N
  let BC := differentialCutoffBudget N Bχ
  let BQ := differentialSourceBudget d N BA BZ Bχ
  T * (T * Bμ * Bμ) *
    (d * (T * BQ * BZ) + d * (T * (T * BC * BA) * BZ + T * BQ * BA))

private theorem cutoff_budget {N : ℕ} {χ : E → ℝ} {x : E} {Bχ : ℝ}
    (hχ : JetBudget (N+1) χ x Bχ) :
    JetBudget (N+1) (fun y ↦ χ y ^ 2) x (differentialCutoffBudget N Bχ) := by
  simpa only [pow_two, differentialCutoffBudget] using hχ.mul hχ

private theorem cutoff_partial_budget {N : ℕ} {χ : E → ℝ} {x : E} {Bχ : ℝ}
    (hχ : JetBudget (N+1) χ x Bχ) (a : Fin d) :
    JetBudget N (fun y ↦ partialDeriv (fun z ↦ χ z ^ 2) y a) x
      (differentialCutoffBudget N Bχ) := by
  have hc := cutoff_budget hχ
  refine ⟨(hc.smooth.fderiv_right (by simp)).clm_apply contDiff_const, hc.nonneg, ?_⟩
  intro n hn
  have hd := norm_iteratedFDeriv_clm_apply_const
    ((hc.smooth.fderiv_right (by simp)).contDiffAt)
    (show (n : ℕ∞ω) ≤ ∞ by simp) (c := EuclideanSpace.single a 1) (x := x)
  rw [norm_iteratedFDeriv_fderiv] at hd
  simpa [partialDeriv] using hd.trans
    (mul_le_mul_of_nonneg_left (hc.bound (n+1) (by omega)) (norm_nonneg _))

/-- Quantitative source-product jets are derived from `A`, `Z`, and `χ`,
including all derivatives falling on `χ²`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_iteratedFDeriv_sourceProductCoefficient_le_primitive
    (A : E → Fin d → Mat) (Z : E → Mat) (χ : E → ℝ) (N : ℕ)
    (BA BZ Bχ : ℝ) (hBA : 0 ≤ BA) (hBZ : 0 ≤ BZ) (hBχ : 0 ≤ Bχ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (hχ : ContDiff ℝ ∞ χ)
    (x : E)
    (bA : ∀ a i j n, n ≤ N → ‖iteratedFDeriv ℝ n (fun y ↦ A y a i j) x‖ ≤ BA)
    (bZ : ∀ i j n, n ≤ N → ‖iteratedFDeriv ℝ n (fun y ↦ Z y i j) x‖ ≤ BZ)
    (bχ : ∀ n ≤ N+1, ‖iteratedFDeriv ℝ n χ x‖ ≤ Bχ)
    (i j : Fin d) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y ↦ sourceProductCoefficient A Z (fun z ↦ χ z^2) y i j) x‖ ≤
      differentialSourceBudget d N BA BZ Bχ := by
  have hc := cutoff_budget (JetBudget.mk hχ hBχ bχ)
  have hcN : JetBudget N (fun z ↦ χ z^2) x (differentialCutoffBudget N Bχ) :=
    ⟨hc.smooth, hc.nonneg, fun k hk ↦ hc.bound k (by omega)⟩
  have ha a : JetBudget N (fun y ↦ A y a i j) x BA := ⟨hA a i j, hBA, bA a i j⟩
  have hz : JetBudget N (fun y ↦ Z y i j) x BZ := ⟨hZ i j, hBZ, bZ i j⟩
  exact ((JetBudget.sum (mul_nonneg (mul_nonneg (by positivity) hBA) hc.nonneg) (fun a ↦
    (ha a).mul (cutoff_partial_budget ⟨hχ, hBχ, bχ⟩ a))).add (hz.mul hcN)).bound n hn


/-- The explicit affine budget is nonnegative for nonnegative primitive budgets
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem differentialAffineBudget_nonneg (d N : ℕ) (BA BZ Bμ Bχ : ℝ)
    (hBA : 0 ≤ BA) (hBZ : 0 ≤ BZ) (hBμ : 0 ≤ Bμ) (hBχ : 0 ≤ Bχ) :
    0 ≤ differentialAffineBudget d N BA BZ Bμ Bχ := by
  unfold differentialAffineBudget differentialSourceBudget differentialCutoffBudget
  positivity

private theorem affine_entry_budget
    (A : E → Fin d → Mat) (Z : E → Mat) (χ μ : E → ℝ) (N : ℕ)
    (BA BZ Bμ Bχ : ℝ) (hBA : 0 ≤ BA) (hBZ : 0 ≤ BZ) (hBμ : 0 ≤ Bμ) (hBχ : 0 ≤ Bχ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ) (p : E × E)
    (bA : ∀ x ∈ ({p.1, p.2} : Set E), ∀ a i j n, n ≤ N →
      ‖iteratedFDeriv ℝ n (fun y ↦ A y a i j) x‖ ≤ BA)
    (bZ : ∀ x ∈ ({p.1, p.2} : Set E), ∀ i j n, n ≤ N →
      ‖iteratedFDeriv ℝ n (fun y ↦ Z y i j) x‖ ≤ BZ)
    (bμ : ∀ x ∈ ({p.1, p.2} : Set E), ∀ n ≤ N, ‖iteratedFDeriv ℝ n μ x‖ ≤ Bμ)
    (bχ : ∀ n ≤ N+1, ‖iteratedFDeriv ℝ n χ p.1‖ ≤ Bχ) (i l : Fin d)
    (a : Option (Fin d)) :
    JetBudget N (fun q ↦ differentialRemainderCoefficients A Z (fun x ↦ χ x^2) μ i l q a)
      p (differentialAffineBudget d N BA BZ Bμ Bχ) := by
  let T := (2 : ℝ)^N
  let BC := differentialCutoffBudget N Bχ
  let BQ := differentialSourceBudget d N BA BZ Bχ
  have hT : 0 ≤ T := by positivity
  have hBC : 0 ≤ BC := by dsimp [BC, differentialCutoffBudget]; positivity
  have hBQ : 0 ≤ BQ := by dsimp [BQ, differentialSourceBudget, differentialCutoffBudget]; positivity
  have hcx := cutoff_budget (JetBudget.mk hχ hBχ bχ)
  have hc : JetBudget N (fun q : E × E ↦ χ q.1 ^ 2) p BC :=
    (show JetBudget N (fun x ↦ χ x^2) p.1 BC from
      ⟨hcx.smooth, hcx.nonneg, fun k hk ↦ hcx.bound k (by omega)⟩).precomp
        (ContinuousLinearMap.norm_fst_le ℝ E E)
  have hax a i j : JetBudget N (fun q : E × E ↦ A q.1 a i j) p BA :=
    (show JetBudget N (fun x ↦ A x a i j) p.1 BA from
      ⟨hA a i j, hBA, bA p.1 (by simp) a i j⟩).precomp (ContinuousLinearMap.norm_fst_le ℝ E E)
  have hay a i j : JetBudget N (fun q : E × E ↦ A q.2 a i j) p BA :=
    (show JetBudget N (fun x ↦ A x a i j) p.2 BA from
      ⟨hA a i j, hBA, bA p.2 (by simp) a i j⟩).precomp (ContinuousLinearMap.norm_snd_le ℝ E E)
  have hzy i j : JetBudget N (fun q : E × E ↦ Z q.2 i j) p BZ :=
    (show JetBudget N (fun x ↦ Z x i j) p.2 BZ from
      ⟨hZ i j, hBZ, bZ p.2 (by simp) i j⟩).precomp (ContinuousLinearMap.norm_snd_le ℝ E E)
  have hmx : JetBudget N (fun q : E × E ↦ μ q.1) p Bμ :=
    (JetBudget.mk hμ hBμ (bμ p.1 (by simp))).precomp (ContinuousLinearMap.norm_fst_le ℝ E E)
  have hmy : JetBudget N (fun q : E × E ↦ μ q.2) p Bμ :=
    (JetBudget.mk hμ hBμ (bμ p.2 (by simp))).precomp (ContinuousLinearMap.norm_snd_le ℝ E E)
  have hq j : JetBudget N
      (fun q : E × E ↦ sourceProductCoefficient A Z (fun x ↦ χ x^2) q.1 i j) p BQ :=
    (show JetBudget N (fun x ↦ sourceProductCoefficient A Z (fun y ↦ χ y^2) x i j) p.1 BQ from
      ⟨contDiff_sourceProductCoefficient A Z _ hA hZ hcx.smooth i j, hBQ,
        norm_iteratedFDeriv_sourceProductCoefficient_le_primitive A Z χ N BA BZ Bχ
          hBA hBZ hBχ hA hZ hχ p.1 (bA p.1 (by simp)) (bZ p.1 (by simp)) bχ i j⟩).precomp
            (ContinuousLinearMap.norm_fst_le ℝ E E)
  have hfirst : 0 ≤ (d : ℝ) * (T * BQ * BZ) := by positivity
  have hsecond : 0 ≤ (d : ℝ) * (T * (T * BC * BA) * BZ + T * BQ * BA) := by positivity
  cases a with
  | none =>
    have h := (hmx.mul hmy).ofReal.mul
      (JetBudget.sum (by positivity : 0 ≤ T * BQ * BZ)
        (fun j ↦ (hq j).ofReal.mul (hzy l j).ofReal))
    exact h.mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsecond) (by positivity))
  | some a =>
    have h := (hmx.mul hmy).ofReal.mul
      (JetBudget.sum (by positivity : 0 ≤ T * (T * BC * BA) * BZ + T * BQ * BA)
        (fun j ↦ ((((hc.mul (hax a i j)).mul (hzy l j)).ofReal).sub
          ((hq j).ofReal.mul (hay a l j).ofReal)).imul))
    exact h.mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hfirst) (by positivity))

private theorem norm_iteratedFDeriv_pi_le {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {ι : Type*} [Fintype ι] {f : D → ι → ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : D) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (fun y ↦ f y a) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)))).mpr
  intro a
  have heq := congrArg (fun L ↦ L v)
    ((ContinuousLinearMap.proj a : (ι → ℂ) →L[ℝ] ℂ).iteratedFDeriv_comp_left
      (x := x) hf.contDiffAt (show (n : ℕ∞ω) ≤ ∞ by simp))
  change iteratedFDeriv ℝ n (fun y ↦ f y a) x v =
    (iteratedFDeriv ℝ n f x v) a at heq
  rw [← heq]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hb a) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)))

/-- The actual affine coefficient jets have an explicit global budget from
primitive bounds on a fixed compact chart. Outside that chart the measurement
masks, and hence every remainder jet, vanish
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_iteratedFDeriv_differentialRemainderCoefficients_le_primitive
    (A : E → Fin d → Mat) (Z : E → Mat) (χ μ : E → ℝ) (K : Set E)
    (hK : IsCompact K) (hμK : tsupport μ ⊆ K) (N : ℕ)
    (BA BZ Bμ Bχ : ℝ) (hBA : 0 ≤ BA) (hBZ : 0 ≤ BZ) (hBμ : 0 ≤ Bμ) (hBχ : 0 ≤ Bχ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (bA : ∀ x ∈ K, ∀ a i j n, n ≤ N → ‖iteratedFDeriv ℝ n (fun y ↦ A y a i j) x‖ ≤ BA)
    (bZ : ∀ x ∈ K, ∀ i j n, n ≤ N → ‖iteratedFDeriv ℝ n (fun y ↦ Z y i j) x‖ ≤ BZ)
    (bμ : ∀ x ∈ K, ∀ n ≤ N, ‖iteratedFDeriv ℝ n μ x‖ ≤ Bμ)
    (bχ : ∀ x ∈ K, ∀ n ≤ N+1, ‖iteratedFDeriv ℝ n χ x‖ ≤ Bχ)
    (i l : Fin d) (n : ℕ) (hn : n ≤ N) (p : E × E) :
    ‖iteratedFDeriv ℝ n (differentialRemainderCoefficients A Z (fun x ↦ χ x^2) μ i l) p‖ ≤
      differentialAffineBudget d N BA BZ Bμ Bχ := by
  have hB := differentialAffineBudget_nonneg d N BA BZ Bμ Bχ hBA hBZ hBμ hBχ
  have hs := contDiff_differentialRemainderCoefficients A Z (fun x ↦ χ x^2) μ
    hA hZ (hχ.pow 2) hμ i l
  by_cases hp : p ∈ K ×ˢ K
  · have hpair : ∀ x ∈ ({p.1, p.2} : Set E), x ∈ K := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hp.1
      · exact hp.2
    apply norm_iteratedFDeriv_pi_le hs n p hB
    intro a
    exact (affine_entry_budget A Z χ μ N BA BZ Bμ Bχ hBA hBZ hBμ hBχ hA hZ hχ hμ p
      (fun x hx ↦ bA x (hpair x hx)) (fun x hx ↦ bZ x (hpair x hx))
      (fun x hx ↦ bμ x (hpair x hx)) (bχ p.1 hp.1) i l a).bound n hn
  · have hsupport : tsupport (differentialRemainderCoefficients A Z (fun x ↦ χ x^2) μ i l) ⊆
        K ×ˢ K := by
      apply closure_minimal _ (hK.isClosed.prod hK.isClosed)
      intro q hq
      by_contra hqK
      have hz : μ q.1 * μ q.2 = 0 := by
        by_cases hx : q.1 ∈ tsupport μ
        · have hy : q.2 ∉ tsupport μ := fun hy ↦ hqK ⟨hμK hx, hμK hy⟩
          simp [image_eq_zero_of_notMem_tsupport hy]
        · simp [image_eq_zero_of_notMem_tsupport hx]
      apply hq
      funext a
      cases a <;> simp [differentialRemainderCoefficients, hz]
    have hz : iteratedFDeriv ℝ n (differentialRemainderCoefficients A Z (fun x ↦ χ x^2) μ i l) p = 0 := by
      by_contra hne
      exact hp (hsupport (support_iteratedFDeriv_subset n hne))
    simpa only [hz, norm_zero] using hB

/-- Quantitative order-minus-one bound for every physical jet of the actual
remainder, uniform through order `N`. The displayed constant uses only `d`, `N`,
and the four primitive entrywise budgets on `K`; no compactness-selected bound
or assumed remainder estimate enters the result
(`app:ch_background:prop:bg-frame`, Step 1, image-normal paragraph). -/
theorem norm_iteratedFDeriv_differentialRemainderAmplitude_le_primitive
    (A : E → Fin d → Mat) (Z : E → Mat) (χ μ : E → ℝ) (K : Set E)
    (hK : IsCompact K) (hμK : tsupport μ ⊆ K) (N : ℕ)
    (BA BZ Bμ Bχ : ℝ) (hBA : 0 ≤ BA) (hBZ : 0 ≤ BZ) (hBμ : 0 ≤ Bμ) (hBχ : 0 ≤ Bχ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (bA : ∀ x ∈ K, ∀ a i j n, n ≤ N → ‖iteratedFDeriv ℝ n (fun y ↦ A y a i j) x‖ ≤ BA)
    (bZ : ∀ x ∈ K, ∀ i j n, n ≤ N → ‖iteratedFDeriv ℝ n (fun y ↦ Z y i j) x‖ ≤ BZ)
    (bμ : ∀ x ∈ K, ∀ n ≤ N, ‖iteratedFDeriv ℝ n μ x‖ ≤ Bμ)
    (bχ : ∀ x ∈ K, ∀ n ≤ N+1, ‖iteratedFDeriv ℝ n χ x‖ ≤ Bχ)
    (i l : Fin d) (n : ℕ) (hn : n ≤ N) (ξ : E) (p : E × E) :
    ‖iteratedFDeriv ℝ n
      (fun q : E × E ↦ differentialRemainderAmplitude A Z (fun x ↦ χ x^2) μ q.1 q.2 ξ i l) p‖ ≤
      ((d + 1) * differentialAffineBudget d N BA BZ Bμ Bχ) * imageBesselSymbol ξ := by
  have hs := contDiff_differentialRemainderCoefficients A Z (fun x ↦ χ x^2) μ
    hA hZ (hχ.pow 2) hμ i l
  have hb := norm_iteratedFDeriv_differentialRemainderCoefficients_le_primitive
    A Z χ μ K hK hμK N BA BZ Bμ Bχ hBA hBZ hBμ hBχ hA hZ hχ hμ bA bZ bμ bχ i l n hn p
  rw [differentialRemainderAmplitude_eq_contraction]
  apply ((differentialRemainderContraction ξ).norm_iteratedFDeriv_comp_left
    hs.contDiffAt (by simp)).trans
  have hw : 0 ≤ imageBesselSymbol ξ := by
    unfold imageBesselSymbol euclideanSobolevWeight
    positivity
  exact (mul_le_mul (norm_differentialRemainderContraction_le ξ) hb
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

end JanetCartan.ContinuumNormalReduction.ImageNormal
