module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.Jets

/-!
# Weighted first-output jet budgets

Explicit primitive weighted bounds for the fixed one-derivative shift in the
order-minus-one gain of `app:ch_regular_base:thm:actual-calculus`, Step 3.
These bounds are consumed by the parent's order-zero operator estimate.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FirstOutputJets
open FullAmplitudePrimitiveBudget
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "M" => Matrix (Fin r) (Fin r) ℂ

/-- Number of physical covector derivatives in a joint word. Source: the symbol
orders in the gain-one paragraph of `app:ch_regular_base:thm:actual-calculus`. -/
def frequencyOrder (w : List (Coordinate n)) : ℕ := w.countP (fun c ↦ c.1 == .covector)

/-- The Leibniz split preserves the total number of physical covector derivatives.
Source: gain one in Step 3. -/
theorem frequencyOrder_split {w : List (Coordinate n)}
    {p : List (Coordinate n) × List (Coordinate n)} (hp : p ∈ splits w) :
    frequencyOrder p.1 + frequencyOrder p.2 = frequencyOrder w := by
  induction w generalizing p with
  | nil => simp only [splits, List.mem_singleton] at hp; subst p; rfl
  | cons c w ih =>
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hh := ih hq
    rcases hp with rfl | rfl <;>
      simp only [frequencyOrder, List.countP_cons] at * <;> split <;> omega

private theorem weighted_norm_sum_le (l : List M) (t C : ℝ) (ht : 0 ≤ t)
    (h : ∀ z ∈ l, t * ‖z‖ ≤ C) : t * ‖l.sum‖ ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hz := h z (by simp)
    have hl := ih (fun a ha ↦ h a (by simp [ha]))
    have hs := mul_le_mul_of_nonneg_left (norm_add_le z l.sum) ht
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Weighted finite product estimate. An order-one scalar times an order-minus-one
matrix has order zero, with the exact covector derivative count.
Source: the gain-one paragraph of Step 3. -/
theorem weighted_product_le (w : List (Coordinate n))
    (p : List (Coordinate n) × List (Coordinate n)) (hp : p ∈ splits w)
    (ρ a b : ℝ) (hρ : 0 < ρ) (hb : 0 ≤ b) (z : ℂ) (B : M)
    (hz : ρ ^ frequencyOrder p.1 * ‖z‖ ≤ b * ρ)
    (hB : ρ ^ frequencyOrder p.2 * ‖B‖ ≤ a / ρ) :
    ρ ^ frequencyOrder w * ‖z • B‖ ≤ b * a := by
  have hh := mul_le_mul hz hB (mul_nonneg (pow_nonneg hρ.le _) (norm_nonneg _))
    (mul_nonneg hb hρ.le)
  rw [← frequencyOrder_split hp, pow_add, norm_smul]
  calc
    _ = (ρ ^ frequencyOrder p.1 * ‖z‖) * (ρ ^ frequencyOrder p.2 * ‖B‖) := by ring
    _ ≤ (b * ρ) * (a / ρ) := hh
    _ = b * a := by field_simp

/-- Order-zero bound for the first output amplitude from primitive weighted jets
through one fixed extra derivative. Here `ρ` can be the usual Japanese bracket;
no frequency rescaling is made. The phase-gradient bound spends one phase
primitive derivative, so the largest primitive order is `|w|+1`.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem weighted_firstOutput_le
    (A : FullAmplitude n r) (f : Field n ℂ) (c : Coordinate n) (hc : c.1 ≠ .covector)
    (hA : SmoothAwayZero A) (hf : SmoothAwayZero f)
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0)
    (ρ a b : ℝ) (hρ : 1 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAj : ∀ v, v.length ≤ w.length + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ a / ρ)
    (hfj : ∀ v, v.length ≤ w.length →
      ρ ^ frequencyOrder v * ‖jet v f x y η‖ ≤ b * ρ) :
    ρ ^ frequencyOrder w * ‖jet w (derivative c A + multiply f A) x y η‖ ≤
      a + (2 : ℝ) ^ w.length * (b * a) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hd := hAj (w ++ [c]) (by simp)
  have hcount : frequencyOrder (w ++ [c]) = frequencyOrder w := by
    simp [frequencyOrder, List.countP_append, hc]
  rw [hcount] at hd
  have hd' : ρ ^ frequencyOrder w * ‖jet (w ++ [c]) A x y η‖ ≤ a :=
    hd.trans (div_le_self ha hρ)
  let l := (splits w).map (fun p ↦ jet p.1 f x y η • jet p.2 A x y η)
  have hs : ρ ^ frequencyOrder w * ‖l.sum‖ ≤ (2 : ℝ) ^ w.length * (b * a) := by
    have h := weighted_norm_sum_le l (ρ ^ frequencyOrder w) (b * a) (pow_nonneg hρ0.le _)
      (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
        have hh := lengths_split hp
        exact weighted_product_le w p hp ρ a b hρ0 hb _ _
          (hfj p.1 (by omega)) (hAj p.2 (by omega)))
    simpa only [l, List.length_map, length_splits, Nat.cast_pow, Nat.cast_ofNat] using h
  rw [jet_firstOutput A f c hA hf w x y η hη]
  have ht := mul_le_mul_of_nonneg_left
    (norm_add_le (jet (w ++ [c]) A x y η) l.sum) (pow_nonneg hρ0.le (frequencyOrder w))
  dsimp only [l] at hs ht
  nlinarith

/-- Concrete forward order-zero jet bound for the existing first output amplitude.
Only primitive matrix and phase-gradient jets enter the right side; no branch
operator norm or Sobolev estimate is a premise. The phase-gradient jets have
primitive order `|v|+1`. Source: gain one in Step 3. -/
theorem weighted_graphFirstOutputAmplitude_le
    (S : E → E → ℝ) (A : FullAmplitude n r) (i : Fin n)
    (hA : SmoothAwayZero A) (hS : SmoothAwayZero (phaseOutputCoefficient S i))
    (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0)
    (ρ a b : ℝ) (hρ : 1 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAj : ∀ v, v.length ≤ w.length + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ a / ρ)
    (hSj : ∀ v, v.length ≤ w.length →
      ρ ^ frequencyOrder v * ‖jet v (phaseOutputCoefficient S i) x y η‖ ≤ b * ρ) :
    ρ ^ frequencyOrder w * ‖jet w (graphFirstOutputAmplitude S A i) x y η‖ ≤
      a + (2 : ℝ) ^ w.length * (b * a) := by
  have he : graphFirstOutputAmplitude S A i =
      derivative (.left, i) A + multiply (phaseOutputCoefficient S i) A := by
    funext x y η
    simp only [graphFirstOutputAmplitude, derivative, phaseOutputCoefficient, multiply,
      slice, anchor, Pi.add_apply]
  rw [he]
  exact weighted_firstOutput_le A _ (.left, i) (by simp) hA hS w x y η hη
    ρ a b hρ ha hb hAj hSj

end JanetCartan.FourierIntegral.FirstOutputJets
