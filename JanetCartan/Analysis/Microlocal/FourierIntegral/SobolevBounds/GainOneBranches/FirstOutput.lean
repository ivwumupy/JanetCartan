module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches.Profiles

/-!
# Tame first-output jets before transfer

Expand the first-output amplitude before bounding products. This is the fixed
extra derivative in the gain-one paragraph following
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneBranches
open FullAmplitudePrimitiveBudget FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "M" => Matrix (Fin r) (Fin r) ℂ

/-- Finite matrix sums retain their exact multiplicity in the gain-one
Leibniz and branch expansions. Source: `app:ch_regular_base:thm:actual-calculus`, Step 3. -/
theorem weighted_matrix_sum_le (l : List M) (a D : ℝ) (ha : 0 ≤ a)
    (h : ∀ z ∈ l, a * ‖z‖ ≤ D) : a * ‖l.sum‖ ≤ l.length * D := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hz := h z (by simp)
    have hl := ih (fun b hb ↦ h b (by simp [hb]))
    have hs := mul_le_mul_of_nonneg_left (norm_add_le z l.sum) ha
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Tame jets of an actual first-output amplitude, with the product expanded
into original amplitude and order-one scalar jets. The scalar jet has primitive
order `|v|+1`, so every product uses at most `|w|+1` derivatives in total.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem firstOutput_jet_profile (μ t B : ℕ) (C H : ℝ) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (A : FullAmplitude n r) (f : Field n ℂ) (c : Coordinate n) (hc : c.1 ≠ .covector)
    (hA : SmoothAwayZero A) (hf : SmoothAwayZero f)
    (x y η : E) (hη : η ≠ 0) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hAj : ∀ v, v.length ≤ B + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ C * profile μ t H v.length / ρ)
    (hfj : ∀ v, v.length ≤ B →
      ρ ^ frequencyOrder v * ‖jet v f x y η‖ ≤ C * profile μ t H (v.length + 1) * ρ)
    (w : List (Coordinate n)) (hw : w.length ≤ B) :
    ρ ^ frequencyOrder w * ‖jet w (derivative c A + multiply f A) x y η‖ ≤
      ((1 + (2 : ℝ) ^ B) * C ^ 2) * profile μ t H (w.length + 1) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hcount : frequencyOrder (w ++ [c]) = frequencyOrder w := by
    simp [frequencyOrder, List.countP_append, hc]
  have hd := hAj (w ++ [c]) (by simpa using Nat.add_le_add_right hw 1)
  simp only [List.length_append, List.length_singleton, hcount] at hd
  have hCC : C ≤ C ^ 2 := by nlinarith
  have hd' : ρ ^ frequencyOrder w * ‖jet (w ++ [c]) A x y η‖ ≤
      C ^ 2 * profile μ t H (w.length + 1) :=
    hd.trans ((div_le_self (mul_nonneg hC0 (profile_nonneg _ _ _ hH)) hρ).trans
      (mul_le_mul_of_nonneg_right hCC (profile_nonneg _ _ _ hH)))
  let l := (splits w).map (fun p ↦ jet p.1 f x y η • jet p.2 A x y η)
  have hs : ρ ^ frequencyOrder w * ‖l.sum‖ ≤
      (2 : ℝ) ^ B * (C ^ 2 * profile μ t H (w.length + 1)) := by
    have hh := weighted_matrix_sum_le l (ρ ^ frequencyOrder w)
      (C ^ 2 * profile μ t H (w.length + 1)) (pow_nonneg hρ0.le _) (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
        have hlen := lengths_split hp
        have hp' := weighted_product_le w p hp ρ
          (C * profile μ t H p.2.length) (C * profile μ t H (p.1.length + 1))
          hρ0 (mul_nonneg hC0 (profile_nonneg _ _ _ hH)) _ _
          (hfj p.1 (by omega)) (hAj p.2 (by omega))
        apply hp'.trans
        calc
          _ = C ^ 2 * (profile μ t H (p.1.length + 1) * profile μ t H p.2.length) := by ring
          _ ≤ C ^ 2 * profile μ t H (p.1.length + 1 + p.2.length) :=
            mul_le_mul_of_nonneg_left (profile_mul_le _ _ _ _ hH) (sq_nonneg C)
          _ = _ := by congr 2; omega)
    simp only [l, List.length_map, length_splits, Nat.cast_pow, Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw)
      (mul_nonneg (sq_nonneg C) (profile_nonneg _ _ _ hH)))
  rw [jet_firstOutput A f c hA hf w x y η hη]
  have ht := mul_le_mul_of_nonneg_left
    (norm_add_le (jet (w ++ [c]) A x y η) l.sum) (pow_nonneg hρ0.le (frequencyOrder w))
  dsimp only [l] at hs ht
  nlinarith

/-- Forward first-output jets with a single high profile of the original
amplitude and phase. Order minus one cancels order one at the physical frequency.
Source: `app:ch_regular_base:thm:actual-calculus`, gain-one paragraph. -/
theorem graphFirstOutput_jet_profile (μ t B : ℕ) (C H : ℝ) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (S : E → E → ℝ) (A : FullAmplitude n r) (i : Fin n)
    (hA : SmoothAwayZero A)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (x y η : E) (hη : η ≠ 0) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hAj : ∀ v, v.length ≤ B + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ C * profile μ t H v.length / ρ)
    (hSj : ∀ v, v.length ≤ B + 1 →
      ρ ^ frequencyOrder v * ‖jet v (phasePrimitive S) x y η‖ ≤
        C * profile μ t H v.length * ρ)
    (w : List (Coordinate n)) (hw : w.length ≤ B) :
    ρ ^ frequencyOrder w * ‖jet w (graphFirstOutputAmplitude S A i) x y η‖ ≤
      ((1 + (2 : ℝ) ^ B) * C ^ 2) * profile μ t H (w.length + 1) := by
  have he : graphFirstOutputAmplitude S A i =
      derivative (.left, i) A + multiply (phaseOutputCoefficient S i) A := by
    rfl
  rw [he]
  apply firstOutput_jet_profile μ t B C H hC hH A _ (.left, i) (by simp) hA
    (smooth_phaseOutputCoefficient S hS i) x y η hη ρ hρ hAj ?_ w hw
  intro v hv
  rw [jet_phaseOutputCoefficient S hS i v x y η hη]
  have hv' := hSj (v ++ [(.left, i)]) (by simpa using Nat.add_le_add_right hv 1)
  have hcount : frequencyOrder (v ++ [(.left, i)]) = frequencyOrder v := by
    simp [frequencyOrder, List.countP_append]
  rw [hcount, List.length_append, List.length_singleton] at hv'
  exact hv'

/-- The literal adjoint uses the original amplitude jets, conjugate-transposed
once, and its actual physical covector. Source: gain one and
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjointFirstOutput_jet_profile (μ t B : ℕ) (C H : ℝ) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (A : FullAmplitude n r) (i : Fin n) (hA : SmoothAwayZero A)
    (x y η : E) (hη : η ≠ 0) (ρ : ℝ) (hρ : 1 ≤ ρ) (hηρ : ‖η‖ ≤ ρ)
    (hAj : ∀ v, v.length ≤ B + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ C * profile μ t H v.length / ρ)
    (w : List (Coordinate n)) (hw : w.length ≤ B) :
    ρ ^ frequencyOrder w * ‖jet w (adjointFirstOutputAmplitude A i) x y η‖ ≤
      ((1 + (2 : ℝ) ^ B) * C ^ 2) * profile μ t H (w.length + 1) := by
  have he : adjointFirstOutputAmplitude A i =
      derivative (.right, i) (fun x y η ↦ (A x y η).conjTranspose) +
        multiply (covectorOutputCoefficient i) (fun x y η ↦ (A x y η).conjTranspose) := by
    rfl
  rw [he]
  apply firstOutput_jet_profile μ t B C H hC hH _ _ (.right, i) (by simp)
    hA.conjTranspose (smooth_covectorOutputCoefficient i) x y η hη ρ hρ ?_ ?_ w hw
  · intro v hv
    simpa only [norm_jet_conjTranspose] using hAj v hv
  · intro v _
    apply (weighted_covectorOutputCoefficient_le i v x y η ρ hρ hηρ).trans
    have hp : 1 ≤ profile μ t H (v.length + 1) := by
      exact Real.one_le_rpow hH (by positivity)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_mul_of_one_le_of_one_le hC hp) (zero_le_one.trans hρ)

end JanetCartan.FourierIntegral.GainOneBranches
