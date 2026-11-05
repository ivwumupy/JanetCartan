module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches.FirstOutput

/-!
# The shared gain-one budget through all transfer branches

The first-output jet estimate is propagated through the existing exact local
branch expansions. Source: the gain-one paragraph after
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneBranches
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open FullAmplitudePrimitiveBudget.Local.Weighted FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- A uniform branch constant chosen before the high bound and all primitive
fields. Here `t = s-1`; the low baseline is enlarged only to `μ₀+1`.
Source: `app:ch_regular_base:thm:actual-calculus`, gain-one paragraph. -/
def branchConstant (n μ₀ t : ℕ) (C : ℝ) : ℝ :=
  (branchTermCount n t * (t + 1) ^ μ₀ : ℕ) *
    ((1 + (2 : ℝ) ^ (μ₀ + t)) * C ^ (t + 2))

/-- Nonnegativity of the fixed gain-one branch constant (`app:ch_regular_base:thm:actual-calculus`, Step 3). -/
theorem branchConstant_nonneg (n μ₀ t : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ branchConstant n μ₀ t C := by
  unfold branchConstant
  positivity

/-- Every scalar multiplication shares the initial extra derivative budget.
The seed estimate is produced by `graphFirstOutput_jet_profile` or
`adjointFirstOutput_jet_profile`, not an assumption in the carrier theorems.
Source: `app:ch_regular_base:eq:joint-primitive-product`, gain-one paragraph. -/
theorem term_firstOutput_profile (μ t B : ℕ) (C H : ℝ) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (S : E → E → ℝ) (F : FullAmplitude n r) (x y η : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hF : ∀ w, w.length ≤ B →
      ρ ^ frequencyOrder w * ‖jet w F x y η‖ ≤
        ((1 + (2 : ℝ) ^ B) * C ^ 2) * profile μ t H (w.length + 1))
    (hS : ∀ a w, w.length ≤ B →
      ρ ^ frequencyOrder w * ‖jet w (scalarPrimitive S a) x y η‖ ≤
        C * profile μ t H w.length)
    (u : Term n) (hu : u.order ≤ B) :
    ρ ^ u.frequencyOrder * ‖u.value S F x y η‖ ≤
      ((1 + (2 : ℝ) ^ B) * C ^ (u.orders.length + 1)) * profile μ t H (u.order + 1) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  induction u with
  | amplitude w => simpa [Term.value, Term.frequencyOrder, Term.orders, Term.order] using hF w hu
  | factor a w u ih =>
    have horder : w.length + u.order ≤ B := hu
    have hi := ih (by omega)
    have hs := hS a w (by omega)
    simp only [Term.value, multiply, Term.frequencyOrder, pow_add, norm_smul,
      Term.orders, List.length_cons, Term.order]
    calc
      _ = (ρ ^ frequencyOrder w * ‖jet w (scalarPrimitive S a) x y η‖) *
          (ρ ^ u.frequencyOrder * ‖u.value S F x y η‖) := by ring
      _ ≤ (C * profile μ t H w.length) *
          (((1 + (2 : ℝ) ^ B) * C ^ (u.orders.length + 1)) * profile μ t H (u.order + 1)) :=
        mul_le_mul hs hi (by positivity) (mul_nonneg hC0 (profile_nonneg _ _ _ hH))
      _ = ((1 + (2 : ℝ) ^ B) * C ^ (u.orders.length + 1 + 1)) *
          (profile μ t H w.length * profile μ t H (u.order + 1)) := by rw [pow_succ]; ring
      _ ≤ ((1 + (2 : ℝ) ^ B) * C ^ (u.orders.length + 1 + 1)) *
          profile μ t H (w.length + (u.order + 1)) :=
        mul_le_mul_of_nonneg_left (profile_mul_le _ _ _ _ hH) (by positivity)
      _ = _ := by simp only [pow_add, pow_one, Nat.add_assoc, mul_assoc]

private theorem sum_fields_apply (l : List (FullAmplitude n r)) (x y η : E) :
    l.sum x y η = (l.map (fun f ↦ f x y η)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simpa only [List.sum_cons, List.map_cons, Pi.add_apply] using congrArg (f x y η + ·) ih

/-- A local transfer expansion with a first-output seed obeys the gain-one
exponent. This is used with the proved concrete forward and reverse expansions;
its seed premise is discharged by the exact primitive Leibniz bounds.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem expansion_firstOutput_profile (μ₀ t k : ℕ) (C H : ℝ) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (S : E → E → ℝ) (F G : FullAmplitude n r) (U : Set (Point n))
    (hU : IsOpen U) (h : SmoothPrimitivesOn S F U)
    (he : WeightedExpansionOn S F G U (t - k) (branchTermCount n t) (t + 1) 0)
    (x y η : E) (hp : ((x, y), η) ∈ U) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hF : ∀ v, v.length ≤ μ₀ + t →
      ρ ^ frequencyOrder v * ‖jet v F x y η‖ ≤
        ((1 + (2 : ℝ) ^ (μ₀ + t)) * C ^ 2) * profile (μ₀ + 1) t H (v.length + 1))
    (hS : ∀ a v, v.length ≤ μ₀ + t →
      ρ ^ frequencyOrder v * ‖jet v (scalarPrimitive S a) x y η‖ ≤
        C * profile (μ₀ + 1) t H v.length)
    (w : List (Coordinate n)) (hw : w.length ≤ μ₀) :
    ρ ^ frequencyOrder w * ‖jet w G x y η‖ ≤
      branchConstant n μ₀ t C * H ^ (((t - k : ℕ) : ℝ) / t) := by
  obtain ⟨ts, heq, hlen, ht⟩ := he.jet hU h w
  have hN : ts.length ≤ branchTermCount n t * (t + 1) ^ μ₀ :=
    hlen.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hw))
  have hb : ∀ u ∈ ts, ρ ^ frequencyOrder w * ‖u.value S F x y η‖ ≤
      ((1 + (2 : ℝ) ^ (μ₀ + t)) * C ^ (t + 2)) * H ^ (((t - k : ℕ) : ℝ) / t) := by
    intro u hu
    obtain ⟨horder, hfactors, hfreq⟩ := ht u hu
    have hord : u.order ≤ μ₀ + t := by omega
    rw [← Nat.zero_add (frequencyOrder w), ← hfreq]
    apply (term_firstOutput_profile (μ₀ + 1) t (μ₀ + t) C H hC hH
      S F x y η ρ hρ hF hS u hord).trans
    have hpower : C ^ (u.orders.length + 1) ≤ C ^ (t + 2) :=
      pow_le_pow_right₀ hC (by omega)
    have hprof : profile (μ₀ + 1) t H (u.order + 1) ≤ H ^ (((t - k : ℕ) : ℝ) / t) := by
      unfold profile
      apply Real.rpow_le_rpow_of_exponent_le hH
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg t)
      exact_mod_cast (show u.order + 1 - (μ₀ + 1) ≤ t - k by omega)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpower (by positivity)) hprof
      (profile_nonneg _ _ _ hH) (by positivity)
  change ρ ^ frequencyOrder w * ‖uncurry (jet w G) ((x, y), η)‖ ≤ _
  rw [heq hp]
  change ρ ^ frequencyOrder w * ‖(ts.map (Term.value S F)).sum x y η‖ ≤ _
  rw [sum_fields_apply, List.map_map]
  have hs := weighted_matrix_sum_le (ts.map (fun u ↦ u.value S F x y η))
    (ρ ^ frequencyOrder w) _ (pow_nonneg hρ _) (by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      exact hb u hu)
  simp only [List.length_map] at hs
  apply hs.trans
  unfold branchConstant
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (show (ts.length : ℝ) ≤ (branchTermCount n t * (t + 1) ^ μ₀ : ℕ) by exact_mod_cast hN)
    (show 0 ≤ ((1 + (2 : ℝ) ^ (μ₀ + t)) * C ^ (t + 2)) *
      H ^ (((t - k : ℕ) : ℝ) / t) from
      mul_nonneg (by positivity) (Real.rpow_nonneg (zero_le_one.trans hH) _))

end JanetCartan.FourierIntegral.GainOneBranches
