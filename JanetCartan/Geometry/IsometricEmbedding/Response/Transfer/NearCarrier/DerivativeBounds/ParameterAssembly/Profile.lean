module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.ParameterAssembly.Bounds

/-!
# The joint K profile

Conversion of the direct weighted finite sum into the joint `K^(s+q)`
profile of `app:ch_response:eq:direct-envelope-profile`. These are estimates
for actual mixed datum jets, not assumptions on the output operator.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier.ParameterAssembly

variable {d m : ℕ} {Y : Type*}
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Finite combination of datum profile constants used by
`app:ch_response:eq:direct-envelope-profile`. Only orders `p ≤ s` and mixed
words of length at most `z.length+is.length` occur. -/
def profileCoefficient (s : ℕ) (M : ℕ → List (Fin m ⊕ Fin d) → ℝ) :
    List (Fin m) → List (Fin m ⊕ Fin d) → ℝ
  | [], z => ∑ p ∈ Finset.range (s + 1), M p z
  | i :: is, z => profileCoefficient s M is z +
      ∑ j : Fin d, profileCoefficient s M is (.inr j :: z) +
      profileCoefficient s M is (.inl i :: z)

/-- Nonnegativity of the finite datum constant in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem profileCoefficient_nonneg (s : ℕ) (M : ℕ → List (Fin m ⊕ Fin d) → ℝ)
    (hM : ∀ p z, 0 ≤ M p z) (is : List (Fin m)) (z : List (Fin m ⊕ Fin d)) :
    0 ≤ profileCoefficient s M is z := by
  induction is generalizing z with
  | nil =>
      exact Finset.sum_nonneg fun p _ => hM p z
  | cons i is ih =>
      exact add_nonneg
        (add_nonneg (ih z) (Finset.sum_nonneg fun j _ => ih (.inr j :: z))) (ih (.inl i :: z))

/-- The shared derivative budget in
`app:ch_response:eq:direct-envelope-profile`: mixed datum bounds of order
`p+word.length` give total order `s+q+z.length`, since `1 ≤ L ≤ K`.
This deduction uses only the displayed finite set of datum norm bounds. -/
theorem profile_le_K
    (s : ℕ) (M : ℕ → List (Fin m ⊕ Fin d) → ℝ) (_hM : ∀ p z, 0 ≤ M p z)
    {L K A₀ : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K) (_hA : 0 ≤ A₀)
    (F : List (Fin m ⊕ Fin d) → Y → L2) (is : List (Fin m))
    (z : List (Fin m ⊕ Fin d)) (t : Y)
    (hF : ∀ z', z'.length ≤ z.length + is.length → ∀ p, p ≤ s →
      fourierSobolevNorm (p : ℝ) (F z' t) ≤ A₀ * M p z' * K ^ (p + z'.length)) :
    profile s L F is z t ≤
      A₀ * profileCoefficient s M is z * K ^ (s + is.length + z.length) := by
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 ≤ K := by linarith
  induction is generalizing z with
  | nil =>
    simp only [profile, profileCoefficient, List.length_nil, Nat.add_zero]
    unfold spatialEnvelopeSobolevProfile
    calc
      _ ≤ ∑ p ∈ Finset.range (s + 1), A₀ * M p z * K ^ (s + z.length) := by
        apply Finset.sum_le_sum
        intro p hp
        have hps : p ≤ s := by have := Finset.mem_range.mp hp; omega
        calc
          _ ≤ K ^ (s - p) * (A₀ * M p z * K ^ (p + z.length)) :=
            mul_le_mul (pow_le_pow_left₀ hL0 hLK _) (hF z (by simp) p hps)
              (fourierSobolevNorm_nonneg _ _) (pow_nonneg hK0 _)
          _ = _ := by
            rw [mul_left_comm, ← pow_add]
            congr 2
            omega
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  | cons i is ih =>
    have hr := ih z (fun z' hz' p hp => hF z' (by simp only [List.length_cons]; omega) p hp)
    have hd (j : Fin d) := ih (.inr j :: z)
      (fun z' hz' p hp => hF z' (by simp only [List.length_cons] at *; omega) p hp)
    have hp := ih (.inl i :: z)
      (fun z' hz' p hp => hF z' (by simp only [List.length_cons] at *; omega) p hp)
    have hr' : L * profile s L F is z t ≤
        A₀ * profileCoefficient s M is z * K ^ (s + (i :: is).length + z.length) := by
      calc
        _ ≤ K * (A₀ * profileCoefficient s M is z * K ^ (s + is.length + z.length)) :=
          mul_le_mul hLK hr (profile_nonneg s hL0 F is z t) hK0
        _ = _ := by
          rw [show s + (i :: is).length + z.length = (s + is.length + z.length) + 1 by
            simp only [List.length_cons]; omega, pow_succ]
          ring
    have hd' (j : Fin d) : profile s L F is (.inr j :: z) t ≤
        A₀ * profileCoefficient s M is (.inr j :: z) * K ^ (s + (i :: is).length + z.length) := by
      convert hd j using 1
      simp only [List.length_cons]
      congr 2
      omega
    have hp' : profile s L F is (.inl i :: z) t ≤
        A₀ * profileCoefficient s M is (.inl i :: z) * K ^ (s + (i :: is).length + z.length) := by
      convert hp using 1
      simp only [List.length_cons]
      congr 2
      omega
    calc
      _ ≤ A₀ * profileCoefficient s M is z * K ^ (s + (i :: is).length + z.length) +
          ∑ j, A₀ * profileCoefficient s M is (.inr j :: z) * K ^ (s + (i :: is).length + z.length) +
          A₀ * profileCoefficient s M is (.inl i :: z) * K ^ (s + (i :: is).length + z.length) :=
        add_le_add (add_le_add hr' (Finset.sum_le_sum fun j _ => hd' j)) hp'
      _ = _ := by simp only [profileCoefficient, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]

end JanetCartan.IsometricEmbedding.Response.NearCarrier.ParameterAssembly
