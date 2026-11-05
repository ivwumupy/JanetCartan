module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.ParameterAssembly.Jets

/-!
# Weighted finite mixed jet estimates

The quantitative induction for `app:ch_response:eq:direct-envelope-profile`.
The constant precedes scales, primitive fields, realizations, data, and parameter
points. All modified-amplitude estimates are supplied by the checked spatial
Sobolev theorem. The datum profile below is a finite weighted sum, with each
parameter differentiation either supplying a factor `L` or taking one actual
mixed datum derivative.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier.ParameterAssembly

variable {d m : ℕ} {X E ι Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- The direct finite weighted datum sum for
`app:ch_response:eq:direct-envelope-profile`. A leaf taking `r` new datum derivatives has
weight `L^(q-r)` times the spatial profile, so the total budget is `s+q`.
Repeated branches are retained, including their multiplicity. -/
def profile (s : ℕ) (L : ℝ) (F : List (Fin m ⊕ Fin d) → Y → L2) :
    List (Fin m) → List (Fin m ⊕ Fin d) → Y → ℝ
  | [], z, t => spatialEnvelopeSobolevProfile s L (F z t)
  | i :: is, z, t => L * profile s L F is z t +
      ∑ j : Fin d, profile s L F is (.inr j :: z) t +
      profile s L F is (.inl i :: z) t

/-- Positivity of the weighted finite sum in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem profile_nonneg (s : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (F : List (Fin m ⊕ Fin d) → Y → L2) (is : List (Fin m))
    (z : List (Fin m ⊕ Fin d)) (t : Y) : 0 ≤ profile s L F is z t := by
  induction is generalizing z with
  | nil =>
      unfold profile spatialEnvelopeSobolevProfile
      exact Finset.sum_nonneg fun r _ => mul_nonneg (pow_nonneg hL _) (fourierSobolevNorm_nonneg _ _)
  | cons i is ih =>
      simp only [profile]
      exact add_nonneg
        (add_nonneg (mul_nonneg hL (ih z)) (Finset.sum_nonneg fun j _ => ih (.inr j :: z)))
        (ih (.inl i :: z))

private theorem sobolev_add_sum {J : Type*} (t : Finset J) {s : ℝ}
    {u : L2} {v : J → L2} (hu : MemFourierSobolev s u)
    (hv : ∀ j ∈ t, MemFourierSobolev s (v j)) :
    MemFourierSobolev s (u + ∑ j ∈ t, v j) ∧
      fourierSobolevNorm s (u + ∑ j ∈ t, v j) ≤
        fourierSobolevNorm s u + ∑ j ∈ t, fourierSobolevNorm s (v j) := by
  classical
  induction t using Finset.induction_on generalizing u with
  | empty => simpa using And.intro hu (le_refl (fourierSobolevNorm s u))
  | @insert j t hj ih =>
    have hjmem := hv j (Finset.mem_insert_self _ _)
    have h := ih (hu.add hjmem) (fun k hk => hv k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert hj, ← add_assoc]
    refine ⟨h.1, h.2.trans ?_⟩
    rw [Finset.sum_insert hj, ← add_assoc]
    exact add_le_add (fourierSobolevNorm_add_le hu hjmem) le_rfl

/-- Finite parameter transfer bound in
`app:ch_response:eq:direct-envelope-profile`, before identifying the expression
with actual derivatives. This strengthened induction allows initial amplitude
cost `k`; it uses primitive jets only through `c+k+s+q`. Datum Sobolev membership
is needed only through mixed word length `z.length+q`. The predicate `P` is the
support/sector admissibility condition; its preservation contains no norm bound.
The only operator norm premise is the uniform low theorem. -/
theorem exists_value_constant
    (v : Fin m → X) (qs : Fin m → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin m → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin m → Fin d → ι)
    (sv : Fin d → X) (sq : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (sB : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (si : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : ℕ) (is : List (Fin m)) (e : AmplitudeExpression X E ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + e.derivativeCost + s + is.length → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (T : Y → (X → E) → L2 →L[ℂ] L2) (P : (X → E) → Prop) (t : Y),
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T t b‖ ≤ C₀ * A) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (sv i) (sq i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (sB i j) (si i j)).evaluate a)) →
      HasSpatialAmplitudeTransfer sv sq sB si a (T t) P →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a)) →
      P (e.evaluate a) →
      ∀ (F : List (Fin m ⊕ Fin d) → Y → L2) (z : List (Fin m ⊕ Fin d)),
      (∀ z', z'.length ≤ z.length + is.length → MemFourierSobolev (s : ℝ) (F z' t)) →
      MemFourierSobolev (s : ℝ) (value v qs B idx a T F is e z t) ∧
        fourierSobolevNorm (s : ℝ) (value v qs B idx a T F is e z t) ≤
          C * (L ^ e.derivativeCost * profile s L F is z t) := by
  classical
  induction is generalizing e with
  | nil =>
    obtain ⟨C, hC, hbound⟩ := e.exists_spatialSobolev_constant sv sq sB si M hM c R hR C₀ hC₀ s
    refine ⟨C, hC, ?_⟩
    intro L hL a ha hj T P t hl hsr hsc hs _ _ he F z hF
    exact hbound L hL a ha (by simpa using hj) (T t) P hl hsr hsc hs he (F z t)
      (hF z (by simp))
  | cons i is ih =>
    obtain ⟨Cr, hCr, hr⟩ := ih (e.divergenceTransfer (v i) (qs i))
    choose Cd hCd hd using fun j : Fin d => ih (e.coefficientProduct (B i j) (idx i j))
    obtain ⟨Cp, hCp, hp⟩ := ih e
    let C := Cr + ∑ j, Cd j + Cp
    have hsum : 0 ≤ ∑ j, Cd j := Finset.sum_nonneg fun j _ => hCd j
    have hC : 0 ≤ C := add_nonneg (add_nonneg hCr hsum) hCp
    have hCrC : Cr ≤ C := by dsimp [C]; linarith
    have hCpC : Cp ≤ C := by dsimp [C]; linarith
    have hCdC (j : Fin d) : Cd j ≤ C := by
      have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hCd k) (Finset.mem_univ j)
      dsimp [C]; linarith
    refine ⟨C, hC, ?_⟩
    intro L hL a ha hj T P t hl hsr hsc hs hpr hpc he F z hF
    have hL0 : 0 ≤ L := by linarith
    have hrout := hr L hL a ha
      (fun l n hn => hj l n (by
        simp only [AmplitudeExpression.derivativeCost_divergenceTransfer] at hn
        simp only [List.length_cons]
        omega))
      T P t hl hsr hsc hs hpr hpc (hpr e he i) F z
      (fun z' hz' => hF z' (by simp only [List.length_cons]; omega))
    have hdout (j : Fin d) := hd j L hL a ha
      (fun l n hn => hj l n (by
        simp only [AmplitudeExpression.derivativeCost_coefficientProduct] at hn
        simp only [List.length_cons]
        omega))
      T P t hl hsr hsc hs hpr hpc (hpc e he i j) F (.inr j :: z)
      (fun z' hz' => hF z' (by simp only [List.length_cons] at *; omega))
    have hpout := hp L hL a ha
      (fun l n hn => hj l n (by simp only [List.length_cons]; omega))
      T P t hl hsr hsc hs hpr hpc he F (.inl i :: z)
      (fun z' hz' => hF z' (by simp only [List.length_cons] at *; omega))
    have hsout := sobolev_add_sum Finset.univ hrout.1 (fun j _ => (hdout j).1)
    refine ⟨hsout.1.add hpout.1, ?_⟩
    have hrt : fourierSobolevNorm (s : ℝ)
        (value v qs B idx a T F is (e.divergenceTransfer (v i) (qs i)) z t) ≤
        C * (L ^ e.derivativeCost * (L * profile s L F is z t)) := by
      apply hrout.2.trans
      simp only [AmplitudeExpression.derivativeCost_divergenceTransfer, pow_succ, mul_assoc]
      exact mul_le_mul_of_nonneg_right hCrC
        (mul_nonneg (pow_nonneg hL0 _) (mul_nonneg hL0 (profile_nonneg s hL0 F is z t)))
    have hdt (j : Fin d) : fourierSobolevNorm (s : ℝ)
        (value v qs B idx a T F is (e.coefficientProduct (B i j) (idx i j)) (.inr j :: z) t) ≤
        C * (L ^ e.derivativeCost * profile s L F is (.inr j :: z) t) := by
      apply (hdout j).2.trans
      simp only [AmplitudeExpression.derivativeCost_coefficientProduct]
      exact mul_le_mul_of_nonneg_right (hCdC j)
        (mul_nonneg (pow_nonneg hL0 _) (profile_nonneg s hL0 F is _ t))
    have hpt := hpout.2.trans (mul_le_mul_of_nonneg_right hCpC
      (mul_nonneg (pow_nonneg hL0 _) (profile_nonneg s hL0 F is (.inl i :: z) t)))
    calc
      _ ≤ (fourierSobolevNorm (s : ℝ)
          (value v qs B idx a T F is (e.divergenceTransfer (v i) (qs i)) z t) +
          ∑ j, fourierSobolevNorm (s : ℝ)
            (value v qs B idx a T F is (e.coefficientProduct (B i j) (idx i j)) (.inr j :: z) t)) +
          fourierSobolevNorm (s : ℝ) (value v qs B idx a T F is e (.inl i :: z) t) :=
        (fourierSobolevNorm_add_le hsout.1 hpout.1).trans (add_le_add hsout.2 le_rfl)
      _ ≤ C * (L ^ e.derivativeCost * (L * profile s L F is z t)) +
          ∑ j, C * (L ^ e.derivativeCost * profile s L F is (.inr j :: z) t) +
          C * (L ^ e.derivativeCost * profile s L F is (.inl i :: z) t) :=
        add_le_add (add_le_add hrt (Finset.sum_le_sum fun j _ => hdt j)) hpt
      _ = _ := by simp only [profile, mul_add, Finset.mul_sum]

end JanetCartan.IsometricEmbedding.Response.NearCarrier.ParameterAssembly
