module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.SobolevAssembly

/-!
# Near-carrier spatial envelope profile

The passage from `app:ch_response:eq:direct-envelope-profile` to
`app:ch_response:eq:fixed-factor-transfer`, on literal Euclidean Lebesgue L².
The low calculus, primitive jets, and exact one-derivative identities remain
explicit inputs. No final operator estimate is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d : ℕ}
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- The finite weighted sum in `app:ch_response:eq:direct-envelope-profile`
is bounded by the datum's `K^s` profile whenever `1 ≤ L ≤ K`. Only datum
orders through `s` occur. -/
theorem spatialEnvelopeSobolevProfile_le_K (s : ℕ) {L K A₀ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (_hA : 0 ≤ A₀)
    (D : ℕ → ℝ) (f : L2)
    (hf : ∀ r, r ≤ s → fourierSobolevNorm (r : ℝ) f ≤ A₀ * D r * K ^ r) :
    spatialEnvelopeSobolevProfile s L f ≤
      A₀ * (∑ r ∈ Finset.range (s + 1), D r) * K ^ s := by
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 ≤ K := hL0.trans hLK
  unfold spatialEnvelopeSobolevProfile
  calc
    _ ≤ ∑ r ∈ Finset.range (s + 1), A₀ * D r * K ^ s := by
      apply Finset.sum_le_sum
      intro r hr
      have hrs : r ≤ s := by have := Finset.mem_range.mp hr; omega
      calc
        _ ≤ K ^ (s - r) * (A₀ * D r * K ^ r) :=
          mul_le_mul (pow_le_pow_left₀ hL0 hLK _) (hf r hrs)
            (fourierSobolevNorm_nonneg _ _) (pow_nonneg hK0 _)
        _ = _ := by rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hrs]
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace AmplitudeExpression

/-- The spatial `K^s` bound of `app:ch_response:eq:fixed-factor-transfer`,
derived from primitive finite jets, the uniform low calculus and the literal
spatial transfer identity. The constant precedes `L`, `K`, the amplitude
realization (including frequency), the datum, and its size `A₀`. -/
theorem exists_spatial_K_constant
    (v : Fin d → X) (qs : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : ℕ) (e : AmplitudeExpression X E ι) (he : e.derivativeCost = 0)
    (D : ℕ → ℝ) (hD : ∀ p, 0 ≤ D p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L K A₀ : ℝ), 1 ≤ L → L ≤ K → 0 ≤ A₀ →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + s → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (T : (X → E) → L2 →L[ℂ] L2) (P : (X → E) → Prop),
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T b‖ ≤ C₀ * A) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a)) →
      HasSpatialAmplitudeTransfer v qs B idx a T P → P (e.evaluate a) →
      ∀ f : L2, MemFourierSobolev (s : ℝ) f →
        (∀ r, r ≤ s → fourierSobolevNorm (r : ℝ) f ≤ A₀ * D r * K ^ r) →
        MemFourierSobolev (s : ℝ) (T (e.evaluate a) f) ∧
          fourierSobolevNorm (s : ℝ) (T (e.evaluate a) f) ≤
            C * A₀ * K ^ s := by
  obtain ⟨C, hC, hb⟩ := exists_spatialSobolev_constant_of_zero v qs B idx M hM
    c R hR C₀ hC₀ s e he
  refine ⟨C * ∑ r ∈ Finset.range (s + 1), D r,
    mul_nonneg hC (Finset.sum_nonneg fun r _ => hD r), ?_⟩
  intro L K A₀ hL hLK hA a ha hj T P hl hr hc ht hp f hf hnorm
  obtain ⟨hmem, hnormOut⟩ := hb L hL a ha hj T P hl hr hc ht hp f hf
  refine ⟨hmem, hnormOut.trans ?_⟩
  have hprofile := spatialEnvelopeSobolevProfile_le_K s hL hLK hA D f hnorm
  have h := mul_le_mul_of_nonneg_left hprofile hC
  simpa only [spatialEnvelopeSobolevProfile, mul_assoc, mul_left_comm, mul_comm] using h

end AmplitudeExpression
end JanetCartan.IsometricEmbedding.Response.NearCarrier
