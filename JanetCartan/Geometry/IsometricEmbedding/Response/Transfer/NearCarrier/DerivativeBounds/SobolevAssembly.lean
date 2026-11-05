module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.TransferAmplitudes
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic

/-!
# Spatial Sobolev assembly for near-carrier amplitudes

This is the spatial induction in `app:ch_response:eq:direct-envelope-profile`.
The analytic inputs are a uniform low L² theorem and the literal one-derivative
distributional transfer identity on L² data with L² coordinate derivatives.
The geometric construction must supply that identity and preservation of the
support/sector predicate. The predicate is not a norm bound.

All spaces here are scalar Euclidean Lebesgue L² spaces. Primitive jets, not
modified-amplitude estimates, are hypotheses. The physical derivative estimates
retain their `2π` constants.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d : ℕ}
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- The spatial profile in `app:ch_response:eq:direct-envelope-profile`, with
the literal Euclidean Fourier Sobolev norms at each integer order. -/
def spatialEnvelopeSobolevProfile (s : ℕ) (L : ℝ) (f : L2) : ℝ :=
  ∑ r ∈ Finset.range (s + 1), L ^ (s - r) * fourierSobolevNorm (r : ℝ) f

private theorem profile_nonneg (s : ℕ) {L : ℝ} (hL : 0 ≤ L) (f : L2) :
    0 ≤ spatialEnvelopeSobolevProfile s L f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hL _)
    (fourierSobolevNorm_nonneg _ _)

private theorem profile_scale_le (s : ℕ) {L : ℝ} (hL : 0 ≤ L) (f : L2) :
    L * spatialEnvelopeSobolevProfile s L f ≤ spatialEnvelopeSobolevProfile (s + 1) L f := by
  unfold spatialEnvelopeSobolevProfile
  rw [Finset.mul_sum]
  calc
    _ = ∑ r ∈ Finset.range (s + 1), L ^ (s + 1 - r) * fourierSobolevNorm (r : ℝ) f := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [show s + 1 - r = (s - r) + 1 by have := Finset.mem_range.mp hr; omega,
        pow_succ]
      ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun r _ _ => mul_nonneg (pow_nonneg hL _) (fourierSobolevNorm_nonneg _ _))

private theorem profile_le_succ (s : ℕ) {L : ℝ} (hL : 1 ≤ L) (f : L2) :
    spatialEnvelopeSobolevProfile s L f ≤ spatialEnvelopeSobolevProfile (s + 1) L f :=
  (le_mul_of_one_le_left (profile_nonneg s (by linarith) f) hL).trans
    (profile_scale_le s (by linarith) f)

private theorem profile_derivative_le (s : ℕ) {L : ℝ} (hL : 0 ≤ L)
    {f g : L2} {i : Fin d} (hg : HasEuclideanL2CoordinateDerivative i f g)
    (hf : MemFourierSobolev ((s + 1 : ℕ) : ℝ) f) :
    spatialEnvelopeSobolevProfile s L g ≤
      (2 * Real.pi) * spatialEnvelopeSobolevProfile (s + 1) L f := by
  unfold spatialEnvelopeSobolevProfile
  calc
    _ ≤ ∑ r ∈ Finset.range (s + 1),
        (2 * Real.pi) * (L ^ (s - r) * fourierSobolevNorm ((r : ℝ) + 1) f) := by
      apply Finset.sum_le_sum
      intro r hr
      have horder : (r : ℝ) + 1 ≤ ((s + 1 : ℕ) : ℝ) := by
        exact_mod_cast Finset.mem_range.mp hr
      have h := mul_le_mul_of_nonneg_left
        (hg.fourierSobolevNorm_le (by positivity) (hf.mono horder)) (pow_nonneg hL (s - r))
      nlinarith
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.sum_range_succ' (n := s + 1)]
      simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
      exact le_add_of_nonneg_right
        (mul_nonneg (pow_nonneg hL _) (fourierSobolevNorm_nonneg _ _))

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

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The conditional analytic input to the spatial induction in
`app:ch_response:eq:direct-envelope-profile`. Each equality asserts the actual
coordinate weak derivative of the actual output. It is required only for data
possessing all first coordinate derivatives in L². Directions, coefficient maps,
and primitive indices are fixed before scale, fields, and operator realization.
The geometry and oscillatory integral construction must prove this identity;
no Sobolev membership or operator estimate is part of it. -/
def HasSpatialAmplitudeTransfer
    (v : Fin d → X) (qs : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin d → Fin d → ι)
    (a : ι → X → E) (T : (X → E) → L2 →L[ℂ] L2) (P : (X → E) → Prop) : Prop :=
  ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
    ∀ (f : L2) (df : Fin d → L2),
      (∀ j, HasEuclideanL2CoordinateDerivative j f (df j)) →
      ∀ i, HasEuclideanL2CoordinateDerivative i (T (b.evaluate a) f)
        (T ((b.divergenceTransfer (v i) (qs i)).evaluate a) f +
          ∑ j, T ((b.coefficientProduct (B i j) (idx i j)).evaluate a) (df j))

namespace AmplitudeExpression

/-- Strengthened spatial induction for
`app:ch_response:eq:direct-envelope-profile`. An initial expression of cost `k`
uses primitive jets only through `c + k + s` and contributes the extra factor
`L^k`. The constant precedes scale, primitive fields, operator realizations
(including any frequency index), and datum. Modified-amplitude bounds follow
from `exists_lowOperator_constant`; they are never hypotheses.

The support/sector predicate must be preserved by the two literal modifications.
Its geometric meaning and the one-derivative identity remain obligations of the
parent near-carrier construction. -/
theorem exists_spatialSobolev_constant
    (v : Fin d → X) (qs : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : ℕ) (e : AmplitudeExpression X E ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + e.derivativeCost + s → ∀ x,
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
        MemFourierSobolev (s : ℝ) (T (e.evaluate a) f) ∧
          fourierSobolevNorm (s : ℝ) (T (e.evaluate a) f) ≤
            C * (L ^ e.derivativeCost * spatialEnvelopeSobolevProfile s L f) := by
  classical
  induction s generalizing e with
  | zero =>
    obtain ⟨C, hC, hbound⟩ := e.exists_lowOperator_constant M hM c R e.derivativeCost
      hR le_rfl C₀ hC₀ (H := L2) (K := L2)
    refine ⟨C, hC, ?_⟩
    intro L hL a ha hj T P hl _ _ _ hp f _
    refine ⟨by simp, ?_⟩
    simpa [spatialEnvelopeSobolevProfile, mul_assoc] using
      (hbound L hL a ha (by simpa using hj) T P hl hp).2 f
  | succ s ih =>
    obtain ⟨Cb, hCb, hb⟩ := ih e
    choose Cr hCr hr using fun i : Fin d => ih (e.divergenceTransfer (v i) (qs i))
    choose Cd hCd hd using fun i j : Fin d => ih (e.coefficientProduct (B i j) (idx i j))
    let C := Cb + ∑ i, (Cr i + (2 * Real.pi) * ∑ j, Cd i j)
    have hC : 0 ≤ C := add_nonneg hCb (Finset.sum_nonneg fun i _ =>
      add_nonneg (hCr i) (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hCd i j)))
    refine ⟨C, hC, ?_⟩
    intro L hL a ha hj T P hl hrem hcoeff htransfer hp f hf
    have hL0 : 0 ≤ L := by linarith
    have hfs : MemFourierSobolev (s : ℝ) f := hf.mono (by exact_mod_cast Nat.le_succ s)
    have hf' : MemFourierSobolev ((s : ℝ) + 1) f := by
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    obtain ⟨df, hdf⟩ := hf'.exists_coordinateDerivatives (by positivity)
    have hjb : ∀ i j, j ≤ c + e.derivativeCost + s → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R) :=
      fun i j h => hj i j (by omega)
    have hbout := hb L hL a ha hjb T P hl hrem hcoeff htransfer hp f hfs
    have hrout (i : Fin d) := hr i L hL a ha
      (fun l j h => hj l j (by simp only [derivativeCost_divergenceTransfer] at h; omega))
      T P hl hrem hcoeff htransfer (hrem e hp i) f hfs
    have hdout (i j : Fin d) := hd i j L hL a ha
      (fun l m h => hj l m (by simp only [derivativeCost_coefficientProduct] at h; omega))
      T P hl hrem hcoeff htransfer (hcoeff e hp i j) (df j) (hdf j).2
    let g : Fin d → L2 := fun i =>
      T ((e.divergenceTransfer (v i) (qs i)).evaluate a) f +
        ∑ j, T ((e.coefficientProduct (B i j) (idx i j)).evaluate a) (df j)
    have hgmem (i : Fin d) : MemFourierSobolev (s : ℝ) (g i) :=
      (sobolev_add_sum Finset.univ (hrout i).1 (fun j _ => (hdout i j).1)).1
    have hgderiv (i : Fin d) : HasEuclideanL2CoordinateDerivative i (T (e.evaluate a) f) (g i) :=
      htransfer e hp f df (fun j => (hdf j).1) i
    let S := L ^ e.derivativeCost * spatialEnvelopeSobolevProfile (s + 1) L f
    have hbterm : fourierSobolevNorm (s : ℝ) (T (e.evaluate a) f) ≤ Cb * S :=
      hbout.2.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (profile_le_succ s hL f) (pow_nonneg hL0 _)) hCb)
    have hrterm (i : Fin d) :
        fourierSobolevNorm (s : ℝ) (T ((e.divergenceTransfer (v i) (qs i)).evaluate a) f) ≤
          Cr i * S := by
      apply (hrout i).2.trans
      apply mul_le_mul_of_nonneg_left _ (hCr i)
      simp only [derivativeCost_divergenceTransfer, pow_succ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (profile_scale_le s hL0 f) (pow_nonneg hL0 _)
    have hdterm (i j : Fin d) :
        fourierSobolevNorm (s : ℝ) (T ((e.coefficientProduct (B i j) (idx i j)).evaluate a) (df j)) ≤
          ((2 * Real.pi) * Cd i j) * S := by
      calc
        _ ≤ Cd i j * (L ^ e.derivativeCost * spatialEnvelopeSobolevProfile s L (df j)) := by
          simpa only [derivativeCost_coefficientProduct] using (hdout i j).2
        _ ≤ Cd i j * (L ^ e.derivativeCost * ((2 * Real.pi) *
            spatialEnvelopeSobolevProfile (s + 1) L f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (profile_derivative_le s hL0 (hdf j).1 hf) (pow_nonneg hL0 _)) (hCd i j)
        _ = _ := by dsimp [S]; ring
    have hgterm (i : Fin d) : fourierSobolevNorm (s : ℝ) (g i) ≤
        (Cr i + (2 * Real.pi) * ∑ j, Cd i j) * S := by
      calc
        _ ≤ _ := (sobolev_add_sum Finset.univ (hrout i).1 (fun j _ => (hdout i j).1)).2
        _ ≤ Cr i * S + ∑ j, ((2 * Real.pi) * Cd i j) * S :=
          add_le_add (hrterm i) (Finset.sum_le_sum fun j _ => hdterm i j)
        _ = _ := by rw [add_mul, Finset.mul_sum, Finset.sum_mul]
    constructor
    · -- Assemble actual derivative representatives using the published word family.
      choose w hw using fun i => (hgmem i).exists_integerDerivatives
      let W : EuclideanL2DerivativeFamily d (s + 1) := fun x =>
        match x with
        | none => T (e.evaluate a) f
        | some (i, j) => w i j
      have hW : HasEuclideanL2Derivatives (s + 1) (T (e.evaluate a) f) W := by
        refine ⟨rfl, fun i => ?_⟩
        change HasEuclideanL2CoordinateDerivative i (T (e.evaluate a) f)
            (w i (.empty d s)) ∧
          HasEuclideanL2Derivatives s (w i (.empty d s)) (w i)
        rw [(hw i).root]
        exact ⟨hgderiv i, hw i⟩
      exact hW.memFourierSobolev
    · calc
        _ ≤ fourierSobolevNorm (s : ℝ) (T (e.evaluate a) f) +
            ∑ i, fourierSobolevNorm (s : ℝ) (g i) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            fourierSobolevNorm_le_coordinateDerivatives (by positivity) hbout.1 hgmem hgderiv
        _ ≤ Cb * S + ∑ i, (Cr i + (2 * Real.pi) * ∑ j, Cd i j) * S :=
          add_le_add hbterm (Finset.sum_le_sum fun i _ => hgterm i)
        _ = _ := by rw [← Finset.sum_mul, ← add_mul]

/-- The cost-zero spatial estimate of
`app:ch_response:eq:direct-envelope-profile`, on literal Euclidean Lebesgue L².
Only primitive jets through `c + s` are needed. The constant is uniform over
all frequency-indexed realizations satisfying the displayed low theorem and
first-derivative identity, since it is chosen before the realization `T`.
The parent construction must supply these analytic inputs and the support/sector
preservation hypotheses; this theorem makes no assertion that they hold for an
unconstructed oscillatory integral. -/
theorem exists_spatialSobolev_constant_of_zero
    (v : Fin d → X) (qs : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : ℕ) (e : AmplitudeExpression X E ι) (he : e.derivativeCost = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
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
        MemFourierSobolev (s : ℝ) (T (e.evaluate a) f) ∧
          fourierSobolevNorm (s : ℝ) (T (e.evaluate a) f) ≤
            C * ∑ r ∈ Finset.range (s + 1), L ^ (s - r) * fourierSobolevNorm (r : ℝ) f := by
  simpa only [he, Nat.add_zero, pow_zero, one_mul, spatialEnvelopeSobolevProfile] using
    exists_spatialSobolev_constant v qs B idx M hM c R hR C₀ hC₀ s e

end AmplitudeExpression
end JanetCartan.IsometricEmbedding.Response.NearCarrier
