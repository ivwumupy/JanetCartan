module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Assembly

/-!
# Uniform decay from the actual vector envelope split

The complete-complement split of `app:ch_response:thm:response-literal-transfer`.
The cutoff is evaluated at the physical covector `2πξ`. The high tail is derived
from `HasEnvelopeProfile`, with its Sobolev order chosen before the family index.
The low input of `completeComplement_vector_rapidDecay` is discharged by the
forward/reverse source integration estimates in the consuming graph theorems.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential JanetCartan.ArbitraryAccuracy

namespace JanetCartan.ResponseTransfer.Complement

variable {n r : ℕ} {ι : Type*}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The genuine physical-frequency high envelope pays every fixed polynomial
Sobolev cost of the same full operator. The cost is supplied by the graph/adjoint
Sobolev calculus and carrier multiplication; no high-tail estimate is assumed.
This holds at every positive cutoff radius, including the bounded-frequency
range. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorHigh_rapidDecay
    (T : ι → H →L[ℂ] H) (f : ι → H) (ρ K A : ι → ℝ)
    (s t : ℕ) (ν c B R D d : ℝ)
    (χ : ∀ i, EnvelopeCutoff n (c * (ρ i) ^ (1 - ν / 2)) B R)
    (hν : 0 < ν) (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρ : ∀ i, 1 ≤ ρ i) (hK : ∀ i, 0 ≤ K i) (hA : ∀ i, 0 ≤ A i)
    (hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hf : HasEnvelopeProfile vectorFourierSobolevScale f A K)
    (hT : ∀ i v, MemVectorFourierSobolev (t : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (T i v) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i v) ≤
        D * (ρ i) ^ d * vectorFourierSobolevNorm (t : ℝ) v) :
    RapidDecayAt vectorFourierSobolevScale s ρ A
      (fun i ↦ T i ((χ i).physicalCovectorCutoff.vectorHigh (f i))) := by
  intro Q
  obtain ⟨_, p₀, _, _, _, hp₀⟩ := exists_complement_orders hν 0 d Q 0 0 t
  let p := p₀ + t
  have htp : (t : ℝ) ≤ p := by dsimp [p]; exact_mod_cast Nat.le_add_left t p₀
  have hp : d + (1 - ν / 2) * t - (ν / 2) * p ≤ -Q := by
    dsimp [p]
    rw [Nat.cast_add]
    nlinarith [mul_nonneg hν.le (Nat.cast_nonneg (α := ℝ) t)]
  obtain ⟨C, hC, hprofile⟩ := (hasEnvelopeProfile_vectorFourier_iff f A K).mp hf p
  let F := (1 + B) * (2 * Real.pi) ^ ((p : ℝ) - t)
  have hF : 0 ≤ F := mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  refine ⟨D * F * C * c ^ ((t : ℝ) - p), by positivity, ?_⟩
  intro i
  have hρp : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  obtain ⟨hm, hb⟩ := (χ i).vectorHigh_physical_tail_bound
    (mul_pos hc (Real.rpow_pos_of_pos hρp _)) htp (hprofile i).1
  obtain ⟨hTm, hTb⟩ := hT i _ hm
  refine ⟨hTm, ?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hTm]
  calc
    _ ≤ D * (ρ i) ^ d * (F * (c * (ρ i) ^ (1 - ν / 2)) ^ ((t : ℝ) - p) *
        (C * A i * K i ^ p)) := by
      apply hTb.trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (Real.rpow_nonneg hρp.le _))
      exact hb.trans (mul_le_mul_of_nonneg_left (hprofile i).2
        (mul_nonneg hF (Real.rpow_nonneg (by positivity) _)))
    _ = (D * F * C * A i) * ((ρ i) ^ d * K i ^ p *
        (c * (ρ i) ^ (1 - ν / 2)) ^ ((t : ℝ) - p)) := by ring
    _ ≤ (D * F * C * A i) * (c ^ ((t : ℝ) - p) *
        (ρ i) ^ (d + (1 - ν / 2) * t - (ν / 2) * p)) :=
      mul_le_mul_of_nonneg_left (highEnvelope_scale_bound (hρ i) (hK i) hc (hKρ i) t p)
        (mul_nonneg (mul_nonneg (mul_nonneg hD hF) hC) (hA i))
    _ ≤ (D * F * C * A i) * (c ^ ((t : ℝ) - p) * (ρ i) ^ (-Q)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hρ i) hp)
          (Real.rpow_nonneg hc.le _))
        (mul_nonneg (mul_nonneg (mul_nonneg hD hF) hC) (hA i))
    _ = _ := by ring

/-- Complete vector assembly on the ORIGINAL datum, with its actual internal
Fourier split. The high estimate is proved from the source profile. The low
estimate is the output of `forwardComplement_lowSupport_vector` or
`reverseComplement_lowSupport_of_geometry`, not a hypothesis of the final
graph theorems. All fixed losses precede the integration orders and the family
index. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem completeComplement_vector_rapidDecay
    (T : ι → H →L[ℂ] H) (f : ι → H) (ρ L K A : ι → ℝ)
    (s t b : ℕ) (ν c B R D dLow dHigh : ℝ)
    (χ : ∀ i, EnvelopeCutoff n (c * (ρ i) ^ (1 - ν / 2)) B R)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1) (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hA : ∀ i, 0 ≤ A i)
    (hLK : ∀ i, L i ≤ K i) (hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hf : HasEnvelopeProfile vectorFourierSobolevScale f A K)
    (hT : ∀ i v, MemVectorFourierSobolev (t : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (T i v) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i v) ≤
        D * (ρ i) ^ dHigh * vectorFourierSobolevNorm (t : ℝ) v)
    (hlow : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      MemVectorFourierSobolev (s : ℝ) (T i ((χ i).physicalCovectorCutoff.vectorLow (f i))) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i ((χ i).physicalCovectorCutoff.vectorLow (f i))) ≤
        C * A i * (ρ i) ^ dLow * (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) *
          (L i) ^ b * (L i / ρ i) ^ q) :
    RapidDecayAt vectorFourierSobolevScale s ρ A (fun i ↦ T i (f i)) := by
  have hhigh := vectorHigh_rapidDecay T f ρ K A s t ν c B R D dHigh χ
    hν.1 hc hB hD hρ (fun i ↦ (zero_le_one.trans (hL i)).trans (hLK i)) hA hKρ hf hT
  intro Q
  obtain ⟨q, _, _, _, hq, _⟩ := exists_complement_orders hν.1 dLow dHigh Q n b t
  obtain ⟨C, hC, hlo⟩ := hlow q
  obtain ⟨D₁, hD₁, hhi⟩ := hhigh Q
  let C₁ := C * c ^ ((n : ℝ) / 2)
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨C₁ + D₁, add_nonneg hC₁ hD₁, ?_⟩
  intro i
  have hlob : vectorFourierSobolevNorm (s : ℝ)
      (T i ((χ i).physicalCovectorCutoff.vectorLow (f i))) ≤
      C₁ * A i * (ρ i) ^ (-Q) := by
    calc
      _ ≤ C * A i * (ρ i) ^ dLow * (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) *
          L i ^ b * (L i / ρ i) ^ q := (hlo i).2
      _ = (C * A i) * ((ρ i) ^ dLow * (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) *
          L i ^ b * (L i / ρ i) ^ q) := by ring
      _ ≤ (C * A i) * (c ^ ((n : ℝ) / 2) *
          (ρ i) ^ (dLow + (1 - ν / 2) * ((n : ℝ) / 2) + b - ν * q)) :=
        mul_le_mul_of_nonneg_left
          (lowEnvelope_scale_bound (hρ i) (zero_le_one.trans (hL i)) hν.1.le hc
            ((hLK i).trans (hKρ i)) n b q) (mul_nonneg hC (hA i))
      _ ≤ (C * A i) * (c ^ ((n : ℝ) / 2) * (ρ i) ^ (-Q)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hρ i) hq)
            (Real.rpow_nonneg hc.le _)) (mul_nonneg hC (hA i))
      _ = _ := by dsimp [C₁]; ring
  have he : T i (f i) = T i ((χ i).physicalCovectorCutoff.vectorLow (f i)) +
      T i ((χ i).physicalCovectorCutoff.vectorHigh (f i)) := by
    rw [← map_add, (χ i).physicalCovectorCutoff.vectorLow_add_vectorHigh]
  dsimp only
  rw [he]
  refine ⟨(vectorFourierSobolevScale.level s).add_mem (hlo i).1 (hhi i).1, ?_⟩
  calc
    _ ≤ vectorFourierSobolevScale.gradeNorm s
          (T i ((χ i).physicalCovectorCutoff.vectorLow (f i))) +
        vectorFourierSobolevScale.gradeNorm s
          (T i ((χ i).physicalCovectorCutoff.vectorHigh (f i))) :=
      ResponseTransfer.gradeNorm_add_le _ (hlo i).1 (hhi i).1
    _ ≤ C₁ * A i * (ρ i) ^ (-Q) + D₁ * A i * (ρ i) ^ (-Q) := by
      rw [vectorFourierSobolevScale_gradeNorm s (hlo i).1]
      exact add_le_add hlob (hhi i).2
    _ = _ := by ring

end JanetCartan.ResponseTransfer.Complement
