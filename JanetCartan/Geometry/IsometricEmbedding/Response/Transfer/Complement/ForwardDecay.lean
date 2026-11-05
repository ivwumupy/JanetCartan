module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorDecay
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ForwardEstimate
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.SourceGeometry

/-!
# Arbitrary precision for the complete forward graph complement

The forward complete-complement paragraphs of
`app:ch_response:thm:response-literal-transfer`. The low estimate is proved from
primitive full-amplitude grades and the actual regularizations; the high estimate
is proved from the original vector Sobolev profile. Compatible phase geometry
produces the selector plateau and phase grades. The finite calculus produces
the literal regularizations and the fixed polynomial Sobolev cost for the SAME
operator. No projected source or complementary decay estimate is an input.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.Complement
open FourierIntegral NormalComparison Pseudodifferential LowEnvelope ArbitraryAccuracy
variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Complete forward complementary decay on the original envelope, including
all frequency shoulders and bounded frequencies. The cutoff at
`c ρ^(1-ν/2)` occurs only inside the proof. The constant precedes the family
index, which may include compact parameters and the coefficient field.
`T` is the actual demodulated complete graph, identified by `hreal`/`hlim`.
Its fixed polynomial Sobolev cost is the graph-calculus input, independent of
precision. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem forwardComplement_rapidDecay
    (S : ι → E → E → ℝ) (φ : ι → E → ℝ)
    (A : ι → ℕ → FullAmplitude n r) (q₀ : ι → E → ℂ) (ζ : ι → E)
    (T : ι → H →L[ℂ] H) (u : ι → ℕ → H → H) (f : ι → H)
    (ρ L K a : ι → ℝ) (s t b : ℕ) (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (ν c g Z B R D d : ℝ)
    (χ : ∀ i, EnvelopeCutoff n (c * (ρ i) ^ (1 - ν / 2)) B R)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1) (hc : 0 < c) (hg : 0 < g)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hD : 0 ≤ D) (hcg : R * c ≤ g / 2)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (ha : ∀ i, 0 ≤ a i)
    (hLK : ∀ i, L i ≤ K i) (hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hf : HasEnvelopeProfile vectorFourierSobolevScale f a K)
    (hC : ∀ j k, 0 ≤ C j k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    (hζ : ∀ i, ‖ζ i‖ ≤ Z)
    (hq : ∀ i δ, ‖δ‖ < g * ρ i → q₀ i δ = 1)
    (hSc : ∀ i, Continuous (fun p : E × E ↦ S i p.1 p.2))
    (hS : ∀ i η, ContDiff ℝ ∞ (fun z ↦ S i z η))
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hA : ∀ i k, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) p.1.1 p.1.2 p.2))
    {Ks Kt : Set E} {Kη : ι → ℕ → Set E}
    (hKs : IsCompact Ks) (hKt : IsCompact Kt) (hKη : ∀ i k, IsCompact (Kη i k))
    (ht : ∀ i k x y η, x ∉ Kt →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (hfreq : ∀ i k x y η, η ∉ Kη i k →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (hs : ∀ i k η x y, y ∉ Ks →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (hAj : ∀ i k η (β : List (Fin n)) j x y,
      ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) v w η) x) y‖ ≤
        C β.length j * L i ^ (b + β.length + j))
    (hSj : ∀ i η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun w ↦ S i w η) x‖ ≤ PS j * ‖η‖ * L i ^ (j - 1))
    (hφj : ∀ i j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (φ i) x‖ ≤ Pφ j * L i ^ (j - 1))
    (hreal : ∀ i k v, (u i k v : E → EuclideanSpace ℂ (Fin r)) =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (forwardDemodulatedGraph (S i) (φ i)
        (complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i))
        (ζ i) (ρ i) (fun y ↦ ⇑(v y)) x))
    (hlim : ∀ i v, Tendsto (fun k ↦ u i k v) atTop (𝓝 (T i v)))
    (hT : ∀ i v, MemVectorFourierSobolev (t : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (T i v) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i v) ≤
        D * (ρ i) ^ d * vectorFourierSobolevNorm (t : ℝ) v) :
    RapidDecayAt vectorFourierSobolevScale s ρ a (fun i ↦ T i (f i)) := by
  apply completeComplement_vector_rapidDecay T f ρ L K a s t 0 ν c B R D
    (b + s + n : ℕ) d χ hν hc hB hD hρ hL ha hLK hKρ hf hT
  intro q
  obtain ⟨C₀, hC₀, hf₀⟩ := (hasEnvelopeProfile_vectorFourier_iff f a K).mp hf 0
  let F := (r : ℝ) * lowEnvelopeSobolevConstant n r Ks Kt (forwardGapConstant g Z)
    (1 + Z + g / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C s q
  refine ⟨max 0 F * B * C₀ * R ^ ((n : ℝ) / 2), by positivity, ?_⟩
  intro i
  have hρp : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  have hΛ : 0 ≤ c * (ρ i) ^ (1 - ν / 2) := by positivity
  have hLρ : L i ≤ ρ i := (hLK i).trans ((hKρ i).trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (hρ i) (show 1 - ν ≤ 1 by linarith [hν.1])))
  obtain ⟨hm, hb⟩ := forwardComplement_lowSupport_vector
    (S i) (φ i) (A i) (q₀ i) (ζ i) s q b C PS Pφ hC hPS hPφ hg zero_le_one
    (hL i) hLρ (mul_nonneg hR hΛ)
    (farEnvelope_outerRadius_le (hρ i) hν.1.le hc.le hR hcg) (hζ i) (hq i)
    (hSc i) (hS i) (hφ i) (hA i) hKs hKt (hKη i) (ht i) (hfreq i) (hs i)
    (by simpa only [mul_one] using hAj i) (hSj i) (hφj i)
    ((χ i).physicalCovectorCutoff.vectorLow (f i))
    ((χ i).paperL2FourierTransform_vectorLow_zero_outside (f i)) (T i)
    (fun k ↦ u i k ((χ i).physicalCovectorCutoff.vectorLow (f i)))
    (fun k ↦ hreal i k _) (hlim i _)
  have hnorm : ‖(χ i).physicalCovectorCutoff.vectorLow (f i)‖ ≤ B * (C₀ * a i) := by
    apply ((χ i).physicalCovectorCutoff.norm_vectorLow_le (f i)).trans
    exact mul_le_mul_of_nonneg_left (by
      simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, pow_zero, mul_one] using
        (hf₀ i).2) hB
  refine ⟨hm, hb.trans ?_⟩
  change F * 1 * (ρ i) ^ (b + s + n) *
    (R * (c * (ρ i) ^ (1 - ν / 2))) ^ ((n : ℝ) / 2) * (L i / ρ i) ^ q *
      ‖(χ i).physicalCovectorCutoff.vectorLow (f i)‖ ≤ _
  have hLi : 0 ≤ L i := zero_le_one.trans (hL i)
  calc
    _ ≤ max 0 F * 1 * (ρ i) ^ (b + s + n) *
        (R * (c * (ρ i) ^ (1 - ν / 2))) ^ ((n : ℝ) / 2) * (L i / ρ i) ^ q *
          ‖(χ i).physicalCovectorCutoff.vectorLow (f i)‖ := by gcongr; exact le_max_right _ _
    _ ≤ max 0 F * 1 * (ρ i) ^ (b + s + n) *
        (R * (c * (ρ i) ^ (1 - ν / 2))) ^ ((n : ℝ) / 2) * (L i / ρ i) ^ q *
          (B * (C₀ * a i)) := by gcongr
    _ = _ := by
      rw [Real.mul_rpow hR hΛ, Real.rpow_natCast]
      simp only [pow_zero, mul_one]
      ring

end JanetCartan.ResponseTransfer.Complement
