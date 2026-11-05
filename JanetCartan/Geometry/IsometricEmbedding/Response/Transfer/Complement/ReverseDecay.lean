module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorDecay
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ReverseEstimate

/-!
# Arbitrary precision for the complete reverse graph complement

The reverse complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`. The full inverse-chart geometry
supplies a uniform source gap before frequency or datum is chosen. The original
weighted inverse amplitude, both physical positions and all cutoff shoulders
are retained. The finite calculus must supply the same literal regularization
limit and fixed polynomial Sobolev cost; no complementary bound is an input.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.Complement
open FourierIntegral NormalComparison Pseudodifferential LowEnvelope ArbitraryAccuracy
variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Complete reverse complementary decay from the full buffered chart. The
uniform gap `d₀` is constructed from the annular and inverse-chart bounds.
Every admissible internal Fourier cutoff gives the same ORIGINAL output.
The reverse phase uses source `x`; an amplitude such as `j_S U⁻¹` is never
replaced by an unweighted adjoint. Fixed coefficient/parameter labels may be
included in `ι`. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem reverseComplement_rapidDecay_of_geometry {I : Type*}
    (S : I → E → E → ℝ) {P : Set I} {Ω U Z D : Set E}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hΩU : Ω ⊆ U) (hZ : IsCompact Z)
    (hZ0 : ∀ ζ ∈ Z, ζ ≠ 0) (hZD : Z ⊆ D)
    (hcone : ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ → ρ • η ∈ D)
    (hSdiff : ∀ p ∈ P, ∀ η ∈ D, DifferentiableOn ℝ (fun x ↦ S p x η) U)
    (hhom : ∀ p ∈ P, ∀ x ∈ U, ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ →
      S p x (ρ • η) = ρ * S p x η)
    {m M B₀ g : ℝ} (hm : 0 < m) (hM : 0 < M) (hB₀ : 0 < B₀) (hg : 0 < g)
    (hannular : ∀ p ∈ P, ∀ x ∈ Ω, ∀ η ∈ D,
      m * ‖η‖ ≤ ‖gradient (fun y ↦ S p y η) x‖ ∧
      ‖gradient (fun y ↦ S p y η) x‖ ≤ M * ‖η‖)
    (hinverse : ∀ p ∈ P, ∀ x ∈ Ω, ∀ u ∈ D, ∀ v ∈ D,
      ‖u - v‖ ≤ B₀ * ‖gradient (fun y ↦ S p y u) x -
        gradient (fun y ↦ S p y v) x‖) :
    ∃ d₀ > 0,
    ∀ (A : ι → ℕ → FullAmplitude n r) (q₀ : ι → E → ℂ) (ζ : ι → E) (p : ι → I)
    (_hp : ∀ i, p i ∈ P) (_hζ : ∀ i, ζ i ∈ Z)
    (T : ι → H →L[ℂ] H) (u : ι → ℕ → H → H) (f : ι → H)
    (ρ L K a : ι → ℝ) (s t b : ℕ) (C : ℕ → ℕ → ℝ) (PS : ℕ → ℝ)
    (ν c B R DT d : ℝ)
    (_χ : ∀ i, EnvelopeCutoff n (c * (ρ i) ^ (1 - ν / 2)) B R)
    (_hν : ν ∈ Set.Ioo (0 : ℝ) 1) (_hc : 0 < c)
    (_hB : 0 ≤ B) (_hR : 0 ≤ R) (_hDT : 0 ≤ DT) (_hcg : R * c ≤ d₀ / 2)
    (_hρ : ∀ i, 1 ≤ ρ i) (_hL : ∀ i, 1 ≤ L i) (_ha : ∀ i, 0 ≤ a i)
    (_hLK : ∀ i, L i ≤ K i) (_hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (_hf : HasEnvelopeProfile vectorFourierSobolevScale f a K)
    (_hC : ∀ j k, 0 ≤ C j k) (_hPS : ∀ j, 0 ≤ PS j)
    (_hq : ∀ i δ, ‖δ‖ < g * ρ i → q₀ i δ = 1)
    (_hSc : ∀ i, Continuous (fun z : E × E ↦ S (p i) z.1 z.2))
    (_hS : ∀ i η, ContDiff ℝ ∞ (fun z ↦ S (p i) z η))
    (_hA : ∀ i k, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) p.1.1 p.1.2 p.2))
    {Ks Kt : Set E} {Kη : ι → ℕ → Set E}
    (_hKs : IsCompact Ks) (_hKsΩ : Ks ⊆ Ω) (_hKt : IsCompact Kt) (_hKη : ∀ i k, IsCompact (Kη i k))
    (_ht : ∀ i k x y η, x ∉ Kt →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (_hfreq : ∀ i k x y η, η ∉ Kη i k →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (_hs : ∀ i k η x y, y ∉ Ks →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (_hchart : ∀ i k y x η, η ∉ D → A i k y x η = 0)
    (_hAj : ∀ i k η (β : List (Fin n)) j x y,
      ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) v w η) x) y‖ ≤
        C β.length j * L i ^ (b + β.length + j))
    (_hSj : ∀ i η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun w ↦ S (p i) w η) x‖ ≤ PS j * ‖η‖ * L i ^ (j - 1))
    (_hreal : ∀ i k v, (u i k v : E → EuclideanSpace ℂ (Fin r)) =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (reverseDemodulatedGraph (S (p i)) (fun x ↦ S (p i) x (ζ i))
        (complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i))
        (ζ i) (ρ i) (fun y ↦ ⇑(v y)) x))
    (_hlim : ∀ i v, Tendsto (fun k ↦ u i k v) atTop (𝓝 (T i v)))
    (_hT : ∀ i v, MemVectorFourierSobolev (t : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (T i v) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i v) ≤
        DT * (ρ i) ^ d * vectorFourierSobolevNorm (t : ℝ) v),
    RapidDecayAt vectorFourierSobolevScale s ρ a (fun i ↦ T i (f i)) := by
  obtain ⟨d₀, hd₀, Z₀, hZ₀, hlow⟩ := reverseComplement_lowSupport_of_geometry (r := r)
    S hΩ hU hΩU hZ hZ0 hZD hcone hSdiff hhom hm hM hB₀ hg hannular hinverse
  refine ⟨d₀, hd₀, ?_⟩
  intro A q₀ ζ p hp hζ T u f ρ L K a s t b C PS ν c B R DT d χ
    hν hc hB hR hDT hcg hρ hL ha hLK hKρ hf hC hPS hq hSc hS hA
    Ks Kt Kη hKs hKsΩ hKt hKη ht hfreq hs hchart hAj hSj hreal hlim hT
  apply completeComplement_vector_rapidDecay T f ρ L K a s t 0 ν c B R DT
    (b + s + n : ℕ) d χ hν hc hB hDT hρ hL ha hLK hKρ hf hT
  intro q
  obtain ⟨C₀, hC₀, hf₀⟩ := (hasEnvelopeProfile_vectorFourier_iff f a K).mp hf 0
  let F := (r : ℝ) * lowEnvelopeSobolevConstant n r Ks Kt (d₀ / 2)
    (PS 1 + PS 1 * Z₀ + d₀ / 2)
    (fun j ↦ PS (j + 1) + PS (j + 1) * Z₀) (fun _ ↦ 1 + Z₀) C s q
  refine ⟨max 0 F * B * C₀ * R ^ ((n : ℝ) / 2), by positivity, ?_⟩
  intro i
  have hρp : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  have hΛ : 0 ≤ c * (ρ i) ^ (1 - ν / 2) := by positivity
  have hLρ : L i ≤ ρ i := (hLK i).trans ((hKρ i).trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (hρ i) (show 1 - ν ≤ 1 by linarith [hν.1])))
  obtain ⟨hm, hb⟩ := hlow (p i) (hp i) (ζ i) (hζ i) (A i) (q₀ i) s q b C PS
    hC hPS 1 (L i) (ρ i) (R * (c * (ρ i) ^ (1 - ν / 2))) zero_le_one
    (hL i) hLρ (mul_nonneg hR hΛ)
    (farEnvelope_outerRadius_le (hρ i) hν.1.le hc.le hR hcg)
    (hq i) (hSc i) (hS i) (hA i) Ks Kt (Kη i) hKs hKsΩ hKt (hKη i)
    (ht i) (hfreq i) (hs i) (hchart i)
    (by simpa only [mul_one] using hAj i) (hSj i)
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
