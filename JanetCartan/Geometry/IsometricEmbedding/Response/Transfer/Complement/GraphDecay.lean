module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ForwardDecay
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ReverseDecay

/-!
# Complete graph complements on the original envelope

The graph estimates of `app:ch_response:thm:response-literal-transfer` with
all internal Fourier-cutoff obligations discharged. The cutoff is constructed
at one quarter of the supplied/derived source gap. It is never applied to the
final datum or used to change the operator. Primitive geometric and full-symbol
inputs come from compatible phase geometry; literal regularization convergence
and fixed Sobolev costs come from finite FIO calculus for the same operators.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.Complement
open FourierIntegral NormalComparison Pseudodifferential LowEnvelope ArbitraryAccuracy
variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The complete forward estimate with the internal low/high cutoff constructed
inside the proof. The original datum, literal graph, supports, and cutoff order
are retained. Only primitive phase/amplitude hypotheses, literal convergence,
and a fixed polynomial Sobolev cost are inputs.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem forwardCompleteComplement_rapidDecay
    (S : ι → E → E → ℝ) (φ : ι → E → ℝ)
    (A : ι → ℕ → FullAmplitude n r) (q₀ : ι → E → ℂ) (ζ : ι → E)
    (T : ι → H →L[ℂ] H) (u : ι → ℕ → H → H) (f : ι → H)
    (ρ L K a : ι → ℝ) (s t b : ℕ) (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (ν g Z D d : ℝ)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1) (hg : 0 < g)
    (hD : 0 ≤ D)
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
  let c := g / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let χ (i : ι) := internalEnvelopeCutoff n (c * (ρ i) ^ (1 - ν / 2))
    (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hρ i)) _))
  exact forwardComplement_rapidDecay S φ A q₀ ζ T u f ρ L K a s t b C PS Pφ
    ν c g Z 1 2 D d χ hν hc hg zero_le_one (by norm_num) hD
    (by dsimp [c]; linarith) hρ hL ha hLK hKρ hf hC hPS hPφ hζ hq hSc hS hφ hA
    hKs hKt hKη ht hfreq hs hAj hSj hφj hreal hlim hT

/-- The complete reverse estimate with its full source gap derived from
buffered inverse-chart geometry and its internal Fourier cutoff constructed.
The source for integration by parts is `x`. The original weighted inverse
amplitude and all shoulders remain in the literal regularizations.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem reverseCompleteComplement_rapidDecay {I : Type*}
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
        gradient (fun y ↦ S p y v) x‖)
    (A : ι → ℕ → FullAmplitude n r) (q₀ : ι → E → ℂ) (ζ : ι → E) (p : ι → I)
    (hp : ∀ i, p i ∈ P) (hζ : ∀ i, ζ i ∈ Z)
    (T : ι → H →L[ℂ] H) (u : ι → ℕ → H → H) (f : ι → H)
    (ρ L K a : ι → ℝ) (s t b : ℕ) (C : ℕ → ℕ → ℝ) (PS : ℕ → ℝ)
    (ν DT d : ℝ)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1)
    (hDT : 0 ≤ DT)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (ha : ∀ i, 0 ≤ a i)
    (hLK : ∀ i, L i ≤ K i) (hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hf : HasEnvelopeProfile vectorFourierSobolevScale f a K)
    (hC : ∀ j k, 0 ≤ C j k) (hPS : ∀ j, 0 ≤ PS j)
    (hq : ∀ i δ, ‖δ‖ < g * ρ i → q₀ i δ = 1)
    (hSc : ∀ i, Continuous (fun z : E × E ↦ S (p i) z.1 z.2))
    (hS : ∀ i η, ContDiff ℝ ∞ (fun z ↦ S (p i) z η))
    (hA : ∀ i k, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) p.1.1 p.1.2 p.2))
    {Ks Kt : Set E} {Kη : ι → ℕ → Set E}
    (hKs : IsCompact Ks) (hKsΩ : Ks ⊆ Ω) (hKt : IsCompact Kt) (hKη : ∀ i k, IsCompact (Kη i k))
    (ht : ∀ i k x y η, x ∉ Kt →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (hfreq : ∀ i k x y η, η ∉ Kη i k →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (hs : ∀ i k η x y, y ∉ Ks →
      complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) x y η = 0)
    (hchart : ∀ i k y x η, η ∉ D → A i k y x η = 0)
    (hAj : ∀ i k η (β : List (Fin n)) j x y,
      ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i) v w η) x) y‖ ≤
        C β.length j * L i ^ (b + β.length + j))
    (hSj : ∀ i η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun w ↦ S (p i) w η) x‖ ≤ PS j * ‖η‖ * L i ^ (j - 1))
    (hreal : ∀ i k v, (u i k v : E → EuclideanSpace ℂ (Fin r)) =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (reverseDemodulatedGraph (S (p i)) (fun x ↦ S (p i) x (ζ i))
        (complementaryAmplitude (A i k) (ζ i) (ρ i) (q₀ i))
        (ζ i) (ρ i) (fun y ↦ ⇑(v y)) x))
    (hlim : ∀ i v, Tendsto (fun k ↦ u i k v) atTop (𝓝 (T i v)))
    (hT : ∀ i v, MemVectorFourierSobolev (t : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (T i v) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i v) ≤
        DT * (ρ i) ^ d * vectorFourierSobolevNorm (t : ℝ) v) :
    RapidDecayAt vectorFourierSobolevScale s ρ a (fun i ↦ T i (f i)) := by
  obtain ⟨d₀, hd₀, hdecay⟩ := reverseComplement_rapidDecay_of_geometry (ι := ι) (r := r)
    S hΩ hU hΩU hZ hZ0 hZD hcone hSdiff hhom hm hM hB₀ hg hannular hinverse
  let c := d₀ / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let χ (i : ι) := internalEnvelopeCutoff n (c * (ρ i) ^ (1 - ν / 2))
    (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hρ i)) _))
  exact hdecay A q₀ ζ p hp hζ T u f ρ L K a s t b C PS ν c 1 2 DT d χ
    hν hc zero_le_one (by norm_num) hDT (by dsimp [c]; linarith)
    hρ hL ha hLK hKρ hf hC hPS hq hSc hS hA hKs hKsΩ hKt hKη ht hfreq hs
    hchart hAj hSj hreal hlim hT

end JanetCartan.ResponseTransfer.Complement
