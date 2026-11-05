module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.Sobolev
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Limits

/-!
# Low-envelope bounds through supplied regularization convergence

For `app:ch_response:thm:response-literal-transfer`, these theorems derive
uniform Sobolev bounds on the actual compact-frequency graphs from primitive
full-amplitude and phase grades, then pass to their supplied L² limit. The
frequency supports may grow without affecting the constant. No Sobolev bound
or membership of a regularization is an input.

The finite calculus must supply the full amplitudes with uniform grades and
identify the L² limit with its actual operator; compatible phase geometry must
supply the reverse gap. These conclusions do not construct that convergence.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison JanetCartan.Localization Pseudodifferential
variable {n r : ℕ}

/-- The forward low-envelope estimate passes through explicit L²
regularization convergence (`app:ch_response:thm:response-literal-transfer`).
All regularized Sobolev estimates are derived here, with a constant independent
of the regularization index and fixed loss `b+s+n`, independent of `q`. -/
theorem forwardComplement_lowSupport_sobolev_of_tendsto
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : ℕ → FullAmplitude n r) (χ : Euclidean n → ℂ) (ζ : Euclidean n)
    (s q b : ℕ) (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ) (hΛρ : Λ ≤ c * ρ / 2)
    (hζ : ‖ζ‖ ≤ Z) (hχ : ∀ δ, ‖δ‖ < c * ρ → χ δ = 1)
    (hSc : Continuous (fun p : Euclidean n × Euclidean n ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ∀ k, ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      complementaryAmplitude (A k) ζ ρ χ p.1.1 p.1.2 p.2))
    {K Kt : Set (Euclidean n)} {Kη : ℕ → Set (Euclidean n)} (hK : IsCompact K)
    (hKt : IsCompact Kt) (hKη : ∀ k, IsCompact (Kη k))
    (ht : ∀ k x y η, x ∉ Kt → complementaryAmplitude (A k) ζ ρ χ x y η = 0)
    (hf : ∀ k x y η, η ∉ Kη k → complementaryAmplitude (A k) ζ ρ χ x y η = 0)
    (hs : ∀ k η z y, y ∉ K → complementaryAmplitude (A k) ζ ρ χ z y η = 0)
    (hAj : ∀ m η (β : List (Fin n)) k z y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude (A m) ζ ρ χ v w η) z) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ S w η) z‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j φ z‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0)
    (u : ℕ → Fin r → Lp (α := Euclidean n) ℂ 2 volume)
    (v : Fin r → Lp (α := Euclidean n) ℂ 2 volume)
    (hreal : ∀ k i, (u k i : Euclidean n → ℂ) =ᵐ[volume]
      (fun x ↦ forwardDemodulatedGraph S φ (complementaryAmplitude (A k) ζ ρ χ)
        ζ ρ (fun y ↦ ⇑(f y)) x i))
    (hlim : ∀ i, Tendsto (fun k ↦ u k i) atTop (𝓝 (v i))) :
    (∀ i, MemFourierSobolev (s : ℝ) (v i)) ∧
    (∀ i, fourierSobolevNorm (s : ℝ) (v i) ≤
      lowEnvelopeSobolevConstant n r K Kt (forwardGapConstant c Z)
        (1 + Z + c / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C s q *
        a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖) := by
  have hreg (k : ℕ) := forwardComplement_lowSupport_sobolev S φ (A k) χ ζ s q b C PS Pφ
    hC hPS hPφ hc ha hL hLρ hΛ hΛρ hζ hχ hSc hS hφ (hA k) hK hKt (hKη k)
    (ht k) (hf k) (hs k) (hAj k) hSj hφj f hfs
  have hresult (i : Fin r) : MemFourierSobolev (s : ℝ) (v i) ∧
      fourierSobolevNorm (s : ℝ) (v i) ≤
        lowEnvelopeSobolevConstant n r K Kt (forwardGapConstant c Z)
        (1 + Z + c / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C s q *
          a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ := by
    apply memFourierSobolev_and_norm_le_of_tendsto (s : ℝ) (hlim i)
      (fun k ↦ ?_) tendsto_const_nhds (fun k ↦ ?_)
    all_goals
      obtain ⟨hm, hmem, hb⟩ := hreg k
      have he : (hm i).toLp _ = u k i := Lp.ext ((hm i).coeFn_toLp.trans (hreal k i).symm)
      first | exact he ▸ hmem i | exact he ▸ hb i
  exact ⟨fun i ↦ (hresult i).1, fun i ↦ (hresult i).2⟩

/-- The reverse low-envelope estimate passes through explicit L²
regularization convergence (`app:ch_response:thm:response-literal-transfer`).
All regularized Sobolev estimates are derived here, with a constant independent
of the regularization index and fixed loss `b+s+n`, independent of `q`. -/
theorem reverse_lowSupport_sobolev_of_tendsto
    {Ω K : Set (Euclidean n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : ℕ → FullAmplitude n r) (ζ : Euclidean n) (s q b : ℕ)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ)
    (hζ : ‖ζ‖ ≤ Z) (hΛρ : Λ ≤ c * ρ / 2)
    (hSc : Continuous (fun p : Euclidean n × Euclidean n ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ∀ k, ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A k p.1.1 p.1.2 p.2))
    {Kt : Set (Euclidean n)} {Kη : ℕ → Set (Euclidean n)}
    (hKt : IsCompact Kt) (hKη : ∀ k, IsCompact (Kη k))
    (ht : ∀ k y x η, y ∉ Kt → A k y x η = 0)
    (hf : ∀ k y x η, η ∉ Kη k → A k y x η = 0)
    (hs : ∀ k η z x, x ∉ K → A k z x η = 0)
    (hgap : ∀ k η, (∃ z x, A k z x η ≠ 0) → ∀ x ∈ Ω,
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x‖)
    (hAj : ∀ m η (β : List (Fin n)) k z x,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A m v w η) z) x‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0)
    (u : ℕ → Fin r → Lp (α := Euclidean n) ℂ 2 volume)
    (v : Fin r → Lp (α := Euclidean n) ℂ 2 volume)
    (hreal : ∀ k i, (u k i : Euclidean n → ℂ) =ᵐ[volume]
      (fun x ↦ reverseDemodulatedGraph S φ (A k) ζ ρ (fun x ↦ ⇑(f x)) x i))
    (hlim : ∀ i, Tendsto (fun k ↦ u k i) atTop (𝓝 (v i))) :
    (∀ i, MemFourierSobolev (s : ℝ) (v i)) ∧
    (∀ i, fourierSobolevNorm (s : ℝ) (v i) ≤
      lowEnvelopeSobolevConstant n r K Kt (c / 2) (PS 1 + Pφ 1 + c / 2)
        (fun j ↦ PS (j + 1) + Pφ (j + 1)) (fun _ ↦ 1 + Z) C s q *
        a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖) := by
  have hreg (k : ℕ) := reverse_lowSupport_sobolev hΩ hK hKΩ S φ (A k) ζ s q b C PS Pφ
    hC hPS hPφ hc ha hL hLρ hΛ hζ hΛρ hSc hS hφ (hA k) hKt (hKη k)
    (ht k) (hf k) (hs k) (hgap k) (hAj k) hSj hφj f hfs
  have hresult (i : Fin r) : MemFourierSobolev (s : ℝ) (v i) ∧
      fourierSobolevNorm (s : ℝ) (v i) ≤
        lowEnvelopeSobolevConstant n r K Kt (c / 2) (PS 1 + Pφ 1 + c / 2)
        (fun j ↦ PS (j + 1) + Pφ (j + 1)) (fun _ ↦ 1 + Z) C s q *
          a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ := by
    apply memFourierSobolev_and_norm_le_of_tendsto (s : ℝ) (hlim i)
      (fun k ↦ ?_) tendsto_const_nhds (fun k ↦ ?_)
    all_goals
      obtain ⟨hm, hmem, hb⟩ := hreg k
      have he : (hm i).toLp _ = u k i := Lp.ext ((hm i).coeFn_toLp.trans (hreal k i).symm)
      first | exact he ▸ hmem i | exact he ▸ hb i
  exact ⟨fun i ↦ (hresult i).1, fun i ↦ (hresult i).2⟩

end JanetCartan.ResponseTransfer.LowEnvelope
