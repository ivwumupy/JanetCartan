module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.Regularization
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# The literal forward low-envelope estimate on vector L²

This is the forward low-frequency input to the complete-complement assembly in
`app:ch_response:thm:response-literal-transfer`. The existing low-envelope
theorem derives the full forward source gap and all scalar Sobolev estimates.
Here the same regularization limit is identified with the actual vector
operator, in the existing Hilbert Sobolev norm.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement

open FourierIntegral NormalComparison Pseudodifferential LowEnvelope

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Vector Hilbert Sobolev membership and the complete forward low-envelope
bound. The regularizations retain the original physical cutoffs and all
frequency shoulders. Their source-gradient gap follows from the selector
plateau; no oscillatory kernel bound is assumed. The constant is independent
of the growing regularization frequency support, and `b+s+n` is independent
of `q`. The finite calculus must supply the displayed primitive grades and
literal convergence to `T`. Source: `app:ch_response:thm:response-literal-transfer`.
-/
theorem forwardComplement_lowSupport_vector
    (S : E → E → ℝ) (φ : E → ℝ)
    (A : ℕ → FullAmplitude n r) (χ : E → ℂ) (ζ : E)
    (s q b : ℕ) (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ j k, 0 ≤ C j k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ) (hΛρ : Λ ≤ c * ρ / 2)
    (hζ : ‖ζ‖ ≤ Z) (hχ : ∀ δ, ‖δ‖ < c * ρ → χ δ = 1)
    (hSc : Continuous (fun p : E × E ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ∀ k, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      complementaryAmplitude (A k) ζ ρ χ p.1.1 p.1.2 p.2))
    {Ks Kt : Set E} {Kη : ℕ → Set E} (hKs : IsCompact Ks)
    (hKt : IsCompact Kt) (hKη : ∀ k, IsCompact (Kη k))
    (ht : ∀ k x y η, x ∉ Kt → complementaryAmplitude (A k) ζ ρ χ x y η = 0)
    (hf : ∀ k x y η, η ∉ Kη k → complementaryAmplitude (A k) ζ ρ χ x y η = 0)
    (hs : ∀ k η z y, y ∉ Ks → complementaryAmplitude (A k) ζ ρ χ z y η = 0)
    (hAj : ∀ k η (β : List (Fin n)) j z y,
      ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude (A k) ζ ρ χ v w η) z) y‖ ≤
        C β.length j * a * L ^ (b + β.length + j))
    (hSj : ∀ η j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ S w η) z‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j φ z‖ ≤ Pφ j * L ^ (j - 1))
    (f : H) (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0)
    (T : H →L[ℂ] H) (u : ℕ → H)
    (hreal : ∀ k, (u k : E → EuclideanSpace ℂ (Fin r)) =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (forwardDemodulatedGraph S φ (complementaryAmplitude (A k) ζ ρ χ)
        ζ ρ (fun y ↦ ⇑(f y)) x))
    (hlim : Tendsto u atTop (𝓝 (T f))) :
    MemVectorFourierSobolev (s : ℝ) (T f) ∧
      vectorFourierSobolevNorm (s : ℝ) (T f) ≤
        (r : ℝ) * lowEnvelopeSobolevConstant n r Ks Kt (forwardGapConstant c Z)
          (1 + Z + c / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C s q *
          a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ := by
  have hr (k : ℕ) (i : Fin r) :
      (finiteL2CoordinateIsometry volume (u k) i : E → ℂ) =ᵐ[volume]
        fun x ↦ forwardDemodulatedGraph S φ (complementaryAmplitude (A k) ζ ρ χ)
          ζ ρ (fun y ↦ ⇑(f y)) x i :=
    (finiteL2CoordinateIsometry_ae_iff volume (u k) _).mp (hreal k) i
  have hl (i : Fin r) :
      Tendsto (fun k ↦ finiteL2CoordinateIsometry volume (u k) i) atTop
        (𝓝 (finiteL2CoordinateIsometry volume (T f) i)) := by
    have hcont : Continuous (fun v : H ↦ finiteL2CoordinateIsometry volume v i) :=
      (PiLp.continuous_apply 2 _ i).comp (finiteL2CoordinateIsometry volume).continuous
    exact (hcont.tendsto (T f)).comp hlim
  obtain ⟨hmem, hbound⟩ := forwardComplement_lowSupport_sobolev_of_tendsto
    S φ A χ ζ s q b C PS Pφ hC hPS hPφ hc ha hL hLρ hΛ hΛρ hζ hχ
    hSc hS hφ hA hKs hKt hKη ht hf hs hAj hSj hφj f hfs
    (fun k i ↦ finiteL2CoordinateIsometry volume (u k) i)
    (fun i ↦ finiteL2CoordinateIsometry volume (T f) i) hr hl
  refine ⟨hmem, (matrixFourierSobolevNorm_le_sum _ _).trans ?_⟩
  calc
    _ ≤ ∑ _ : Fin r, lowEnvelopeSobolevConstant n r Ks Kt (forwardGapConstant c Z)
        (1 + Z + c / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C s q *
        a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ :=
      Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = _ := by simp [mul_assoc]

end JanetCartan.ResponseTransfer.Complement
