module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.SourceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.Regularization
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Low-envelope reverse complement from buffered geometry

For `app:ch_response:thm:response-literal-transfer`, the inverse-chart gap is
proved before applying the low-envelope theorem. The output is the supplied
operator's actual L² limit and has the existing vector Fourier Sobolev norm.
Both physical positions and the complete complementary amplitude remain literal.

The finite calculus supplies regularizations, convergence to the same operator,
and primitive amplitude/phase grades. Compatible phase geometry supplies the
full chart hypotheses. Neither a low-envelope bound nor a complementary decay
estimate is an assumption.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement

open FourierIntegral NormalComparison Pseudodifferential LowEnvelope

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The low-envelope reverse estimate with its gap discharged from the full
buffered inverse chart. The positive gap `d` and carrier bound `Z₀` precede all
frequencies, envelopes, amplitudes, proof orders and regularizations. The fixed
loss is `b+s+n`, independent of the integration order `q`.

`T` is the demodulated complete reverse factor; `hreal` and `hlim` identify its
action with the literal regularizations. For the paper coordinate inverse take
the original amplitudes to be `reverseFullAmplitude`, which retains `j_S U⁻¹`
and all physical cutoffs. It is not identified with an unweighted adjoint.
Source: `app:ch_response:thm:response-literal-transfer`.
-/
theorem reverseComplement_lowSupport_of_geometry {I : Type*}
    (S : I → E → E → ℝ) {P : Set I} {Ω U Z D : Set E}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hΩU : Ω ⊆ U) (hZ : IsCompact Z)
    (hZ0 : ∀ ζ ∈ Z, ζ ≠ 0) (hZD : Z ⊆ D)
    (hcone : ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ → ρ • η ∈ D)
    (hSdiff : ∀ p ∈ P, ∀ η ∈ D, DifferentiableOn ℝ (fun x ↦ S p x η) U)
    (hhom : ∀ p ∈ P, ∀ x ∈ U, ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ →
      S p x (ρ • η) = ρ * S p x η)
    {m M B c : ℝ} (hm : 0 < m) (hM : 0 < M) (hB : 0 < B) (hc : 0 < c)
    (hannular : ∀ p ∈ P, ∀ x ∈ Ω, ∀ η ∈ D,
      m * ‖η‖ ≤ ‖gradient (fun y ↦ S p y η) x‖ ∧
      ‖gradient (fun y ↦ S p y η) x‖ ≤ M * ‖η‖)
    (hinverse : ∀ p ∈ P, ∀ x ∈ Ω, ∀ u ∈ D, ∀ v ∈ D,
      ‖u - v‖ ≤ B * ‖gradient (fun y ↦ S p y u) x -
        gradient (fun y ↦ S p y v) x‖) :
    ∃ d > 0, ∃ Z₀ > 0, ∀ p ∈ P, ∀ ζ ∈ Z,
      ∀ (A : ℕ → FullAmplitude n r) (χ : E → ℂ)
        (s q b : ℕ) (C : ℕ → ℕ → ℝ) (PS : ℕ → ℝ),
      (∀ j k, 0 ≤ C j k) → (∀ j, 0 ≤ PS j) →
      ∀ a L ρ Λ : ℝ, 0 ≤ a → 1 ≤ L → L ≤ ρ → 0 ≤ Λ → Λ ≤ d * ρ / 2 →
      (∀ δ, ‖δ‖ < c * ρ → χ δ = 1) →
      Continuous (fun z : E × E ↦ S p z.1 z.2) →
      (∀ η, ContDiff ℝ ∞ (fun z ↦ S p z η)) →
      (∀ k, ContDiff ℝ ∞ (fun z : (E × E) × E ↦
        complementaryAmplitude (A k) ζ ρ χ z.1.1 z.1.2 z.2)) →
      ∀ (Ks Kt : Set E) (Kη : ℕ → Set E),
      IsCompact Ks → Ks ⊆ Ω → IsCompact Kt → (∀ k, IsCompact (Kη k)) →
      (∀ k y x η, y ∉ Kt → complementaryAmplitude (A k) ζ ρ χ y x η = 0) →
      (∀ k y x η, η ∉ Kη k → complementaryAmplitude (A k) ζ ρ χ y x η = 0) →
      (∀ k η y x, x ∉ Ks → complementaryAmplitude (A k) ζ ρ χ y x η = 0) →
      (∀ k y x η, η ∉ D → A k y x η = 0) →
      (∀ k η (β : List (Fin n)) j y x,
        ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β
          (fun v ↦ complementaryAmplitude (A k) ζ ρ χ v w η) y) x‖ ≤
          C β.length j * a * L ^ (b + β.length + j)) →
      (∀ η j, 1 ≤ j → ∀ x,
        ‖iteratedFDeriv ℝ j (fun z ↦ S p z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1)) →
      ∀ (f : H), (∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) →
      ∀ (T : H →L[ℂ] H) (u : ℕ → H),
      (∀ k, (u k : E → EuclideanSpace ℂ (Fin r)) =ᵐ[volume] fun y ↦
        WithLp.toLp 2 (reverseDemodulatedGraph (S p) (fun z ↦ S p z ζ)
          (complementaryAmplitude (A k) ζ ρ χ) ζ ρ (fun x ↦ ⇑(f x)) y)) →
      Tendsto u atTop (𝓝 (T f)) →
      MemVectorFourierSobolev (s : ℝ) (T f) ∧
        vectorFourierSobolevNorm (s : ℝ) (T f) ≤
          (r : ℝ) * lowEnvelopeSobolevConstant n r Ks Kt (d / 2)
            (PS 1 + PS 1 * Z₀ + d / 2)
            (fun j ↦ PS (j + 1) + PS (j + 1) * Z₀) (fun _ ↦ 1 + Z₀) C s q *
            a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ := by
  obtain ⟨d, hd, hgap⟩ := reverseComplement_sourceGap_uniform (r := r) S hU hΩU hZ
    hZ0 hZD hcone hSdiff hhom hm hM hB hc hannular hinverse
  obtain ⟨Z₀, hZ₀, hζbound⟩ := hZ.isBounded.exists_pos_norm_le
  refine ⟨d, hd, Z₀, hZ₀, ?_⟩
  intro p hp ζ hζ A χ s q b C PS hC hPS a L ρ Λ ha hL hLρ hΛ hΛρ
    hχ hSc hS hA Ks Kt Kη hKs hKsΩ hKt hKη ht hf hs hD hAj hSj f hfs T u hreal hlim
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hφj (j : ℕ) (hj : 1 ≤ j) (x : E) :
      ‖iteratedFDeriv ℝ j (fun z ↦ S p z ζ) x‖ ≤
        (PS j * Z₀) * L ^ (j - 1) := by
    exact (hSj ζ j hj x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hζbound ζ hζ) (hPS j))
      (pow_nonneg (zero_le_one.trans hL) _))
  have hr (k : ℕ) (i : Fin r) :
      (finiteL2CoordinateIsometry volume (u k) i : E → ℂ) =ᵐ[volume]
        fun y ↦ reverseDemodulatedGraph (S p) (fun z ↦ S p z ζ)
          (complementaryAmplitude (A k) ζ ρ χ) ζ ρ (fun x ↦ ⇑(f x)) y i :=
    (finiteL2CoordinateIsometry_ae_iff volume (u k) _).mp (hreal k) i
  have hl (i : Fin r) :
      Tendsto (fun k ↦ finiteL2CoordinateIsometry volume (u k) i) atTop
        (𝓝 (finiteL2CoordinateIsometry volume (T f) i)) := by
    have hcont : Continuous (fun v : H ↦ finiteL2CoordinateIsometry volume v i) :=
      (PiLp.continuous_apply 2 _ i).comp (finiteL2CoordinateIsometry volume).continuous
    exact (hcont.tendsto (T f)).comp hlim
  obtain ⟨hmem, hbound⟩ := reverse_lowSupport_sobolev_of_tendsto hΩ hKs hKsΩ
    (S p) (fun z ↦ S p z ζ) (fun k ↦ complementaryAmplitude (A k) ζ ρ χ)
    ζ s q b C PS (fun j ↦ PS j * Z₀) hC hPS (fun j ↦ mul_nonneg (hPS j) hZ₀.le)
    hd ha hL hLρ hΛ (hζbound ζ hζ) hΛρ hSc hS (hS ζ) hA hKt hKη ht hf hs
    (fun k ↦ hgap p hp ζ hζ ρ hρ χ hχ (A k) (hD k)) hAj hSj hφj
    f hfs (fun k i ↦ finiteL2CoordinateIsometry volume (u k) i)
    (fun i ↦ finiteL2CoordinateIsometry volume (T f) i) hr hl
  refine ⟨hmem, (matrixFourierSobolevNorm_le_sum _ _).trans ?_⟩
  calc
    _ ≤ ∑ _ : Fin r, lowEnvelopeSobolevConstant n r Ks Kt (d / 2)
        (PS 1 + PS 1 * Z₀ + d / 2)
        (fun j ↦ PS (j + 1) + PS (j + 1) * Z₀) (fun _ ↦ 1 + Z₀) C s q *
        a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ :=
      Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = _ := by simp [mul_assoc]

end JanetCartan.ResponseTransfer.Complement
