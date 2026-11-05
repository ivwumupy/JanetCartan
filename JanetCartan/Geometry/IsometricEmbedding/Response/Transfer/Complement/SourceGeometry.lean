module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ReverseGap
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.ReversePhase

/-!
# Source geometry for the literal complete complement

The complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`. These deductions connect the
buffered inverse-chart estimates to the derivative-map gap consumed by the
source integration-by-parts theorem. All original amplitude supports, including
selector shoulders, are retained. The geometric hypotheses are obligations of
`jc-compatible-phase-geometry`; they concern the entire active chart.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.Complement

open FourierIntegral

variable {n r : ℕ}

/-- Riesz identification preserves the exact reverse source-gap norm. This
connects `reverseSource_gap_uniform` to the integration-by-parts consumer in
`app:ch_response:thm:response-literal-transfer`, without changing covectors. -/
theorem norm_reverseSource_fderiv_eq (S : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → ℝ) (ρ : ℝ) (x η : Euclidean n) :
    ‖ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x‖ =
      ‖ρ • gradient φ x - gradient (fun z ↦ S z η) x‖ := by
  simpa only [map_sub, map_smul, toDual_gradient] using
    (InnerProductSpace.toDual ℝ (Euclidean n)).norm_map
      (ρ • gradient φ x - gradient (fun z ↦ S z η) x)

/-- The full inverse-chart geometry gives the gap on every nonzero part of
the actual complementary amplitude, uniformly before the amplitude, selector,
frequency and carrier are chosen. No support is projected away. The open set
used for integration by parts can be taken as `K` here; its closure need not
be compact for this geometric deduction.
Source: `app:ch_response:thm:response-literal-transfer`.

The producer must prove the annular and inverse estimates on all of `D`,
including its radial/angular shoulders. Local invertibility alone is insufficient.
-/
theorem reverseComplement_sourceGap_uniform {I : Type*}
    (S : I → Euclidean n → Euclidean n → ℝ)
    {P : Set I} {K U Z D : Set (Euclidean n)}
    (hU : IsOpen U) (hKU : K ⊆ U) (hZ : IsCompact Z)
    (hZ0 : ∀ ζ ∈ Z, ζ ≠ 0) (hZD : Z ⊆ D)
    (hcone : ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ → ρ • η ∈ D)
    (hS : ∀ p ∈ P, ∀ η ∈ D, DifferentiableOn ℝ (fun x ↦ S p x η) U)
    (hhom : ∀ p ∈ P, ∀ x ∈ U, ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ →
      S p x (ρ • η) = ρ * S p x η)
    {m M B c : ℝ} (hm : 0 < m) (hM : 0 < M) (hB : 0 < B) (hc : 0 < c)
    (hannular : ∀ p ∈ P, ∀ x ∈ K, ∀ η ∈ D,
      m * ‖η‖ ≤ ‖gradient (fun y ↦ S p y η) x‖ ∧
      ‖gradient (fun y ↦ S p y η) x‖ ≤ M * ‖η‖)
    (hinverse : ∀ p ∈ P, ∀ x ∈ K, ∀ u ∈ D, ∀ v ∈ D,
      ‖u - v‖ ≤ B * ‖gradient (fun y ↦ S p y u) x -
        gradient (fun y ↦ S p y v) x‖) :
    ∃ d > 0, ∀ p ∈ P, ∀ ζ ∈ Z, ∀ ρ : ℝ, 0 < ρ →
      ∀ χ : Euclidean n → ℂ, (∀ δ, ‖δ‖ < c * ρ → χ δ = 1) →
      ∀ A : FullAmplitude n r, (∀ y x η, η ∉ D → A y x η = 0) →
      ∀ η, (∃ y x, complementaryAmplitude A ζ ρ χ y x η ≠ 0) →
      ∀ x ∈ K,
        d * (ρ + ‖η‖) ≤
          ‖ρ • fderiv ℝ (fun z ↦ S p z ζ) x - fderiv ℝ (fun z ↦ S p z η) x‖ := by
  obtain ⟨d, hd, ε, hε, hgap⟩ := reverseSource_gap_uniform S hU hKU hZ hZ0 hZD
    hcone hS hhom hm hM hB hc hannular hinverse
  refine ⟨d, hd, ?_⟩
  intro p hp ζ hζ ρ hρ χ hχ A hA η hnonzero x hx
  obtain ⟨y, z, hz⟩ := hnonzero
  have hη : η ∈ D := by
    by_contra hnot
    exact hz (by simp [complementaryAmplitude, hA y z η hnot])
  have hfar : c * ρ ≤ ‖η - ρ • ζ‖ :=
    tsupport_complementaryAmplitude_subset_far A ζ ρ c χ hχ y z
      (subset_closure hz)
  rw [norm_reverseSource_fderiv_eq]
  simpa only [add_zero] using
    hgap p hp x hx ζ hζ η hη ρ hρ 0 hfar
      (by simpa only [norm_zero] using (mul_pos hε hρ).le)

/-- Choose the internal low-envelope cutoff small enough that its entire
outer shoulder lies within the perturbation allowed by the source gap, for
every `ρ ≥ 1`. Thus even a cutoff radius below one is handled without deleting
bounded frequencies. Source: `app:ch_response:thm:response-literal-transfer`.
The high-envelope leaf already proves its bound at every positive radius. -/
theorem farEnvelope_outerRadius_le {ρ ν c R d : ℝ}
    (hρ : 1 ≤ ρ) (hν : 0 ≤ ν) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hscale : R * c ≤ d / 2) :
    R * (c * ρ ^ (1 - ν / 2)) ≤ d * ρ / 2 := by
  have hp : ρ ^ (1 - ν / 2) ≤ ρ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hρ (show 1 - ν / 2 ≤ 1 by linarith)
  calc
    _ = (R * c) * ρ ^ (1 - ν / 2) := by ring
    _ ≤ (R * c) * ρ := mul_le_mul_of_nonneg_left hp (mul_nonneg hR hc)
    _ ≤ (d / 2) * ρ := mul_le_mul_of_nonneg_right hscale (zero_le_one.trans hρ)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.Complement
