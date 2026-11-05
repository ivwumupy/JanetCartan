module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.UniformProfiles

/-!
# The bounded finite-jet alternative

At any prescribed physical order, bounded original jets allow `L=1` in
`app:ch_waves:eq:individual-raw-slice`. The derivative amplitudes remain the
literal ones. This is a separate specialization of the fixed-reserve proof;
it does not replace that reserve with an order-dependent low budget.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Bounded original amplitude and covector-differential jets through exactly
`s+M+1` control all slice jets and the additional epsilon derivative of the
actual branch. Equivalently, the primitive phase is used through order
`s+M+2`. Uniform rescaled-mask jets are required through `s+M+1`.
Coefficient/initial-data bounds must produce these stated primitive orders
with the actual WKB construction's fixed shifts; that instantiation belongs
to the raw-family parent (`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSliceBranch_boundedFiniteJets
    {U : Set X} {V Ω : Set P} {Q K : Set (ℝ × X × P)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (ζ : P) (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p bmask : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hbmask : ∀ j, 0 ≤ bmask j) :
    ∃ a' p' : ℕ → ℝ, (∀ j, 0 ≤ a' j) ∧ (∀ j, 0 ≤ p' j) ∧
      ∀ (χ : X → ℝ) (m : P → ℂ) (S : X → P → ℝ) (A : X → P → F),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ m Ω →
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      ∀ n s : ℕ,
      (∀ q ∈ K, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (fun z : ℝ × X × P ↦ (χ z.2.1 : ℂ) * m z.2.2) q‖ ≤ bmask j) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (Function.uncurry A) z‖ ≤ a j) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (fun w : X × P ↦ fderiv ℝ (S w.1) w.2) z‖ ≤ p j) →
      ∀ (v : Fin s → ℝ × X × P), (∀ i, ‖v i‖ ≤ 1) →
      ∀ b : SliceDerivativeBranch s, ∀ q ∈ K, ∀ k ≤ rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ k (sliceDerivativeAmplitude
          (rawSlicePhaseExtension S ζ) (rawSliceAmplitudeExtension A χ m ζ) v b) q‖ ≤
            sliceDerivativeJetConstant a' p' b k := by
  obtain ⟨a', p', ha', hp', h⟩ := exists_normalizedRawSliceBranch_uniformProfiles
    (F := F) hU hV hQ hW hIW hK hKQ ζ hshift hθ a p bmask ha hp hbmask
  refine ⟨a', p', ha', hp', ?_⟩
  intro χ m S A hχ hm hS hA n s hmask hAj hDj v hv b q hq k hk
  have hh := h χ m S A hχ hm hS hA n 0 s 1 le_rfl hmask
    (fun z hz j hj ↦ by simpa only [one_pow, mul_one] using hAj z hz j hj)
    (fun z hz j hj ↦ by simpa only [one_pow, mul_one] using hDj z hz j hj)
    v hv b q hq k hk
  change ‖iteratedFDeriv ℝ k (fun z ↦
    ((1 : ℝ) ^ (s - b.phaseCount))⁻¹ • sliceDerivativeAmplitude
      (rawSlicePhaseExtension S ζ) (rawSliceAmplitudeExtension A χ m ζ) v b z) q‖ ≤ _ at hh
  simpa only [one_pow, inv_one, one_smul] using hh

end JanetCartan.RawPrimary.SliceBounds
