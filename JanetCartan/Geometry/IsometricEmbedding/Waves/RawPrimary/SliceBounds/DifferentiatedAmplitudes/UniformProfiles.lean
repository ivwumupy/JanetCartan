module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.OriginalProfiles

/-!
# Uniformity over the original rescaled annular masks

The masks in `app:ch_waves:eq:individual-raw-slice` have a common rescaled
seminorm profile. Choosing the branch constants before those masks permits
the SAME constants to be used for every original dyadic band. The new premise
is only a fixed-mask jet bound, not a bound for any WKB or differentiated
amplitude. The phase and WKB amplitude are still controlled on their original
buffered charts.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open FourierIntegral.NormalOneHigh

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Uniform branch profiles are chosen before the original cutoffs, annular
masks, phase, amplitude, physical order, and scale. Only their common finite
primitive mask profile is used. Every additional slice/epsilon jet is derived
with the fixed manuscript reserve. The concrete mask in the consumer is
`m θ = sqrt ‖θ‖ * β (2^j • θ)`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_normalizedRawSliceBranch_uniformProfiles
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
      ∀ (n Dpr s : ℕ) (L : ℝ), 1 ≤ L →
      (∀ q ∈ K, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (fun z : ℝ × X × P ↦ (χ z.2.1 : ℂ) * m z.2.2) q‖ ≤ bmask j) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (Function.uncurry A) z‖ ≤
          a j * L ^ (j + Dpr - rawSlicePrimitiveReserve n Dpr)) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (fun w : X × P ↦ fderiv ℝ (S w.1) w.2) z‖ ≤
          p j * L ^ (j - 1 + Dpr - rawSlicePrimitiveReserve n Dpr)) →
      ∀ (v : Fin s → ℝ × X × P), (∀ i, ‖v i‖ ≤ 1) →
      ∀ b : SliceDerivativeBranch s, ∀ q ∈ K, ∀ k ≤ rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ k (normalizedSliceDerivativeAmplitude
          (rawSlicePhaseExtension S ζ) (rawSliceAmplitudeExtension A χ m ζ) v b L) q‖ ≤
            sliceDerivativeJetConstant a' p' b k := by
  obtain ⟨c, hc, hmap⟩ := exists_rawSliceShift_jetBounds ζ hK
  let e : ℕ → ℝ := fun k ↦ cNorm K k (fun q : ℝ × X × P ↦ q.2.2)
  have he (j : ℕ) : 0 ≤ e j := cNorm_nonneg _ _ _
  let a' := sliceMaskJetConstant bmask (compositionBudget a c)
  let p' := sliceMaskJetConstant (compositionBudget p c) e
  have ha' : ∀ j, 0 ≤ a' j := sliceMaskJetConstant_nonneg hbmask (compositionBudget_nonneg ha hc)
  have hp' : ∀ j, 0 ≤ p' j := sliceMaskJetConstant_nonneg (compositionBudget_nonneg hp hc) he
  refine ⟨a', p', ha', hp', ?_⟩
  intro χ m S A hχ hm hS hA n Dpr s L hL hmask hAj hDj v hv b q hq k hk
  have hAmp (j : ℕ) (hj : j ≤ s + k) :
      ‖iteratedFDeriv ℝ j (rawSliceAmplitudeExtension A χ m ζ) q‖ ≤
        a' j * L ^ (j + Dpr - rawSlicePrimitiveReserve n Dpr) := by
    have hh := norm_iteratedFDeriv_rawSliceAmplitudeExtension_le
      (k := j) (R := rawSliceParameterOrder n + 2) hU hV hQ hA hχ hm
      (hshift 1 (hIW (by simp))) hθ (hKQ hq) hL ha hc hbmask
      (fun i hi ↦ by simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left,
        ← Nat.sub_sub] using hAj _ (hshift 1 (hIW (by simp)) (hKQ hq)) i (by omega))
      (fun i _ _ ↦ hmap 1 (by simp) q hq i)
      (fun i hi ↦ hmask q hq i (by omega))
    simpa [a', rawSlicePrimitiveReserve, Nat.add_sub_add_left, ← Nat.sub_sub] using hh
  have hPhase (j : ℕ) (hj : j ≤ s + k) :
      ‖iteratedFDeriv ℝ j (rawSlicePhaseExtension S ζ) q‖ ≤
        p' j * L ^ (j - 1 + Dpr - rawSlicePrimitiveReserve n Dpr) := by
    have hh := norm_iteratedFDeriv_rawSlicePhaseExtension_le
      (k := j) (R := rawSliceParameterOrder n + 2) hU hV hQ hW hIW hS hshift
      (hKQ hq) hL hp hc he
      (fun t ht i hi ↦ by simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left,
        ← Nat.sub_sub] using hDj _ (hshift t (hIW ht) (hKQ hq)) i (by omega))
      (fun t ht i _ _ ↦ hmap t ht q hq i)
      (fun i _ ↦ norm_iteratedFDeriv_le_cNorm hK (by fun_prop) hq le_rfl)
    simpa [p', rawSlicePrimitiveReserve, Nat.add_sub_add_left, ← Nat.sub_sub] using hh
  exact norm_iteratedFDeriv_normalizedSliceDerivativeAmplitude_le
    (Dpr := Dpr) hQ (contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift)
    (contDiffOn_rawSliceAmplitudeExtension hA hχ hm (hshift 1 (hIW (by simp))) hθ)
    hk v b hv hL (fun j _ ↦ ha' j) (fun j _ _ ↦ hp' j) (hKQ hq)
    hAmp (fun j _ hj ↦ hPhase j hj)

end JanetCartan.RawPrimary.SliceBounds
