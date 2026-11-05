module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.ChartGrades
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.ParameterJets

/-!
# Fixed profiles from primitive original-chart jets

All constants below are chosen before the phase, WKB amplitude, history scale,
and requested order. No bound for a differentiated amplitude is an input.
This is the original-chart producer of the joint grades used in the proof of
`app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open FourierIntegral.NormalOneHigh

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Construct uniform rescaled profiles from the fixed masks and primitive
original-chart profiles. The order `N` is arbitrary and finite. For an order
`s` slice estimate take `N=s+M+1`: amplitude jets through `N` and covector
differential jets through `N` (hence phase jets through `N+1`) suffice.
The original WKB/coefficient construction remains responsible for these
primitive bounds; no chart-bound or successful-channel premise is assumed
(`app:ch_waves:thm:wkb`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSliceOriginalChart_profiles
    {U : Set X} {V Ω : Set P} {Q K : Set (ℝ × X × P)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (ζ : P) (χ : X → ℝ) (m : P → ℂ)
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ m Ω)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    ∃ a' p' : ℕ → ℝ, (∀ j, 0 ≤ a' j) ∧ (∀ j, 0 ≤ p' j) ∧
      ∀ (S : X → P → ℝ) (A : X → P → F),
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      ∀ (N R : ℕ) (L : ℝ), 1 ≤ L →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (Function.uncurry A) z‖ ≤ a j * L ^ (j - R)) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (fun w : X × P ↦ fderiv ℝ (S w.1) w.2) z‖ ≤
          p j * L ^ (j - 1 - R)) →
      ∀ q ∈ K, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (rawSliceAmplitudeExtension A χ m ζ) q‖ ≤ a' k * L ^ (k - R) ∧
        ‖iteratedFDeriv ℝ k (rawSlicePhaseExtension S ζ) q‖ ≤ p' k * L ^ (k - 1 - R) := by
  obtain ⟨c, hc, hmap⟩ := exists_rawSliceShift_jetBounds ζ hK
  let mask : ℝ × X × P → ℂ := fun q ↦ (χ q.2.1 : ℂ) * m q.2.2
  let proj : ℝ × X × P → P := fun q ↦ q.2.2
  have hmask : ContDiffOn ℝ ∞ mask Q :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hχ.comp contDiffOn_snd.fst (fun q hq ↦ (hshift 1 (hIW (by simp)) hq).1))).mul
      (hm.comp contDiffOn_snd.snd hθ)
  let b : ℕ → ℝ := fun k ↦ cNorm K k mask
  let e : ℕ → ℝ := fun k ↦ cNorm K k proj
  have hb (j : ℕ) : 0 ≤ b j := cNorm_nonneg _ _ _
  have he (j : ℕ) : 0 ≤ e j := cNorm_nonneg _ _ _
  refine ⟨sliceMaskJetConstant b (compositionBudget a c),
    sliceMaskJetConstant (compositionBudget p c) e,
    sliceMaskJetConstant_nonneg hb (compositionBudget_nonneg ha hc),
    sliceMaskJetConstant_nonneg (compositionBudget_nonneg hp hc) he, ?_⟩
  intro S A hS hA N R L hL hAj hDj q hq k hk
  constructor
  · exact norm_iteratedFDeriv_rawSliceAmplitudeExtension_le hU hV hQ hA hχ hm
      (hshift 1 (hIW (by simp))) hθ (hKQ hq) hL ha hc hb
      (fun j hj ↦ hAj _ (hshift 1 (hIW (by simp)) (hKQ hq)) j (hj.trans hk))
      (fun j _ _ ↦ hmap 1 (by simp) q hq j)
      (fun j _ ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun y hy ↦ (hmask.contDiffAt (hQ.mem_nhds (hKQ hy))).of_le (by simp)) hq le_rfl)
  · exact norm_iteratedFDeriv_rawSlicePhaseExtension_le hU hV hQ hW hIW hS hshift
      (hKQ hq) hL hp hc he
      (fun t ht j hj ↦ hDj _ (hshift t (hIW ht) (hKQ hq)) j (hj.trans hk))
      (fun t ht j _ _ ↦ hmap t ht q hq j)
      (fun j _ ↦ norm_iteratedFDeriv_le_cNorm hK (by fun_prop) hq le_rfl)

/-- Original joint grades through the finite orders `s+M+1` construct the
normalized branch bounds. The reserve is exactly `Dpr+r_par+2`, independently
of `s`. Taking `L=1` gives the bounded-finite-jet alternative with the SAME
amplitudes. The phase needs one additional covector derivative; a concrete
coefficient producer certified to use orders through `k+Dpr` must supply
coefficient/initial-data orders through `s+M+2+Dpr`.
This theorem does not assume or assert that coefficient-production step
(`app:ch_waves:thm:wkb`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_normalizedRawSliceBranch_profiles
    {U : Set X} {V Ω : Set P} {Q K : Set (ℝ × X × P)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (ζ : P) (χ : X → ℝ) (m : P → ℂ)
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ m Ω)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    ∃ a' p' : ℕ → ℝ, (∀ j, 0 ≤ a' j) ∧ (∀ j, 0 ≤ p' j) ∧
      ∀ (S : X → P → ℝ) (A : X → P → F),
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      ∀ (n Dpr s : ℕ) (L : ℝ), 1 ≤ L →
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
  obtain ⟨a', p', ha', hp', hprofiles⟩ := exists_rawSliceOriginalChart_profiles
    (F := F) hU hV hQ hW hIW hK hKQ ζ χ m hχ hm hshift hθ a p ha hp
  refine ⟨a', p', ha', hp', ?_⟩
  intro S A hS hA n Dpr s L hL hAj hDj v hv b q hq k hk
  have hgrades := hprofiles S A hS hA (s + rawSliceJetOrder n + 1)
    (rawSliceParameterOrder n + 2) L hL
    (fun z hz j hj ↦ by simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left,
      ← Nat.sub_sub] using hAj z hz j hj)
    (fun z hz j hj ↦ by simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left,
      ← Nat.sub_sub] using hDj z hz j hj)
  apply norm_iteratedFDeriv_normalizedSliceDerivativeAmplitude_le
    (Dpr := Dpr) hQ (contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift)
    (contDiffOn_rawSliceAmplitudeExtension hA hχ hm (hshift 1 (hIW (by simp))) hθ)
    hk v b hv hL (fun j _ ↦ ha' j) (fun j _ _ ↦ hp' j) (hKQ hq)
  · intro j hj
    simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left, ← Nat.sub_sub] using
      (hgrades q hq j (by omega)).1
  · intro j _ hj
    simpa [rawSlicePrimitiveReserve, Nat.add_sub_add_left, ← Nat.sub_sub] using
      (hgrades q hq j (by omega)).2

end JanetCartan.RawPrimary.SliceBounds
