module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.UniformProfiles

/-!
# Normalized branch profiles at the actual WKB reserve

The reconstruction and polynomial steps can spend the two extra derivatives in
the original corrected-family profiles. The remaining reserve `r_par=M+3`
still pays for all `M+1` joint jets required by the slice input. This is the
profile bridge for `exists_rawPhysicalSliceSobolev_wkbGrades`, implementing
`app:ch_waves:thm:wkb` and `app:ch_waves:eq:individual-raw-slice` for the SAME
amplitude. The original coefficient construction remains a parent obligation.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds

section Normalization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The baseline `r_par` alone bounds the required normalized branch jets.
The arbitrary-reserve branch estimate spends at most `k≤M+1≤r_par`, leaving
the exact factor `L^(s-phaseCount)` removed by the existing normalization.
Consumed by `exists_normalizedRawSliceBranch_uniformProfiles_parameterReserve`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_normalizedSliceDerivativeAmplitude_le_parameterReserve
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {A : E → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    {n s k : ℕ} (hk : k ≤ rawSliceJetOrder n + 1)
    (v : Fin s → E) (b : SliceDerivativeBranch s) (hv : ∀ i, ‖v i‖ ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) {a p : ℕ → ℝ}
    (ha : ∀ j ≤ s + k, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + k → 0 ≤ p j)
    {x : E} (hx : x ∈ U)
    (hAj : ∀ j ≤ s + k, ‖iteratedFDeriv ℝ j A x‖ ≤
      a j * L ^ (j - rawSliceParameterOrder n))
    (hφj : ∀ j, 1 ≤ j → j ≤ s + k → ‖iteratedFDeriv ℝ j φ x‖ ≤
      p j * L ^ (j - 1 - rawSliceParameterOrder n)) :
    ‖iteratedFDeriv ℝ k (normalizedSliceDerivativeAmplitude φ A v b L) x‖ ≤
      sliceDerivativeJetConstant a p b k := by
  have hb := norm_iteratedFDeriv_sliceDerivativeAmplitude_le hU hφ hA
    v b hv hL ha hp hx hAj hφj
  have hb' : ‖iteratedFDeriv ℝ k (sliceDerivativeAmplitude φ A v b) x‖ ≤
      sliceDerivativeJetConstant a p b k * L ^ (s - b.phaseCount) := by
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (sliceDerivativeJetConstant_nonneg b k ha hp)
    apply pow_le_pow_right₀ hL
    simp only [rawSliceParameterOrder] at *
    omega
  have hpos : 0 < L ^ (s - b.phaseCount) := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  have hs := contDiffOn_sliceDerivativeAmplitude hU hφ hA v b
  change ‖iteratedFDeriv ℝ k
    (fun y ↦ (L ^ (s - b.phaseCount))⁻¹ • sliceDerivativeAmplitude φ A v b y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((hs.contDiffAt (hU.mem_nhds hx)).of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  apply (mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hpos.le)).trans_eq
  field_simp

end Normalization

open FourierIntegral.NormalOneHigh

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Uniform normalized profiles from the remaining `r_par` WKB reserve,
with constants preceding the masks, actual fields, scales and physical order.
The arbitrary-reserve original-chart estimates preserve this baseline. This
feeds `exists_rawSlicePrimitiveBranchNormalData_wkbGrades`; no differentiated
bound is assumed (`app:ch_waves:thm:wkb`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_normalizedRawSliceBranch_uniformProfiles_parameterReserve
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
      ∀ (n s : ℕ) (L : ℝ), 1 ≤ L →
      (∀ q ∈ K, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (fun z : ℝ × X × P ↦ (χ z.2.1 : ℂ) * m z.2.2) q‖ ≤ bmask j) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (Function.uncurry A) z‖ ≤
          a j * L ^ (j - rawSliceParameterOrder n)) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder n + 1,
        ‖iteratedFDeriv ℝ j (fun w : X × P ↦ fderiv ℝ (S w.1) w.2) z‖ ≤
          p j * L ^ (j - 1 - rawSliceParameterOrder n)) →
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
  intro χ m S A hχ hm hS hA n s L hL hmask hAj hDj v hv b q hq k hk
  have hAmp (j : ℕ) (hj : j ≤ s + k) :
      ‖iteratedFDeriv ℝ j (rawSliceAmplitudeExtension A χ m ζ) q‖ ≤
        a' j * L ^ (j - rawSliceParameterOrder n) := by
    have hh := norm_iteratedFDeriv_rawSliceAmplitudeExtension_le
      (k := j) (R := rawSliceParameterOrder n) hU hV hQ hA hχ hm
      (hshift 1 (hIW (by simp))) hθ (hKQ hq) hL ha hc hbmask
      (fun i hi ↦ hAj _ (hshift 1 (hIW (by simp)) (hKQ hq)) i (by omega))
      (fun i _ _ ↦ hmap 1 (by simp) q hq i)
      (fun i hi ↦ hmask q hq i (by omega))
    exact hh
  have hPhase (j : ℕ) (hj : j ≤ s + k) :
      ‖iteratedFDeriv ℝ j (rawSlicePhaseExtension S ζ) q‖ ≤
        p' j * L ^ (j - 1 - rawSliceParameterOrder n) := by
    have hh := norm_iteratedFDeriv_rawSlicePhaseExtension_le
      (k := j) (R := rawSliceParameterOrder n) hU hV hQ hW hIW hS hshift
      (hKQ hq) hL hp hc he
      (fun t ht i hi ↦ hDj _ (hshift t (hIW ht) (hKQ hq)) i (by omega))
      (fun t ht i _ _ ↦ hmap t ht q hq i)
      (fun i _ ↦ norm_iteratedFDeriv_le_cNorm hK (by fun_prop) hq le_rfl)
    exact hh
  exact norm_iteratedFDeriv_normalizedSliceDerivativeAmplitude_le_parameterReserve
    hQ (contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift)
    (contDiffOn_rawSliceAmplitudeExtension hA hχ hm (hshift 1 (hIW (by simp))) hθ)
    hk v b hv hL (fun j _ ↦ ha' j) (fun j _ _ ↦ hp' j) (hKQ hq)
    hAmp (fun j _ hj ↦ hPhase j hj)

end JanetCartan.RawPrimary.SliceBounds
