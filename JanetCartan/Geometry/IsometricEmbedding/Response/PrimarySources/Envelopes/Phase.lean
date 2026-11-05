module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Bounds

/-!
# Source geometry for the same retained primary phase

`exists_retainedPhase_sourceGeometry` constructs every analytic field of
`SourceNegative.SourceGeometry` for the original source cutoff and the
cutoff extension of the literal `FullModulation.phase T Q x ζ`.
The fixed compact parameter set contains the supplied full shifted-carrier
buffer, with the original `(z, ζ)` labels. Its product with the **entire**
source support must lie in the original retained phase domain; no smaller
source cutoff, carrier family, or working ball is selected.

The parent supplies that geometric containment, smooth compact source cutoff,
primitive immersion regularity, metric and normal gaps, low norm budget,
frame closeness to the produced positive threshold, and `HasDerivativeProfile`.
The original reserve `14 + (rpar + 2)` is sufficient. The phase is independent
of the initial scalar, so no additional scalar reserve or scalar input is used.
Constants and the extension cutoff are selected before the current immersion,
frame, carrier and slow scale. Final application to the full strain and its
negative Sobolev norm belongs to the primary-source envelope consumer.

Sources: `app:ch_response:thm:response-literal-transfer`,
`app:ch_response:prop:response-graded`, `app:ch_response:cor:current-atoms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponsePrimarySources
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame ResponseTransfer SourceNegative ResponseSourceExtension

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the source geometry for the SAME full primary phase from the
fixed source support, retained parameter compact and primitive immersion
profile. All bounds hold on `tsupport χsrc`, including its boundary and the
entire shifted-carrier buffer. No phase estimate is an input
(`app:ch_response:prop:response-graded`, `app:ch_response:cor:current-atoms`). -/
theorem exists_retainedPhase_sourceGeometry {N : ℕ}
    {χsrc : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χsrc) (hcχ : HasCompactSupport χsrc)
    {C : Set (Euclidean 3 × Euclidean (n - 1))} (hC : IsCompact C)
    (hsource : tsupport χsrc ×ˢ C ⊆ domain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) :
    ∃ (θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
      (a G δ : ℝ) (B X : ℕ → ℝ),
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ domain T ∧
      tsupport χsrc ×ˢ C ⊆ interior {w | θ w = 1} ∧
      0 < a ∧ a < G ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
      (∀ j, 0 ≤ B j) ∧ (∀ j, 0 ≤ X j) ∧
      (∀ Q, ContDiff ℝ ∞ (Function.uncurry (retainedPhaseExtension T Q θ)) ∧
        ∀ c ∈ C, ∀ x ∈ tsupport χsrc,
          (fun y ↦ retainedPhaseExtension T Q θ y c) =ᶠ[𝓝 x]
            (fun y ↦ phase T Q y c.2)) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K 4 F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∀ (RF rpar : ℕ) (L : ℝ), 1 ≤ L → 14 + (rpar + 2) ≤ RF →
      HasDerivativeProfile K F RF L AF → ∀ c ∈ C,
      SourceGeometry χsrc (fun x ↦ retainedPhaseExtension T Q θ x c)
        (tsupport χsrc) a G L B X := by
  have hJ : IsCompact (tsupport χsrc ×ˢ C) := hcχ.prod hC
  obtain ⟨θ, hθ, _, hcθ, hsθ, hpθ⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hJ (isOpen_domain T) hsource
  obtain ⟨a, G, δ, ha, haG, hδ, hδT, hgap⟩ :=
    exists_fullPhase_differential_bounds T hJ hsource
  obtain ⟨B, hB, hgrade⟩ := exists_fullPhase_physical_grades
    (N := N) T hJ hsource hK hKU hball M hγ hκ AF hAF
  choose X hX hXbound using fun j ↦ hcχ.exists_bound_iteratedFDeriv hχ j
  refine ⟨θ, a, G, δ, B, X, hθ, hcθ, hsθ, hpθ, ha, haG, hδ, hδT,
    fun j ↦ (hB j).le, hX, ?_, ?_⟩
  · intro Q
    exact ⟨contDiff_retainedPhaseExtension T Q hθ hsθ,
      fun c hc x hx ↦ retainedPhaseExtension_physical_eventuallyEq T Q (hpθ ⟨hx, hc⟩)⟩
  · intro F hF hi hrank hFM hmetric hnormal hlow Q hclose RF rpar L hL hRF hprofile c hc
    refine {
      cutoff_smooth := hχ
      phase_smooth := (contDiff_retainedPhaseExtension T Q hθ hsθ).comp
        (contDiff_id.prodMk contDiff_const)
      compact := hcχ
      support_subset := Subset.rfl
      lower_pos := ha
      lower_lt_upper := haG
      scale_one_le := hL
      phase_constants_nonneg := fun j ↦ (hB j).le
      cutoff_constants_nonneg := hX
      gradient_lower := ?_
      gradient_upper := ?_
      phase_derivatives := ?_
      cutoff_derivatives := ?_ }
    · intro x hx
      rw [fderiv_retainedPhaseExtension_eq T Q (hpθ ⟨hx, hc⟩)]
      exact (hgap Q hclose (x, c) ⟨hx, hc⟩).1
    · intro x hx
      rw [fderiv_retainedPhaseExtension_eq T Q (hpθ ⟨hx, hc⟩)]
      exact (hgap Q hclose (x, c) ⟨hx, hc⟩).2
    · intro x hx j _
      rw [iteratedFDeriv_retainedPhaseExtension_eq T Q (hpθ ⟨hx, hc⟩)]
      exact hgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hprofile
        (x, c) ⟨hx, hc⟩ j
    · intro x j
      exact (hXbound j j le_rfl x).trans
        (le_mul_of_one_le_right (hX j) (one_le_pow₀ hL))

/-- Instantiate the parent's exact remodulation identity with the constructed
phase cutoff. Only its geometric plateau is required; phase agreement is proved
here on the complete original source support
(`app:ch_response:cor:current-atoms`). -/
theorem cutoff_fullPrimaryStrain_eq_modulatedSource_retainedPhase {N : ℕ}
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart)
    (χsrc : Euclidean n → ℝ) (hs : tsupport χsrc ⊆ core)
    (θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    {C : Set (Euclidean 3 × Euclidean (n - 1))}
    (hplateau : tsupport χsrc ×ˢ C ⊆ interior {w | θ w = 1})
    (τ : ℝ) {c : Euclidean 3 × Euclidean (n - 1)} (hc : c ∈ C) :
    (fun x ↦ χsrc x • WKB.complexLinearizedMetric F
      (fun y ↦ RawPrimary.fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2)) x) =
      modulatedSource χsrc (fun y ↦ retainedPhaseExtension T Q θ y c)
        (fullStrainEnvelope T Q F row col Φ Y r χ τ c) τ⁻¹ := by
  apply cutoff_fullPrimaryStrain_eq_modulatedSource_of_phase_eq T Q F row col Φ Y r χ
    χsrc _ hs τ c
  intro x hx
  exact (retainedPhaseExtension_physical_eventuallyEq T Q (hplateau ⟨hx, hc⟩)).self_of_nhds

end JanetCartan.ResponsePrimarySources
