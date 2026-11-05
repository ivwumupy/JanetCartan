module

public import JanetCartan.Iteration.PhysicalParameterRemainder.FullPhase

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.PhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.LocalJets
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization

/-!
# A single representative of the original full-source phase

The primary input to the complete envelope needs global smoothness but uses
jets only on the fixed physical/parameter carrier. Choose one cutoff before
the coefficient field and history, and use the original full-source history
bound on its plateau. Both spatial and parameter-first jets have that bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPrimary
open ActualCarriers ActualCarriers.CurrentFullPhase ResponseTransfer
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open ConstructedCarrierJets RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d

/-- One fixed primary cutoff for the original phase, followed by the history
threshold and profile. The cutoff equals one in a neighborhood of the entire
carrier, so the critical-map producer and both modulations use the same phase
on it. The history grade and reserve come from
`exists_admissible_history_full_source_phase_profiles`
(`app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_physical_history_fullSource_phase_representative (i : Fin (d + 1))
    {KP : Set (E × Par)} (hKP : IsCompact KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ χ : E × Par → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q ∈ KP, χ =ᶠ[𝓝 q] (fun _ ↦ 1)) ∧
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧ ∀ Q,
      let f := fun q : E × Par ↦ χ q * T.fullSourcePhaseInCoordinates i Q q.1 q.2
      ContDiff ℝ ∞ f ∧ (∀ q ∈ KP, f =ᶠ[𝓝 q] Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin n → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      Q.1 = extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u) →
      ∀ j q, q ∈ KP →
        ‖iteratedFDeriv ℝ j (fun p : Par × E ↦ f p.swap) q.swap‖ ≤
          A j * currentCoefficientScale R₀ n ^ (j - Rstar) ∧
        ‖iteratedFDeriv ℝ j (fun y ↦ f (y, q.2)) q.1‖ ≤
          A j * currentCoefficientScale R₀ n ^ (j - Rstar) := by
  let Ω := (fun q : E × Par ↦ ((primaryCoordinateChange i).symm q.1, q.2.2)) ⁻¹' phaseDomain T
  have hΩ : IsOpen Ω := isOpen_ball.preimage (((primaryCoordinateChange i).symm.continuous.comp
    continuous_fst).prodMk continuous_snd.snd)
  obtain ⟨χ, hχ, hcχ, hsχ, _, heχ⟩ := NormalComparison.exists_contDiff_localization
    hΩ hKP hKD (contDiff_const (c := (1 : ℝ))).contDiffOn
  obtain ⟨S, hS, A, hA, hb⟩ := T.exists_physical_history_full_source_phase_profiles
    i hKP hKD G hr hrR hR ext hextcenter hextradius hBband hStar hreserve horder
  refine ⟨χ, hχ, hcχ, heχ, S, hS, A, hA, ?_⟩
  intro Q f
  have hraw := T.fullSourcePhaseInCoordinates_smooth i Q (Ω := Ω) (fun _ h ↦ h)
  have hf : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hraw.contDiffAt (hΩ.mem_nhds (hsχ hq)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with b hb
      exact mul_eq_zero_of_left hb _
  have he q (hq : q ∈ KP) : f =ᶠ[𝓝 q] Function.uncurry (T.fullSourcePhaseInCoordinates i Q) := by
    filter_upwards [heχ q hq] with b hb
    change χ b * _ = _
    rw [hb, one_mul]
    rfl
  refine ⟨hf, he, ?_⟩
  intro R₀ hR₀ n u ell hu hQ j q hq
  have hjet : ‖iteratedFDeriv ℝ j f q‖ ≤ A j * currentCoefficientScale R₀ n ^ (j - Rstar) := by
    apply (norm_iteratedFDeriv_le_cNorm hKP (hf.of_le (by simp)) hq le_rfl).trans
    rw [cNorm_eq_of_eventuallyEq he j]
    exact hb R₀ hR₀ n u ell hu Q hQ j
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, LinearIsometryEquiv.prodComm_apply, Prod.swap_swap] using
      ((LinearIsometryEquiv.prodComm ℝ Par E).norm_iteratedFDeriv_comp_right f q.swap j).le.trans hjet
  · exact (ResponsePrimarySources.norm_iteratedFDeriv_primary_spatialSlice_le
      isOpen_univ isOpen_univ hf.contDiffOn (mem_univ q.1) (mem_univ q.2) j).trans hjet

end JanetCartan.PhysicalPrimary
