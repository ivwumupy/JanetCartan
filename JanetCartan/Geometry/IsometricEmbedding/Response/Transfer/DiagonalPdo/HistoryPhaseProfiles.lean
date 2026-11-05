module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.PhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourcePhase

/-!
# Actual history phase budgets for the selected elliptic response

The original full-source phase producer supplies the low C² cap and every
mixed phase jet. Germ equality on the original compact gives the same
quantitative bounds for any supplied smooth representative, without controlling
its extension elsewhere. One application retains a single representative for
both literal orientations (`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open DirectEvolution FullSourceEnvelopes ActualCarriers FrozenMenu CurrentFullPhase CompatibleResponse
open LeadingWave.FullModulation GeometricProfile ProtectedFlow CurrentCoefficientProfiles
variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d+1)
local notation "Joint" => (E × Par) × W

/-- The actual history phase controls the diagonal source and joint phase
for EVERY representative with the same original germ. Constants do not depend
on its extension outside the source compact, and the low C² constant is the
original producer's constant (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_diagonal_phase_germ_profiles
    (T : PatchQuantitativeFamily P U hU) (i : Fin (d+1))
    {KP : Set (E × Par)} (hKP : IsCompact KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1,q.2.2) ∈ phaseDomain T)
    {Kjoint : Set Joint} (hKjoint : IsCompact Kjoint)
    (hproj : ∀ v ∈ Kjoint, v.1 ∈ KP ∧ (v.2.fst,v.1.2) ∈ KP)
    (G : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (hRstar : 2 ≤ Rstar)
    (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d+1) + bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A C : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧ (∀ j, 0 ≤ C j) ∧
      ∀ Q (φ : E → Par → ℝ), ContDiff ℝ ∞ (Function.uncurry φ) →
        (∀ q ∈ KP, Function.uncurry φ =ᶠ[𝓝 q]
          Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) →
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
        cNorm KP 2 (Function.uncurry φ) ≤ A 2 ∧
        (∀ j q, q ∈ KP → ‖iteratedFDeriv ℝ j (Function.uncurry φ) q‖ ≤
          A j * currentCoefficientScale R₀ n ^ (j-Rstar)) ∧
        ∀ j v, v ∈ Kjoint →
          ‖iteratedFDeriv ℝ j
            (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) v‖ ≤
            C j * currentCoefficientScale R₀ n ^ (j-Rstar) := by
  obtain ⟨S,hS,A,hA,hraw⟩ := T.exists_admissible_history_full_source_phase_profiles
    i hKP hKD G hr hrR hR ext hextcenter hextradius hStar hreserve horder
  obtain ⟨C,hC,hjoint⟩ := exists_diagonal_fullSourcePhase_joint_profiles hKjoint A hA
  refine ⟨S,hS,A,C,hA,hC,?_⟩
  intro Q φ hφ hgerm R₀ hR₀ n u ell hu hQ
  have hL : 1 ≤ currentCoefficientScale R₀ n :=
    one_le_currentCoefficientScale (by linarith) n
  have hsrc (j) (q) (hq : q ∈ KP) :
      ‖iteratedFDeriv ℝ j (Function.uncurry φ) q‖ ≤ A j * currentCoefficientScale R₀ n ^ (j-Rstar) := by
    apply (norm_iteratedFDeriv_le_cNorm hKP (hφ.of_le (by simp)) hq le_rfl).trans
    rw [cNorm_eq_of_eventuallyEq hgerm j]
    exact hraw R₀ hR₀ n u ell hu Q hQ j
  refine ⟨?_,hsrc,hjoint φ hφ KP hproj Rstar _ hL hsrc⟩
  rw [cNorm_eq_of_eventuallyEq hgerm 2]
  have hl := hraw R₀ hR₀ n u ell hu Q hQ 2
  simp only [Nat.sub_eq_zero_of_le hRstar,pow_zero,mul_one] at hl
  convert! hl using 1

/-- Choose ONE original full-source phase representative and apply the actual
history producer to its diagonal elliptic carrier phase. This constructs the
low source cap and all joint phase jets used by both literal orientations;
no phase-jet estimate is assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_diagonal_fullSourcePhase_profiles
    (T : PatchQuantitativeFamily P U hU) (i : Fin (d+1))
    {KP : Set (E × Par)} (hKP : IsCompact KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1,q.2.2) ∈ phaseDomain T)
    {Kjoint : Set Joint} (hKjoint : IsCompact Kjoint)
    (hproj : ∀ v ∈ Kjoint, v.1 ∈ KP ∧ (v.2.fst,v.1.2) ∈ KP)
    (G : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (hRstar : 2 ≤ Rstar)
    (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d+1) + bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin) :
    ∃ χ : E × Par → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q ∈ KP, χ =ᶠ[𝓝 q] (fun _ ↦ 1)) ∧
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A C : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧ (∀ j, 0 ≤ C j) ∧ ∀ Q,
      let φ := fun x c ↦ χ (x,c) * T.fullSourcePhaseInCoordinates i Q x c
      ContDiff ℝ ∞ (Function.uncurry φ) ∧
      (∀ q ∈ KP, Function.uncurry φ =ᶠ[𝓝 q]
        Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) ∧
      ContDiff ℝ ∞ (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
        cNorm KP 2 (Function.uncurry φ) ≤ A 2 ∧
        (∀ j q, q ∈ KP → ‖iteratedFDeriv ℝ j (Function.uncurry φ) q‖ ≤
          A j * currentCoefficientScale R₀ n ^ (j-Rstar)) ∧
        ∀ j v, v ∈ Kjoint →
          ‖iteratedFDeriv ℝ j
            (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) v‖ ≤
            C j * currentCoefficientScale R₀ n ^ (j-Rstar) := by
  obtain ⟨χ,hχ,hcχ,hplateau,_,_,_,_,hrepresent⟩ :=
    exists_fullSource_history_phase_representative T i hKP hKD G hr hrR hR
      ext hextcenter hextradius hStar hreserve horder
  obtain ⟨S,hS,A,C,hA,hC,hprofiles⟩ :=
    exists_admissible_history_diagonal_phase_germ_profiles T i hKP hKD hKjoint hproj
      G hr hrR hR ext hextcenter hextradius hStar hRstar hreserve horder
  refine ⟨χ,hχ,hcχ,hplateau,S,hS,A,C,hA,hC,?_⟩
  intro Q φ
  obtain ⟨hf,hgerm,_⟩ := hrepresent Q
  refine ⟨hf,hgerm,contDiff_diagonalCarrierPhase hf,?_⟩
  exact hprofiles Q φ hf hgerm

end JanetCartan.ResponseTransfer.DiagonalPdo
