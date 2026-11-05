module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.JointPhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.LowPhaseBudgets

/-!
# Reserved history grades for the negative full-source joint phase

The whole negative source phase and the unchanged retained conic chart both cost
coefficient order `m+1`. The same actual history supplies the coefficient
profile with map reserve `Rstar+3`. This is the second/third-jet producer of
the full-source stationary constructor, at all derivative orders for
`app:ch_response:eq:direct-envelope-profile`. The consuming reserved retarded
near estimate keeps the full elapsed interval and the same stationary data;
source sign and literal adjoint orientation remain independent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.Characteristic ConicPhase EvolutionIntegral FullSourceStationary
open ResponseTransfer.DirectEvolution LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "TC" => TwoTimePoint (Euclidean d)

/-- Actual all-order history bounds for BOTH literal orientations of the
negative-source joint phase, with the graph phase unchanged. The independent covector remains free throughout;
all constants precede histories, chart witnesses and derivative orders, with
the original `Rstar+3` reserve and no additional scale power
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_negative_full_source_joint_phase_profiles
    (i : Fin (d + 1)) (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (FullSourcePoint d)} {J : Set TC} {KP : Set (E × Param)}
    (hK : IsCompact K) (hJ : IsCompact J) (hKP : IsCompact KP)
    (hpos : ∀ v ∈ K, 0 < ℓ (spatialPart v.2.snd))
    (hmap : MapsTo (ConicPhase.normalize ℓ ∘ fullSourceGraphPoint adj) K J)
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ KP)
    (hout : ∀ v ∈ K, v.1.2 ∈ KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {KQ : Set E} (hKQ : IsCompact KQ)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
      ∀ C : OpenPartialHomeomorph TC TC, J ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm J m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      ∀ m, cNorm K m (fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ A m * currentCoefficientScale R₀ n ^ (m - Rstar) ∧
        ∀ t (p : (E × Param) × CarrierVariables (d + 1)), ((t, p.1), p.2) ∈ K →
          ‖iteratedFDeriv ℝ m (fun q : (E × Param) × CarrierVariables (d + 1) ↦
            fullSourceJointPhase adj (curriedPhase ℓ C)
              (T.negativeFullSourcePhaseInCoordinates i Q) ((t, q.1), q.2)) p‖ ≤
            A m * currentCoefficientScale R₀ n ^ (m - Rstar) := by
  obtain ⟨S, hS, AQ, _AB, hAQ, _, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hStar (reserve := Rstar + 1) (by omega) horder
  obtain ⟨B, hB, hb⟩ := exists_fullSourceJointPhase_cNorm_bound adj ℓ
    hK hJ hKP hpos hmap hsrc hout
  obtain ⟨BP, hBP, hbP⟩ := T.exists_negativeFullSourcePhaseInCoordinates_frame_bound i hKP hKD
  let A := fun m ↦ B m * (1 + (phaseCost m + BP m) * (1 + AQ (m + 1)))
  refine ⟨S, hS, A, fun m ↦ by
    dsimp [A]
    have hp := hphaseCost m
    have hq := hAQ (m + 1)
    have hbp := hBP m
    exact mul_nonneg (hB m).le (by positivity), ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ C hJC hC hphase m
  have hL : 1 ≤ currentCoefficientScale R₀ n :=
    one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) n
  have h1 := one_le_pow₀ hL (n := m - Rstar)
  have hcoeff' {V : Set E} (hV : IsCompact V) :
      cNorm V (m + 1) Q.1 ≤ AQ (m + 1) * currentCoefficientScale R₀ n ^ (m - Rstar) := by
    rw [hQ]
    simpa only [show m + 1 - (Rstar + 1) = m - Rstar by omega] using
      ((hcoeff R₀ hR₀ n u ell hu).2.2 V hV).1 (m + 1)
  have hφ : ∀ q ∈ KP, ContDiffAt ℝ ∞
      (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) q := by
    intro q hq
    have hF : ContDiff ℝ ∞ (fun q : E × Param ↦
        ((primaryCoordinateChange i).symm q.1, q.2.2)) :=
      ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd.snd
    have hh := ((phase_smooth T Q).contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius) (hKD q hq)))).comp q hF.contDiffAt
    exact hh.neg
  have hg := (hphase m).trans (mul_le_mul_of_nonneg_left
    (add_le_add h1 (hcoeff' hKQ)) (hphaseCost m).le)
  have hp := (hbP Q m).trans (mul_le_mul_of_nonneg_left
    (add_le_add h1 (hcoeff' (isCompact_closedBall _ _))) (hBP m).le)
  have hnorm : cNorm K m (fullSourceJointPhase adj (curriedPhase ℓ C)
      (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ A m * currentCoefficientScale R₀ n ^ (m - Rstar) := by
    apply (hb C hJC hC (T.negativeFullSourcePhaseInCoordinates i Q) hφ m).trans
    calc
      _ ≤ B m * (currentCoefficientScale R₀ n ^ (m - Rstar) +
          phaseCost m * (currentCoefficientScale R₀ n ^ (m - Rstar) +
            AQ (m + 1) * currentCoefficientScale R₀ n ^ (m - Rstar)) +
          BP m * (currentCoefficientScale R₀ n ^ (m - Rstar) +
            AQ (m + 1) * currentCoefficientScale R₀ n ^ (m - Rstar))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 hg) hp) (hB m).le
      _ = _ := by dsimp [A]; ring
  have hsmooth v (hv : v ∈ K) : ContDiffAt ℝ ∞
      (fullSourceJointPhase adj (curriedPhase ℓ C) (T.negativeFullSourcePhaseInCoordinates i Q)) v :=
    contDiffAt_fullSourceJointPhase adj ℓ C hC _
      ⟨by simpa [fullSourceGraphPoint] using hpos v hv, hJC (hmap hv)⟩
      (hφ _ (hsrc v hv)) (hφ _ (hout v hv))
  refine ⟨hnorm, ?_⟩
  intro t p hp
  exact (norm_fullSourceJointPhase_fixedTime_jet_le adj (curriedPhase ℓ C)
    (T.negativeFullSourcePhaseInCoordinates i Q) t (hsmooth _ hp) m).trans
      ((norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun v hv ↦ (hsmooth v hv).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hp le_rfl).trans hnorm)

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
