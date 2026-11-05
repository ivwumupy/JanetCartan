module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets
/-!
# Actual history profiles of the retained modulated phases

The SAME admissible history supplies both the retained local chart budget and
the original primary phase. Their literal forward/adjoint combination has
joint grade `L^(m-Rstar)` with map reserve `Rstar+3`. Freezing elapsed time
retains this exact grade, with no extra power of the envelope scale.

The second endpoint selects the common smooth representative before histories,
charts and orders, and proves the same bounds for its literal modulated phase.
It retains global phase smoothness and the original annular radial identity.
The full compact carrier, its normalization containment and positive spatial
frequency gap remain the parent's geometric obligations, as do uniform critical
points and averaged-Hessian gaps. These are phase-profile constructions, not
an envelope estimate or the full response theorem.
Consumer: both `DirectEvolution.IntegratedEnvelope.Assembly` endpoints,
`app:ch_response:eq:direct-envelope-profile` in paper.tex.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.Characteristic ConicPhase EvolutionIntegral

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => ResponseTransfer.DirectEvolution.CarrierVariables (d + 1)

/-- The SAME extended admissible history supplies all joint jets of the
literal modulated phase, including elapsed time, BOTH physical positions,
frequency and primary parameters. The adjoint is the literal reversed phase.
The retained local chart uses its original coefficient shift one and the
primary phase uses its proved frame shift one; map reserve `Rstar+3` pays
both, without any additional frequency or envelope-scale power.

The fixed compact carriers and their original domain inclusions remain
geometric obligations. This result derives the phase-jet input, not critical
geometry or a successful envelope (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_joint_retained_phase_profiles
    {c C : ℝ} (hP : P.IsValid c C) (i : Fin (d + 1))
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (RetainedCarrierPoint d)} {J : Set TC} {KP : Set (E × Euclidean 3)}
    (hK : IsCompact K) (hJ : IsCompact J) (hKP : IsCompact KP)
    (hpos : ∀ v ∈ K, 0 < ℓ (spatialPart v.2.snd))
    (hmap : MapsTo (ConicPhase.normalize ℓ ∘ carrierGraphPoint adj) K J)
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ KP)
    (hout : ∀ v ∈ K, v.1.2 ∈ KP)
    (hKPU : ∀ q ∈ KP, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
      q.2 ∈ parameterInterior (2 * P.radius))
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
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
      ∀ D : OpenPartialHomeomorph TC TC, J ⊆ D.target →
        ContDiffOn ℝ ∞ (twoTimePhase D) D.target →
        (∀ m, cNorm J m (twoTimePhase D) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      ∀ m, cNorm K m (jointRetainedCarrierPhase adj (curriedPhase ℓ D)
        (T.primaryPhaseInCoordinates i Q)) ≤ A m * currentCoefficientScale R₀ s ^ (m - Rstar) ∧
        ∀ t (p : (E × Euclidean 3) × W), ((t, p.1), p.2) ∈ K →
          ‖iteratedFDeriv ℝ m (fun q : (E × Euclidean 3) × W ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ D)
            (T.primaryPhaseInCoordinates i Q) ((t, q.1), q.2)) p‖ ≤
              A m * currentCoefficientScale R₀ s ^ (m - Rstar) := by
  obtain ⟨S, hS, AQ, AB, hAQ, _, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hStar (reserve := Rstar + 1) (by omega) horder
  obtain ⟨B, hB, hb⟩ := exists_jointRetainedCarrierPhase_cNorm_bound adj ℓ
    hK hJ hKP hpos hmap hsrc hout
  obtain ⟨BP, hBP, hbP⟩ := T.exists_primaryPhaseInCoordinates_frame_bound hP i hKP hKPU
  let A := fun m ↦ B m * (1 + (phaseCost m + BP m) * (1 + AQ (m + 1)))
  refine ⟨S, hS, A, fun m ↦ by
    dsimp [A]
    have hp := hphaseCost m
    have hq := hAQ (m + 1)
    have hbp := hBP m
    exact mul_nonneg (hB m).le (by positivity), ?_⟩
  intro R₀ hR₀ s u ell hu Q hQ D hJD hD hphase m
  have hL : 1 ≤ currentCoefficientScale R₀ s :=
    one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) s
  have h1 := one_le_pow₀ hL (n := m - Rstar)
  have hcoeff' {V : Set E} (hV : IsCompact V) :
      cNorm V (m + 1) Q.1 ≤ AQ (m + 1) * currentCoefficientScale R₀ s ^ (m - Rstar) := by
    rw [hQ]
    simpa only [show m + 1 - (Rstar + 1) = m - Rstar by omega] using
      ((hcoeff R₀ hR₀ s u ell hu).2.2 V hV).1 (m + 1)
  have hφ : ∀ q ∈ KP, ContDiffAt ℝ ∞
      (Function.uncurry (T.primaryPhaseInCoordinates i Q)) q := by
    intro q hq
    have hq' : ((primaryCoordinateChange i).symm q.1, q.2) ∈
        ball (0 : E) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) := hKPU q hq
    have hs := (T.carrier_smooth hP Q).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior (2 * P.radius))).mem_nhds hq')
    change ContDiffAt ℝ ∞ (fun v : E × Euclidean 3 ↦
      T.carrier Q ((primaryCoordinateChange i).symm v.1) v.2) q
    exact hs.comp (f := fun v : E × Euclidean 3 ↦ ((primaryCoordinateChange i).symm v.1, v.2)) q
      (((primaryCoordinateChange i).symm.contDiff.contDiffAt.comp q contDiffAt_fst).prodMk
        contDiffAt_snd)
  have hg := (hphase m).trans (mul_le_mul_of_nonneg_left
    (add_le_add h1 (hcoeff' hKQ)) (hphaseCost m).le)
  have hp := (hbP Q m).trans (mul_le_mul_of_nonneg_left
    (add_le_add h1 (hcoeff' (isCompact_closedBall _ _))) (hBP m).le)
  have hnorm : cNorm K m (jointRetainedCarrierPhase adj (curriedPhase ℓ D)
      (T.primaryPhaseInCoordinates i Q)) ≤ A m * currentCoefficientScale R₀ s ^ (m - Rstar) := by
    apply (hb D hJD hD (T.primaryPhaseInCoordinates i Q) hφ m).trans
    calc
      _ ≤ B m * (currentCoefficientScale R₀ s ^ (m - Rstar) +
          phaseCost m * (currentCoefficientScale R₀ s ^ (m - Rstar) +
            AQ (m + 1) * currentCoefficientScale R₀ s ^ (m - Rstar)) +
          BP m * (currentCoefficientScale R₀ s ^ (m - Rstar) +
            AQ (m + 1) * currentCoefficientScale R₀ s ^ (m - Rstar))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 hg) hp) (hB m).le
      _ = _ := by dsimp [A]; ring
  have hsmooth v (hv : v ∈ K) : ContDiffAt ℝ ∞
      (jointRetainedCarrierPhase adj (curriedPhase ℓ D) (T.primaryPhaseInCoordinates i Q)) v :=
    contDiffAt_jointRetainedCarrierPhase adj ℓ D hD _
      ⟨by simpa [carrierGraphPoint] using hpos v hv, hJD (hmap hv)⟩
      (hφ _ (hsrc v hv)) (hφ _ (hout v hv))
  refine ⟨hnorm, ?_⟩
  intro t p hp
  exact (norm_jointRetainedCarrierPhase_fixedTime_jet_le adj (curriedPhase ℓ D)
    (T.primaryPhaseInCoordinates i Q) t (hsmooth _ hp) m).trans
      ((norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun v hv ↦ (hsmooth v hv).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hp le_rfl).trans hnorm)

/-- Select the common smooth representative BEFORE histories, charts and
orders, then apply the proved original-history phase bounds to that very
representative. Its fixed physical and normalized frequency gaps, global
smoothness and literal annular radial identity are retained. On the supplied
full compact carrier its joint and fixed-time phase grades have the original
reserve `Rstar+3`, in both literal orientations.

This closes the phase-jet and smoothing connection on a common carrier; it
does not select that carrier, construct its uniform critical geometry, or
prove any envelope estimate (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_joint_smooth_phase_profiles
    {c C : ℝ} (hP : P.IsValid c C) (i : Fin (d + 1))
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (RetainedCarrierPoint d)} {J : Set TC} {KP : Set (E × Euclidean 3)}
    (hK : IsCompact K) (hJ : IsCompact J) (hKP : IsCompact KP)
    (hpos : ∀ v ∈ K, 0 < ℓ (spatialPart v.2.snd))
    (hmap : MapsTo (ConicPhase.normalize ℓ ∘ carrierGraphPoint adj) K J)
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ KP)
    (hout : ∀ v ∈ K, v.1.2 ∈ KP)
    (hKPU : ∀ q ∈ KP, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
      q.2 ∈ parameterInterior (2 * P.radius))
    {V : Set TC} (hV : IsOpen V) (hJV : J ⊆ V)
    {δphysical δannular : ℝ} (hphysical : 0 < δphysical) (hannular : 0 < δannular)
    (hfrequency : ∀ v ∈ K, δannular ≤ ‖spatialPart v.2.snd‖)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {KQ : Set E} (hKQ : IsCompact KQ)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, δ ≤ δphysical ∧ δ ≤ δannular ∧
    ∃ χ : TC → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
      (∀ p ∈ J, χ =ᶠ[𝓝 p] (fun _ ↦ 1)) ∧
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
      ∀ D : OpenPartialHomeomorph TC TC, V ⊆ D.target →
        ContDiffOn ℝ ∞ (twoTimePhase D) D.target →
        (∀ m, cNorm J m (twoTimePhase D) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      ContDiff ℝ ∞ (SmoothRepresentative.representative ℓ δ hδ χ (twoTimePhase D)) ∧
      (∀ lam : ℝ, 1 ≤ lam → ∀ R t : ℝ, ∀ x θ : E,
        lam • θ ∈ SmoothRepresentative.annularFrequencyCarrier δ R lam →
        elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase D))
          t x (lam • θ) = lam * elapsedPhase
            (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase D)) t x θ) ∧
      ∀ m, cNorm K m (jointRetainedCarrierPhase adj
        (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase D))
        (T.primaryPhaseInCoordinates i Q)) ≤ A m * currentCoefficientScale R₀ s ^ (m - Rstar) ∧
        ∀ t (p : (E × Euclidean 3) × W), ((t, p.1), p.2) ∈ K →
          ‖iteratedFDeriv ℝ m (fun q : (E × Euclidean 3) × W ↦ jointRetainedCarrierPhase adj
            (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase D))
            (T.primaryPhaseInCoordinates i Q) ((t, q.1), q.2)) p‖ ≤
              A m * currentCoefficientScale R₀ s ^ (m - Rstar) := by
  obtain ⟨δ, hδ, hδp, hδa, χ, hχ, hc, hs, he, hrep⟩ :=
    SmoothRepresentative.exists_common_smooth_representative ℓ hJ hV hJV hphysical hannular
  obtain ⟨S, hS, A, hA, hprofile⟩ :=
    T.exists_admissible_history_joint_retained_phase_profiles hP i adj ℓ
      hK hJ hKP hpos hmap hsrc hout hKPU G hr hrR hR ext hextcenter hextradius
      hStar hreserve horder hKQ phaseCost hphaseCost
  refine ⟨δ, hδ, hδp, hδa, χ, hχ, hc, hs, he, S, hS, A, hA, ?_⟩
  intro R₀ hR₀ s u ell hu Q hQ D hVD hD hphase
  have hr := hrep D hVD hD
  refine ⟨hr.1, hr.2.2.2.2.1, ?_⟩
  have hmap' : MapsTo (carrierGraphPoint adj) K (domain ℓ J) := fun v hv ↦
    ⟨by simpa [carrierGraphPoint] using hpos v hv, hmap hv⟩
  have hfreq v (hv : v ∈ K) : δ ≤ ‖spatialPart v.2.snd‖ :=
    hδa.trans (hfrequency v hv)
  intro m
  have hb := hprofile R₀ hR₀ s u ell hu Q hQ D (hJV.trans hVD) hD hphase m
  refine ⟨?_, ?_⟩
  · rw [cNorm_jointRetainedCarrierPhase_representative_eq adj ℓ D hδ he
      (T.primaryPhaseInCoordinates i Q) hmap' hfreq m]
    exact hb.1
  · intro t p hp
    have hg := jointRetainedCarrierPhase_representative_eventuallyEq adj ℓ D hδ he
      (T.primaryPhaseInCoordinates i Q) (hmap' hp) (hfreq _ hp)
    have hslice : Continuous (fun q : (E × Euclidean 3) × W ↦
        ((t, q.1), q.2)) := (continuous_const.prodMk continuous_fst).prodMk continuous_snd
    have hs := hg.comp_tendsto (hslice.tendsto p)
    have hd := (hs.iteratedFDeriv ℝ m).eq_of_nhds
    rw [show iteratedFDeriv ℝ m (fun q : (E × Euclidean 3) × W ↦ jointRetainedCarrierPhase adj
        (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase D))
          (T.primaryPhaseInCoordinates i Q) ((t, q.1), q.2)) p =
      iteratedFDeriv ℝ m (fun q : (E × Euclidean 3) × W ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ D)
        (T.primaryPhaseInCoordinates i Q) ((t, q.1), q.2)) p from hd]
    exact hb.2 t p hp

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
