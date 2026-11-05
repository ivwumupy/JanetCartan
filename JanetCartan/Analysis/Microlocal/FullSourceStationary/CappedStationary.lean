module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.CappedHessian
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryBranch

/-!
# Full-source stationary radii before the common reference

Fix the coefficient cap and supplied source-incidence geometry first. The
actual low phase budgets then choose one interval for both stationary branches
and the inverse averaged Hessian. The diagonal margin is the existing geometric
output of `FixedResponseSelection.CompactDiagonalMargins`; this leaf does not
repeat the compact or finite selector. Consumer: the supplied-cap variant of
`FixedResponseSelection.IncidenceStationary`, for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution
open ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open EvolutionIntegral.KernelIdentification FullSourceStationary LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)

/-- One positive stationary interval and inverse bound are chosen from the
fixed C4 coefficient cap and supplied geometric margin BEFORE every `Q`, common
reference, finite history, mask and operator. Both literal phases retain the
independent full covector parameters, original conic chart and complete
integration segments. The geometric diagonal inclusion is supplied by
`exists_uniform_full_source_compact_diagonal_margin`; all analytic source and
joint phase budgets are proved from the cap here. The actual cap is supplied by
`exists_reference_tolerance_for_stationary_coefficient_cap`
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_stationary_inverse_maps_of_coefficient_cap
    (i : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε b aperture gap radius : ℝ} (hε : 0 < ε) (hεb : 4 * ε ≤ b)
    (hAp : 0 < aperture) (hg : 0 < gap)
    {A : Set Param} (hA : IsCompact A)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOc : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOK : IsCompact (closure
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius)))
    (hprimary : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    {U₀ : Set (E × Param)} (hU₀ : IsOpen U₀)
    (hU₀KP : U₀ ⊆ closure (elapsedPhysicalBox z ε) ×ˢ A)
    {ρ cap : ℝ} (hρ : 0 < ρ) (hcap : 0 ≤ cap) (KQ : Set E)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ τ > (0 : ℝ), τ ≤ ε ∧ ∃ M > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius
      let D := retainedOpenIntegrationDomain z ε O
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 4 Q.1 ≤ cap →
        cNorm KQ 4 Q.1 ≤ cap →
        (∀ q ∈ U₀, closedBall (WithLp.toLp 2
          (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
            (4 * ρ) ⊆ D) →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m ≤ 3, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.fullSourcePhaseInCoordinates i Q) (p, w)) (κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
              (T.fullSourcePhaseInCoordinates i Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ M) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z ε A O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain ℓ C.target := by
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius
  let D := retainedOpenIntegrationDomain z ε O
  let KP := closure (elapsedPhysicalBox z ε) ×ˢ A
  let K := fullSourceSignedCarrier z ε A O
  have hgeom := fullSourceSignedCarrier_geometry z ε hA hO hOc hOK
  have hK : IsCompact K := hgeom.1
  have hKP : IsCompact KP := by
    have hh := isCompact_closure_retained_physicalBox z (2 * ε)
    simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    exact hh.prod hA
  have hpos v (hv : v ∈ K) :=
    (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK false hv).1
  have hmap (adj : Bool) : MapsTo (ConicPhase.normalize ℓ ∘ fullSourceGraphPoint adj) K
      (closedBall (z.1, z) b) := fun v hv ↦ closedBall_subset_closedBall hεb
    (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK adj hv).2
  obtain ⟨AP, AF, hAP, hAF, hbudgets⟩ :=
    T.exists_full_source_low_phase_budgets_of_coefficient_cap i ℓ hK
      (isCompact_closedBall _ _) hKP hpos hmap
      (fun v hv ↦ (hgeom.2 v hv).1) (fun v hv ↦ (hgeom.2 v hv).2)
      hprimary hcap KQ phaseCost hphaseCost
  obtain ⟨τ₀, hτ₀, hτ₀ε, _, hbranch⟩ := exists_uniform_full_source_conic_stationary_branches
    U₀ hU₀ hρ hε (hAP 2).le (hAF 2).le (hAF 3).le
  obtain ⟨M, hM, τI, hτI, _, inverseVariation, _, hinverse⟩ :=
    T.exists_full_source_hessian_inverse_stability_of_coefficient_cap i ℓ z hε hεb hAp hg
      hA hO hOc hOK hprimary hcap KQ phaseCost hphaseCost
  let τ := min τ₀ τI / 2
  have hτ : 0 < τ := half_pos (lt_min hτ₀ hτI)
  have hτ₀' : 2 * τ ≤ τ₀ := by dsimp [τ]; linarith [min_le_left τ₀ τI]
  have hτI' : 2 * τ ≤ τI := by dsimp [τ]; linarith [min_le_right τ₀ τI]
  have hτε : τ ≤ ε := (by linarith : τ ≤ τ₀).trans hτ₀ε
  have hinterval : Ioo (-2 * τ) (2 * τ) ×ˢ U₀ ⊆ Ioo (-2 * τ₀) (2 * τ₀) ×ˢ U₀ := by
    rintro ⟨t, q⟩ ⟨ht, hq⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hq⟩
  refine ⟨τ, hτ, hτε, M, hM, ?_⟩
  dsimp only
  intro Q hQframe hQcap hdiag Φ C a hC hsource hi hbuffer hCsm hbudget
  let Ω : Set (E × Param) := {q | ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T}
  have hΩ : IsOpen Ω := isOpen_ball.preimage
    (((primaryCoordinateChange i).symm.continuous.comp continuous_fst).prodMk continuous_snd.snd)
  have hφ := T.fullSourcePhaseInCoordinates_smooth i Q (Ω := Ω) (fun _ hq ↦ hq)
  have hgraphs (adj : Bool) : MapsTo (fullSourceGraphPoint adj) K (domain ℓ C.target) :=
    fun v hv ↦ ⟨by simpa only [fullSourceGraphPoint] using hpos v hv, hbuffer (hmap adj hv)⟩
  obtain ⟨W₀, hW₀, hKW₀, hsmooth⟩ := exists_full_source_joint_phase_smooth_neighborhood ℓ C hCsm
    (T.fullSourcePhaseInCoordinates i Q) hΩ hφ hgraphs
      (fun v hv ↦ hprimary _ (hgeom.2 v hv).1) (fun v hv ↦ hprimary _ (hgeom.2 v hv).2)
  have hbuf q (hq : q ∈ U₀) :
      (Icc (-ε) ε ×ˢ {q}) ×ˢ closedBall
        (WithLp.toLp 2 (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
          (4 * ρ) ⊆ K := by
    rintro ⟨⟨t, q'⟩, w⟩ ⟨⟨ht, hq'⟩, hw⟩
    have heq : q' = q := hq'
    subst q'
    exact ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hU₀KP hq⟩,
      subset_closure (hdiag q hq hw)⟩
  obtain ⟨hprimaryBound, hjointBound⟩ := hbudgets Q hQframe hQcap
  have hprimary2 : ∀ q ∈ U₀, ‖iteratedFDeriv ℝ 2
      (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) q‖ ≤ AP 2 := by
    intro q hq
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
      (fun v hv ↦ (hφ.contDiffAt (hΩ.mem_nhds (hprimary v hv))).of_le (by simp))
      (hU₀KP hq) le_rfl).trans (hprimaryBound 2 (by omega))
  have hgraph0 q (hq : q ∈ U₀) : elapsedChartPoint 0 q.1
      (gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) ∈ domain ℓ C.target := by
    have hv : ((0, q), WithLp.toLp 2
        (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1)) ∈ K :=
      hbuf q hq ⟨⟨⟨by linarith, hε.le⟩, rfl⟩, mem_closedBall_self (by positivity)⟩
    exact hgraphs false hv
  have hphase23 adj :
      cNorm K 2 (fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q)) ≤ AF 2 ∧
      cNorm K 3 (fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q)) ≤ AF 3 :=
    ⟨hjointBound C hbuffer hCsm hbudget adj 2 (by omega),
      hjointBound C hbuffer hCsm hbudget adj 3 (by omega)⟩
  obtain ⟨κ, hκ⟩ := hbranch (T.fullSourcePhaseInCoordinates i Q) Ω hΩ hφ
    (hU₀KP.trans hprimary) hprimary2 ℓ Φ C hC z a hsource hi hgraph0
    W₀ K hW₀ hK hKW₀ hbuf hsmooth hphase23 D hdiag
  have hproduct : (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D ⊆ K := by
    rintro ⟨⟨t, q⟩, w⟩ ⟨⟨ht, hq⟩, hw⟩
    exact ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hU₀KP hq⟩, subset_closure hw⟩
  refine ⟨κ, fun adj ↦ ⟨(hsmooth adj).mono (hproduct.trans hKW₀),
    (hκ adj).1.mono hinterval, (hκ adj).2.1, ?_⟩⟩
  intro p hp
  obtain ⟨hκD, hstat, hdist⟩ := (hκ adj).2.2 p (hinterval hp)
  refine ⟨hκD, hstat, hdist, ?_, ?_⟩
  · intro w hw
    have ht : |p.1| ≤ τI := (abs_le.mpr
      ⟨by linarith [hp.1.1], hp.1.2.le⟩).trans hτI'
    have hh := hinverse Q hQframe hQcap Φ C a hC hsource hi hbuffer hCsm hbudget
      adj p.1 ht p.2 (hU₀KP hp.2) (κ adj p) (subset_closure hκD) w hw
    exact ⟨hh.1, hh.2.1⟩
  intro w hw u hu v hv
  have htime : |p.1| ≤ 2 * ε := abs_le.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hseg := (fullSourceSignedCarrier_segments z ε hOc htime (hU₀KP hp.2)
    (subset_closure hκD) hw u hu v hv).1
  exact ⟨hseg, fun adj ↦ hgraphs adj hseg⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
