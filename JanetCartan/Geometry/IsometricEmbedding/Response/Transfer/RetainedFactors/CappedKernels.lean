module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Kernels
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.NestedMasks

/-!
# The complete capped kernels use the same smooth representative

The capped construction puts the output mask in its inner physical box and
the entire elapsed interval below its carrier radius. The nested conic-mask
producer supplies a positive spatial-frequency collar on the FULL multiplier.
These facts prove the smooth representative's supported agreement, including
the nonannular part and the high-pass shoulder. Nothing is truncated in time
or frequency. Consumer: the original regularizations and literal operators in
both `IntegratedEnvelope.Assembly` endpoints
(`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral UniformEvolution
open RegularSector.FiniteMasks FourierIntegral
open FourierIntegral.SourceExpansion
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- The complete elapsed graph, without an annular restriction, normalizes
inside the SAME smooth-phase plateau. This uses the actual capped interval
and nested multiplier cone (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem capped_elapsedPoint_mem_phase_plateau
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε / 2))
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈
      domain ℓ (closedBall (z.1, z) (4 * ε)) := by
  have htε : |t| ≤ ε := by
    rw [abs_of_nonneg ht.1]
    linarith only [ht.2, hsrc, hε]
  have htime : dist (x 0 - t) z.1 ≤ 4 * ε := by
    calc
      _ ≤ dist (x 0 - t) (x 0) + dist (x 0) z.1 := dist_triangle _ _ _
      _ = |t| + dist (x 0) z.1 := by
        rw [Real.dist_eq]
        congr 1
        ring_nf
        exact abs_neg t
      _ ≤ 4 * ε := by
        have hx' : dist (x 0) z.1 < ε / 2 := hx.1
        linarith only [htε, hx', hε]
  refine ⟨hξ.1.1.1, ?_⟩
  change (x 0, (x 0 - t, (spatialPart x,
    (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ))) ∈ _
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff]
  exact ⟨hx.1.le.trans (by linarith only [hε]), htime,
    hx.2.le.trans (by linarith only [hε]),
    hξ.1.1.2.le.trans (by linarith only [hε])⟩

/-- The complete integral agrees with the retained conic phase for the
actual supported multiplier. The source-cap constructor and nested-mask
constructor supply these radius and support facts before choosing amplitudes.
No second multiplier or chart is chosen (`fixed-factor-transfer`). -/
theorem capped_elapsed_integrals_representative_eq_conic
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε)
    (C : OpenPartialHomeomorph TC TC) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χphase : TC → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χphase =ᶠ[𝓝 p] (fun _ ↦ 1))
    {q : ℕ} (W : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (hβ : tsupport β ⊆ retainedFrequencyDomain ℓ z ε aperture (1 / 2))
    (u : SpacetimeL2 d q) :
    let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)
    elapsedGraphIntegral (3 * src / 4) Ψ W χout χsource β u =
      elapsedGraphIntegral (3 * src / 4) (curriedPhase ℓ C) W χout χsource β u ∧
    (∫ t in Icc 0 (3 * src / 4), (elapsedGraph Ψ W χout χsource β t).adjoint u) =
      ∫ t in Icc 0 (3 * src / 4),
        (elapsedGraph (curriedPhase ℓ C) W χout χsource β t).adjoint u := by
  apply SmoothRepresentative.elapsed_integrals_representative_eq_conic ℓ C hδ hχ
  · intro ξ hξ
    exact hδhalf.trans (hβ (subset_tsupport β hξ)).2.le
  · intro t ht x y ξ hA
    have ho : χout x ≠ 0 := fun h ↦ hA
      (elapsedAmplitude_eq_zero_of_mask W χout χsource β t x y ξ (Or.inl h))
    have hb : β ξ ≠ 0 := fun h ↦ hA
      (elapsedAmplitude_eq_zero_of_mask W χout χsource β t x y ξ (Or.inr (Or.inr h)))
    exact capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht
      (hout (subset_tsupport χout ho)) (hβ (subset_tsupport β hb))

/-- The global cancellation phase of the SAME capped solver agrees with the
controlled representative wherever its full two-position amplitude is nonzero.
Only the original support germs of `G` are used, with no derivative bound on
its arbitrary extension. The interval, both masks, multiplier and `W₀+W₁`
are unchanged. Consumer: `retained_fullElapsed_envelopes_of_supported_phase`
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem capped_solver_phase_eq_representative_on_amplitude
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε)
    (C : OpenPartialHomeomorph TC TC) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χphase : TC → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χphase =ᶠ[𝓝 p] (fun _ ↦ 1))
    {q : ℕ} (W₀ W₁ : TC → Matrix (Fin q) (Fin q) ℂ) (G : TC → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (hβ : tsupport β ⊆ retainedFrequencyDomain ℓ z ε aperture (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) (x y ξ : E)
    (hA : elapsedAmplitude (AmplitudeBounds.curryCharacteristicMatrix W₀ +
      AmplitudeBounds.curryCharacteristicMatrix W₁) χout χsource β t x y ξ ≠ 0) :
    elapsedPhase (fun t s y η ↦ G (t, (s, (y, η)))) t x ξ =
      elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase
        (twoTimePhase C)) t x ξ := by
  have ho : χout x ≠ 0 := fun h ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ χout χsource β t x y ξ (Or.inl h))
  have hb : β ξ ≠ 0 := fun h ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ χout χsource β t x y ξ (Or.inr (Or.inr h)))
  have hW : (W₀ + W₁) (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ≠ 0 := by
    intro hz
    apply hA
    simp only [elapsedAmplitude, AmplitudeBounds.curryCharacteristicMatrix, Pi.add_apply] at hz ⊢
    rw [hz]
    exact smul_zero _
  have hconic := congrArg (fun v : ℝ ↦ (x 0 - t) * ξ 0 + v)
    (solver_phase_eq_on_support ℓ C W₀ W₁ G hG hW)
  exact hconic.trans ((SmoothRepresentative.elapsed_representative_eventuallyEq
    ℓ C hδ hχ (capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht
      (hout (subset_tsupport χout ho)) (hβ (subset_tsupport β hb)))
    (hδhalf.trans (hβ (subset_tsupport β hb)).2.le)).eq_of_nhds.symm)

/-- The complete capped residual uses the same controlled representative on
its actual amplitude support. This applies the weaker residual germ only on
the original output-time plateau; no global bound or off-support equality for
the selected `G` is required. `W` is the producer's third collared matrix,
identified with the full `PW₁`, including its zeroth coefficient. Consumer:
`retained_fullElapsed_envelopes_of_supported_phase`
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem capped_residual_phase_eq_representative_on_amplitude
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε)
    (C : OpenPartialHomeomorph TC TC) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χphase : TC → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χphase =ᶠ[𝓝 p] (fun _ ↦ 1))
    {q : ℕ} (W : TC → Matrix (Fin q) (Fin q) ℂ) (G : TC → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : TC, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β : E → ℂ)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (hplateau : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (hβ : tsupport β ⊆ retainedFrequencyDomain ℓ z ε aperture (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) (x y ξ : E)
    (hA : elapsedAmplitude (AmplitudeBounds.curryCharacteristicMatrix W)
      χout χsource β t x y ξ ≠ 0) :
    elapsedPhase (fun t s y η ↦ G (t, (s, (y, η)))) t x ξ =
      elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase
        (twoTimePhase C)) t x ξ := by
  have ho : χout x ≠ 0 := fun h ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ χout χsource β t x y ξ (Or.inl h))
  have hb : β ξ ≠ 0 := fun h ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ χout χsource β t x y ξ (Or.inr (Or.inr h)))
  have hW : W (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ≠ 0 := by
    intro hz
    apply hA
    simp only [elapsedAmplitude, AmplitudeBounds.curryCharacteristicMatrix, hz, smul_zero]
  have hconic := congrArg (fun v : ℝ ↦ (x 0 - t) * ξ 0 + v)
    ((hG _ (hplateau x ho) hW).eq_of_nhds)
  exact hconic.trans ((SmoothRepresentative.elapsed_representative_eventuallyEq
    ℓ C hδ hχ (capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht
      (hout (subset_tsupport χout ho)) (hβ (subset_tsupport β hb)))
    (hδhalf.trans (hβ (subset_tsupport β hb)).2.le)).eq_of_nhds.symm)

/-- Choose the nested angular plateau once. For EVERY retained amplitude,
including `W₀+W₁` and the full `PW₁`, the complete graph and both elapsed
integrals agree with the single smooth representative. The original high-pass
threshold can be increased before selecting operators. Every complex frequency
regularization has the same test output and literal conjugate-transposed reverse
kernel, so the original strong-limit realizations use this very representative. Constants, masks and
thresholds precede the varying chart, coefficients and amplitudes.

`hχ` and `hδhalf` are supplied by `CappedConstruction`, choosing its physical
frequency cap `δphysical = 1/2`. The output support is that constructor's
original physical mask. No supported phase equality is assumed here
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_capped_multiplier_representative_agreement
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (ε / 4) (aperture / 2)) :
    ∃ (angular : Euclidean d → ℝ) (threshold : ℝ), 1 ≤ threshold ∧
      ContDiff ℝ ∞ angular ∧ (∀ η, angular η ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport angular ∧ tsupport angular ⊆ angularCone ℓ z.2.2 (ε / 2) ∧
      (∀ η ∈ tsupport angular, 0 < ℓ η) ∧
      ∀ L ≥ threshold,
        let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask L ξ : ℂ)
        ContDiff ℝ ∞ β ∧ (0 : E) ∉ tsupport β ∧
        tsupport β ⊆ retainedFrequencyDomain ℓ z ε aperture (1 / 2) ∧
        (∀ ξ ∈ tsupport β, conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1)) ∧
        ∀ (C : OpenPartialHomeomorph TC TC) (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 / 2 →
        ∀ χ : TC → ℝ, (∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1)) →
        ∀ (q : ℕ) (W : TwoTimeAmplitude d q) (χout χsource : E → ℂ),
          tsupport χout ⊆ elapsedPhysicalBox z (ε / 2) →
        let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)
        (∀ t ∈ Icc (0 : ℝ) (3 * src / 4),
          elapsedGraph Ψ W χout χsource β t =
            elapsedGraph (curriedPhase ℓ C) W χout χsource β t) ∧
        (∀ t ∈ Icc (0 : ℝ) (3 * src / 4), ∀ cut : E → ℂ,
          graphTestOutput (elapsedPhase Ψ t)
              (frequencyCutFullAmplitude cut (elapsedAmplitude W χout χsource β t)) =
            graphTestOutput (elapsedPhase (curriedPhase ℓ C) t)
              (frequencyCutFullAmplitude cut (elapsedAmplitude W χout χsource β t)) ∧
          ∀ f : E → Fin q → ℂ,
            reverseGraphOperator (elapsedPhase Ψ t)
                (frequencyCutFullAmplitude (fun ξ ↦ star (cut ξ))
                  (fun x y ξ ↦ (elapsedAmplitude W χout χsource β t x y ξ).conjTranspose)) f =
              reverseGraphOperator (elapsedPhase (curriedPhase ℓ C) t)
                (frequencyCutFullAmplitude (fun ξ ↦ star (cut ξ))
                  (fun x y ξ ↦ (elapsedAmplitude W χout χsource β t x y ξ).conjTranspose)) f) ∧
        ∀ u : SpacetimeL2 d q,
          elapsedGraphIntegral (3 * src / 4) Ψ W χout χsource β u =
            elapsedGraphIntegral (3 * src / 4) (curriedPhase ℓ C) W χout χsource β u ∧
          (∫ t in Icc 0 (3 * src / 4), (elapsedGraph Ψ W χout χsource β t).adjoint u) =
            ∫ t in Icc 0 (3 * src / 4),
              (elapsedGraph (curriedPhase ℓ C) W χout χsource β t).adjoint u := by
  obtain ⟨angular, threshold, hthreshold, ha, har, hac, has, hapos, hnested⟩ :=
    exists_retained_nested_conicMask ℓ z hε mask hm hcarrier
  refine ⟨angular, threshold, hthreshold, ha, har, hac, has, hapos, ?_⟩
  intro L hL β
  obtain ⟨hβ, hzero, hsub, hplateau⟩ := hnested L hL
  refine ⟨hβ, hzero, hsub, hplateau, ?_⟩
  intro C δ hδ hδhalf χ hχ q W χout χsource hout Ψ
  have hfreq ξ (hξ : β ξ ≠ 0) : δ ≤ ‖spatialPart ξ‖ :=
    hδhalf.trans (hsub (subset_tsupport β hξ)).2.le
  have hbuffer t (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) x y ξ
      (hA : elapsedAmplitude W χout χsource β t x y ξ ≠ 0) :
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈
        domain ℓ (closedBall (z.1, z) (4 * ε)) := by
    have ho : χout x ≠ 0 := fun h ↦ hA
      (elapsedAmplitude_eq_zero_of_mask W χout χsource β t x y ξ (Or.inl h))
    have hb : β ξ ≠ 0 := fun h ↦ hA
      (elapsedAmplitude_eq_zero_of_mask W χout χsource β t x y ξ (Or.inr (Or.inr h)))
    exact capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht
      (hout (subset_tsupport χout ho)) (hsub (subset_tsupport β hb))
  refine ⟨fun t ht ↦ SmoothRepresentative.elapsedGraph_representative_eq_conic
    ℓ C hδ hχ W χout χsource β t hfreq (hbuffer t ht), ?_,
    fun u ↦ SmoothRepresentative.elapsed_integrals_representative_eq_conic
      ℓ C hδ hχ W χout χsource β (3 * src / 4) hfreq hbuffer u⟩
  intro t ht cut
  have he := SmoothRepresentative.elapsed_representative_eq_on_amplitude
    ℓ C hδ hχ W χout χsource β t hfreq (hbuffer t ht)
  refine ⟨graphTestOutput_phase_congr _ _ _ ?_, fun f ↦ reverseGraphOperator_phase_congr _ _ _ ?_ f⟩
  · intro x y ξ hA
    exact he x y ξ (fun hz ↦ hA (by simp [frequencyCutFullAmplitude, hz]))
  · intro x y ξ hA
    exact he x y ξ (fun hz ↦ hA (by simp [frequencyCutFullAmplitude, hz]))

end JanetCartan.ResponseTransfer.RetainedFactors
