module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.WholeImageGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceProfiles

/-!
# Whole-image bounds on the original selected history chart

Apply the actual history coefficient producer to the retained whole-image
inverse. The selected chart, its radial section, and the original elapsed
interval remain fixed. Every inverse constant precedes the history. Together
with `exists_protected_incidence_full_source_history_profiles` and
`full_source_incidence_critical_slice_of_stationary_segments`, this supplies
the geometric inputs to the literal physical full-source envelope application.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral
open SymbolBudgets FourierIntegral WholeImageGeometry NormalComparison LowBounds
open RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The actual extended history frame constructs all whole-image inverse
bounds on a supplied selected chart. The low coefficient order is paid by
the existing direct-envelope reserve, and the physical elapsed interval is
`[0,3*c.maskRadius/4]`. The phase assumptions are the original chart outputs
of `ProtectedConstruction.FullSource`, not inverse or envelope conclusions.
The inverse and averaged Jacobian are those of the SAME selected phase
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_history_wholeImage_geometry
    {Ω : Set E} {x ξ : E} {RQ M : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d + 1)) ξ M)
    {ε aperture : ℝ} (hε : 0 < ε) (hεtarget : 4 * ε ≤ c.targetRadius)
    (hAp : 0 ≤ aperture) (hsrc : c.maskRadius ≤ ε)
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hStar : 8 ≤ rStar) (hRstar : FullLowBounds.fullLowReserve (d + 1) + 2 < Rstar)
    (hreserve : Rstar + 5 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    let z : Z := ((coordinateSplit c.index x).1, ((coordinateSplit c.index x).2,
      (coordinateSplit c.index ξ).2))
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧
    ∃ gap > (0 : ℝ), ∃ a > (0 : ℝ), ∃ bfreq > a,
    ∃ Mgraph > (0 : ℝ), ∃ Ggraph > (0 : ℝ),
    ∃ cgraph : ℝ, 1 ≤ cgraph ∧ ∃ growth > (0 : ℝ),
    ∀ R₀, S₀ ≤ R₀ →
    ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
    let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) c.targetRadius ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ q ∈ C.target,
        HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      (∀ q ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) c.targetRadius) j (twoTimePhase C) ≤
        c.phaseCost j * (1 + cNorm (closedBall x RQ) (j + 1) Q)) →
    ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 / 2 →
    ∀ χ : TC → ℝ,
      (∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ t ∈ Icc (0 : ℝ) (3 * c.maskRadius / 4),
      let X := elapsedPhysicalBox z (ε / 2)
      let D := retainedFrequencyDomain c.radialSection z ε aperture (1 / 2)
      let S := elapsedPhase (curriedPhase c.radialSection C) t
      let S' := elapsedPhase (SmoothRepresentative.curriedRepresentative c.radialSection δ hδ χ (twoTimePhase C)) t
      let η := wholeImageInverse S D
      let J := averagedJacobian S
      let W := X ×ˢ (X ×ˢ D)
      AveragedGradientChart S' X D η J gap ∧
      IsOpen (bufferedNormalDomain X D S') ∧
      ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D S') ∧
      MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D S') W ∧
      ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J q.1 q.2.1 q.2.2) W ∧
      (∀ q ∈ W, gap ≤ |(J q.1 q.2.1 q.2.2).det|) ∧
      (∀ q ∈ bufferedNormalDomain X D S',
        normalForwardCoordinates S' (normalInverseCoordinates η q) = q) ∧
      (∀ x ∈ X, ∀ y ∈ X, ∀ ξ ∈ D,
        ‖averagedGradient S' x y ξ‖ ≤ growth * (1 + ‖ξ‖)) ∧
      (∀ K : Set (NormalVariables (d + 1)), IsClosed K → K ⊆ W →
        IsClosed (normalForwardCoordinates S' '' K) ∧
          normalForwardCoordinates S' '' K ⊆ bufferedNormalDomain X D S') ∧
      ∀ l : ℕ,
        let V := X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^l) a bfreq)
        let U := normalDyadicShell (bufferedNormalDomain X D S') l
        IsOpen U ∧ IsOpen V ∧
        ContDiffOn ℝ ∞ (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η)) U ∧
        MapsTo (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η)) U V ∧
        ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦
          normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) V ∧
        (∀ q ∈ V, gap ≤ |(normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2).det|) ∧
        (∀ q ∈ V, ∀ j ≤ primitiveNormalReserve (d + 1),
          ‖iteratedFDeriv ℝ j (fun q : NormalVariables (d + 1) ↦
            normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) q‖ ≤ Mgraph) ∧
        (∀ q ∈ U, ∀ j, 1 ≤ j → j ≤ primitiveNormalReserve (d + 1) →
          ‖iteratedFDeriv ℝ j
            (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η)) q‖ ≤ Ggraph) ∧
        ∀ q ∈ V, (2 : ℝ)^l ≤ cgraph * (1 + ‖(2 : ℝ)^l • q.2.2‖) := by
  intro z
  have hwholeReserve := retained_wholeImage_history_reserve hRstar hreserve
  obtain ⟨S₀, hS₀, AQ, _AB, _hAQ, _hAB, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles Gref hr hrR hR ext
      hextcenter hextradius hStar (reserve := wholeImagePhaseReserve (d + 1) + 1)
      (by omega) horder
  obtain ⟨gap, hgap, a, ha, bfreq, hab, Mgraph, hMg, Ggraph, hGg,
    cgraph, hcg, growth, hgrowth, hgeometry⟩ :=
    exists_retained_representative_wholeImage_geometry c.radialSection z hε
      (by linarith : 2 * ε < c.targetRadius) hAp c.phaseCost c.phaseCost_pos
      (AQ (wholeImagePhaseReserve (d + 1) + 1))
  refine ⟨S₀, hS₀, gap, hgap, a, ha, bfreq, hab, Mgraph, hMg, Ggraph, hGg,
    cgraph, hcg, growth, hgrowth, ?_⟩
  intro R₀ hR₀ n u ell hu Q h Φ C hbuffer hsmooth hdiff hnear hphase δ hδ hδhalf χ hχ t ht
  have hQ : cNorm (closedBall x RQ) (wholeImagePhaseReserve (d + 1) + 1) Q ≤
      AQ (wholeImagePhaseReserve (d + 1) + 1) := by
    simpa only [Nat.sub_self, pow_zero, mul_one] using
      ((hcoeff R₀ hR₀ n u ell hu).2.2 (closedBall x RQ) (isCompact_closedBall x RQ)).1
        (wholeImagePhaseReserve (d + 1) + 1)
  exact hgeometry (closedBall x RQ) Q hQ h Φ C hbuffer hsmooth hdiff hnear hphase
    c.maskRadius δ hsrc hδ hδhalf χ hχ t ht

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
