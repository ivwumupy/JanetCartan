module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.UniformProjected
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CurrentNeighborhood
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.SelectedFactors

/-!
# Primitive current neighborhoods for complete signed protection

The relative form of `app:ch_regular:thm:no-return`: one primitive map threshold
supplies the projected-frame neighborhood and the full extended coefficient
low class. The only reference premise is its finite-order cube-frame margin;
its producer is the common source-dilation initialization. This module does not
claim to instantiate that reference producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference
open GeometricProfile

/-- Primitive displacement neighborhood for `app:ch_regular:thm:no-return`.
It assumes only smoothness and a finite-order map displacement bound. -/
abbrev PrimitiveMapNeighborhood {n : ℕ} (G : FlatReference n) (B : ℝ) (m : ℕ) (δ : ℝ) :=
  {F : Euclidean n → Euclidean (embeddingDimension n) //
    ContDiff ℝ ∞ F ∧ cNorm (closedBall 0 B) m (F - G.map) < δ}

/-- Fixed complete-source protection and the full actual coefficient array
from a primitive map neighborhood (`app:ch_regular:thm:no-return`). All centers,
weights, buffers and the extension are chosen before the reference and current
map. The fixed reference margin is explicit and must be supplied by the common
initialization. Current rank, frame smallness and the full-array low class are
proved here, together with operator agreement on the whole physical core. -/
theorem exists_primitive_signed_no_return {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {b B : ℝ} (hbB : b < B)
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 B) isOpen_ball)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ closedBall 0 b)
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    (hpb : p.radius ≤ b)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hradius : ∀ i, r₀ < (T i).physicalRadius)
    (m : ℕ) (hm : 6 ≤ m) {εlow : ℝ} (hεlow : 0 < εlow) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ r δ a A ε τ εx : ℝ, 0 < r ∧ r < r₀ ∧ 3 * r < p.radius ∧
        0 < δ ∧ 0 < a ∧ 0 < A ∧ 0 < ε ∧ 0 < τ ∧ 0 < εx ∧
      ∃ Ω₀ Ω₁ Γin Γout : Set (Euclidean n),
        IsCompact Ω₀ ∧ IsCompact Ω₁ ∧ IsCompact Γin ∧ IsCompact Γout ∧
        Ω₀ ⊆ interior Ω₁ ∧ Ω₁ ⊆ interior Γin ∧ Γin ⊆ interior Γout ∧
        (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
        (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
        (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
        Γout ⊆ (cubeBadSubspaceUnion n)ᶜ ∧
      ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω₁ ∧ (frozenSymbol n).h (0, ξ) = 0})
        (g : s → ComparisonGeometry (Euclidean n)),
        (∀ i : s, 3 * r < (g i).radius) ∧
      ∃ ρ εw : ℝ, 0 < ρ ∧ ρ < τ ∧ 0 < εw ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∃ ηref > (0 : ℝ), ∀ Gref : FlatReference n, B < Gref.domain.chartRadius →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) m
          (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i - cubeStress n i) < ηref) →
      ∃ Z₀ : Euclidean n → Fin n × Fin n → ℝ, ContDiff ℝ ∞ Z₀ ∧
      ∃ dmap > (0 : ℝ),
      ∃ lift : PrimitiveMapNeighborhood Gref B (m + 2) dmap →
        ProjectedImmersionNeighborhood (embeddingDimension n) (ball 0 B) (closedBall 0 b) δ,
      (∀ F, (lift F).1 = F.1) ∧
      ∃ hlow : ∀ (Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap) i,
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress (lift Q).1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
      let family := fun z : PrimitiveMapNeighborhood Gref B (m + 2) dmap × closedBall (0 : Euclidean n) r ↦
        currentGroup T assign R (ProjectedStressFrame.projectedStress (lift z.1).1)
          (frameOfImmersion isOpen_ball (lift z.1)).2.1 (hlow z.1) z.2;
      closure (directionSet family (groupCube D assign)) ⊆ interior Ω₀ ∧
      (∀ z (q : Pair G (Euclidean 3) (groupCube D assign)),
        (∀ L ∈ cubeBadSubspaces n, a * q.beat ≤ ‖projectAway L (q.vector (family z))‖) ∧
        q.vector (family z) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          a * (lam * q.beat) ≤ ‖lam • q.vector (family z)‖ ∧
          ‖lam • q.vector (family z)‖ ≤ A * (lam * q.beat)) ∧
      (∀ (Dprofile : ℕ → ℝ) (order : ℕ), ∃ Cprofile : ℕ → ℝ,
        (∀ j, 0 < Cprofile j) ∧ ∀ slow : ℝ, 1 ≤ slow →
          ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
          HasDerivativeProfile (closedBall p.center p.radius)
            (geometricReducedCoefficients Q.1) order slow Dprofile →
          HasDerivativeProfile (closedBall (0 : Euclidean n) (3 * r))
            (extendedReducedCoefficients p Z₀ Q.1) order slow Cprofile) ∧
      ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
        ContDiff ℝ ∞ (extendedReducedCoefficients p Z₀ Q.1) ∧
        cNorm univ m
          (extendedReducedCoefficients p Z₀ Q.1 - reducedCoefficientBackground Z₀) < εlow ∧
        EqOn (extendedReducedCoefficients p Z₀ Q.1) (geometricReducedCoefficients Q.1)
          (closedBall 0 (3 * r)) ∧
        (∀ x a i k, extendedReducedCoefficients p Z₀ Q.1 x (.inl (a, i, k)) =
          extendedProjectedStress p Q.1 x i a k) ∧
        (∀ u x, x ∈ closedBall 0 (3 * r) → ∀ i,
          reducedCoefficientOperator (extendedReducedCoefficients p Z₀ Q.1) u x i =
            NullTransport.reducedOperator Q.1 (ProjectedStressFrame.projectedStress Q.1) u x i) ∧
        EqOn (extendedProjectedStress p Q.1) (ProjectedStressFrame.projectedStress Q.1) (closedBall 0 (3 * r)) ∧
        let H := normalizedHomogeneousSymbol isOpen_univ (extendedProjectedStress p (lift Q).1)
          (contDiff_affineFrameExtension p ((frameOfImmersion isOpen_ball (lift Q)).2.1.mono
            (by rw [hp0]; exact closedBall_subset_ball (hpb.trans_lt hbB)))).contDiffOn;
        (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
          (Φ : HamiltonFlow H V) (u : InitialData V) (t₀ : ℝ),
          u ∈ Φ.parameters →
          (Φ.position (t₀, u), Φ.momentum (t₀, u)) ∈ closedBall 0 r ×ˢ Ω₁ →
          (∀ t ∈ Icc (-τ) τ, t₀ + t ∈ Φ.time) →
          ∀ t ∈ Icc (-τ) τ,
            closedBall (Φ.position (t₀ + t, u)) εx ⊆ ball 0 (2 * r)) ∧
        ∃ charts : (i : s) → ComparisonChart H (g i),
          IsCompact (normalizedGraphImage (ComparisonChart.familyGradient charts)
            (closedBall 0 (2 * r)) univ) ∧
          let P := positiveConicLift (ComparisonChart.familyGradient charts)
            (ball 0 (2 * r)) univ;
          P ⊆ H.domain ∩ {z | H.h z = 0} ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, H.h z = 0 → z ∈ P) ∧
          (∀ z ∈ P, closedBall (normalizedCovector z.2) ε ⊆
            interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ z ∈ P, ∀ w, CompleteCharacteristicSegment H (ball 0 (2 * r)) z w → w ∈ P) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ w k,
            PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k →
            closedBall (normalizedCovector w.2) ε ⊆
              interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εw ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ v k,
            PositiveConicChain (selectedFactorRelation charts w) z v k →
              closedBall (normalizedCovector v.2) ε ⊆
                interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ z v k, PositiveConicChain (selectedFactorRelation charts w) z v k →
            H.h z ≠ 0 → z = v) ∧
          (∀ i : s, ∀ q : centers i, ∀ backward Ksource,
            Ksource ⊆ (w i q).sourceProduct → ∀ v,
            v ∈ completeImage backward (w i q).physicalSupport Ksource →
            ∃ u ∈ Ksource,
              (canonicalState (charts i).flow u = canonicalState (charts i).flow v ∨
                CompleteCharacteristicSegment H (ball 0 (2 * r))
                  (canonicalState (charts i).flow u) (canonicalState (charts i).flow v)) ∧
              ∀ t ∈ Icc (min u.1.1 v.1.1) (max u.1.1 v.1.1),
                closedBall (canonicalState (charts i).flow ((t, u.1.2), u.2)).1 εw ⊆
                  ball 0 (2 * r)) := by
  have hb : 0 < b := p.radius_pos.trans_le hpb
  have hpK : closedBall p.center p.radius ⊆ closedBall (0 : Euclidean n) b := by
    rw [hp0]
    exact closedBall_subset_closedBall hpb
  have hKU : closedBall (0 : Euclidean n) b ⊆ ball 0 B := closedBall_subset_ball hbB
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr,
    ρ, εw, hρ, hρτ, hεw, centers, w, hlow₀, hclosure, hfreq, hprotect⟩ :=
    exists_projected_signed_uniform_protection (N := embeddingDimension n) hn hD T G assign
      (isCompact_closedBall _ _) hKU hball p hp0 hpK hr₀ hradius
  obtain ⟨ηref, hηref, hcurrent⟩ := exists_current_frame_and_extension_neighborhood
    p hp0 hpb hbB m hm hδ hεlow
  refine ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr,
    ρ, εw, hρ, hρτ, hεw, centers, w, ηref, hηref, ?_⟩
  intro Gref hBref href
  obtain ⟨Z₀, hZ₀, dmap, hdmap, hnear⟩ := hcurrent Gref hBref href
  let lift (F : PrimitiveMapNeighborhood Gref B (m + 2) dmap) :
      ProjectedImmersionNeighborhood (embeddingDimension n) (ball 0 B) (closedBall 0 b) δ :=
    ⟨F.1, F.2.1.contDiffOn, (hnear F.1 F.2.1 F.2.2).1,
      (hnear F.1 F.2.1 F.2.2).2.1, (hnear F.1 F.2.1 F.2.2).2.2.1⟩
  let hlow (F : PrimitiveMapNeighborhood Gref B (m + 2) dmap) := hlow₀ (lift F)
  let family := fun z : PrimitiveMapNeighborhood Gref B (m + 2) dmap × closedBall (0 : Euclidean n) r ↦
    currentGroup T assign R (ProjectedStressFrame.projectedStress (lift z.1).1)
      (frameOfImmersion isOpen_ball (lift z.1)).2.1 (hlow z.1) z.2
  have hdir : directionSet family (groupCube D assign) ⊆
      directionSet (fun z : ProjectedImmersionNeighborhood (embeddingDimension n)
          (ball 0 B) (closedBall 0 b) δ × closedBall (0 : Euclidean n) r ↦
        currentGroup T assign R (ProjectedStressFrame.projectedStress z.1.1)
          (frameOfImmersion isOpen_ball z.1).2.1 (hlow₀ z.1) z.2) (groupCube D assign) := by
    rintro v ⟨z, q, he⟩
    exact ⟨(lift z.1, z.2), q, he⟩
  refine ⟨Z₀, hZ₀, dmap, hdmap, lift, fun _ ↦ rfl, hlow,
    (closure_mono hdir).trans hclosure, fun z q ↦ hfreq (lift z.1, z.2) q, ?_, ?_⟩
  · intro Dprofile order
    obtain ⟨Cprofile, hCprofile, hprofile⟩ := extendedReducedCoefficients_preserves_profile
      (N := embeddingDimension n) p Z₀ hZ₀ isOpen_ball
      (isCompact_closedBall (0 : Euclidean n) (3 * r)) (hpK.trans hKU) Dprofile order
    exact ⟨Cprofile, hCprofile, fun slow hslow Q ↦
      hprofile slow hslow Q.1 Q.2.1 (lift Q).2.2.1 (lift Q).2.2.2.1⟩
  intro Q
  have hcore : closedBall (0 : Euclidean n) (3 * r) ⊆ closedBall p.center p.radius := by
    rw [hp0]
    exact closedBall_subset_closedBall hrp.le
  have hF : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ 2 Q.1 x :=
    fun _ _ ↦ Q.2.1.contDiffAt.of_le (by simp)
  have hrank : HasFullNormalRankOn Q.1 (closedBall p.center p.radius) :=
    fun x hx ↦ (lift Q).2.2.2.1 x (hKU (hpK hx))
  obtain ⟨heq, hrest⟩ := hprotect (lift Q)
  refine ⟨(hnear Q.1 Q.2.1 Q.2.2).2.2.2.1, (hnear Q.1 Q.2.1 Q.2.2).2.2.2.2,
    (extendedReducedCoefficients_eqOn p Z₀ Q.1).mono hcore,
    fun x a i k ↦ extendedReducedCoefficients_principal p Z₀ hF hrank x a i k,
    fun u x hx i ↦ extendedReducedCoefficientOperator_eq p Z₀ hF hrank u (hcore hx) i,
    heq, ?_⟩
  obtain ⟨hflow, charts, hcompact, hzero, hsource, hbuffer, hsegment, hchain,
    hcover, hrect, hweights⟩ := hrest
  refine ⟨hflow, charts, hcompact, hzero, hsource, hbuffer, hsegment, hchain,
    hcover, hrect, hweights, ?_, ?_, ?_⟩
  · intro z hz v k hsteps
    exact hchain z hz v k
      (selectedFactor_chain_is_characteristic_chain charts w hρ hεw hrect hsteps)
  · intro z v k hsteps helliptic
    exact elliptic_selectedFactor_chain_eq charts w hρ hεw
      (W := ball 0 (2 * r)) hrect hsteps helliptic
  · intro i q backward Ksource hKsource v hv
    exact (w i q).completeImage_has_buffered_segments (charts i).chart hρ hεw
      (fun u hu ↦ (hrect i q.1 q.2 u hu).1)
      (fun u hu ↦ (hrect i q.1 q.2 u hu).2) hKsource hv

end JanetCartan.ProtectedFlow
