module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.UniformCarrier
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalCompleteSource
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.InitializedApplication

/-!
# Reflected terminal protection from the original relative no-return cover

The relative signed producer is applied on the supplied original cover, patch
family, extension and reference. Its actual comparison charts discharge every
comparison premise of the uniform carrier deduction. The map-preserving lift
is retained and the common C³ bound is derived from its immersion neighborhood.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open ProtectedFlow
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference
open GeometricProfile ProtectedFlow SelectedSectorProtection SelectedEvenProofMasks
open ProtectedMasks RegularSector.Characteristic FiniteChain.Graph

/-- Apply the signed no-return producer on the original retained data, before
any current map or finite word. All comparison charts are constructed, and the
SAME full coefficient extension is used in every complete root segment. The
source and diagonal branches, as well as literal covector reflection, remain
in one protected annular carrier. The remaining selected-root primitives are
the exact outputs of `selected_root_mask_primitives` and radial refinement;
no all-chain or reachable-set protection is assumed
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_original_signed_reflected_terminal_carrier {d : ℕ} (hn : 5 ≤ d+1)
    {D : CoverData (d+1)} {c C : ℝ} (hD : D.IsValid c C)
    {b B : ℝ} (hbB : b < B)
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 B) isOpen_ball)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (hball : ∀ i, closedBall (0 : Euclidean (d+1)) (T i).data.localReference.stateRadius ⊆ closedBall 0 b)
    (p : BallExtension.Parameters (Euclidean (d+1))) (hp0 : p.center = 0)
    (hpb : p.radius ≤ b)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hradius : ∀ i, r₀ < (T i).physicalRadius)
    (m : ℕ) (hm : 6 ≤ m) {εlow : ℝ} (hεlow : 0 < εlow) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ r δ a A ε τ εx : ℝ, 0 < r ∧ r < r₀ ∧ 3 * r < p.radius ∧
        0 < δ ∧ 0 < a ∧ 0 < A ∧ 0 < ε ∧ 0 < τ ∧ 0 < εx ∧
      ∃ Ω₀ Ω₁ Γin Γout : Set (Euclidean (d+1)),
        IsCompact Ω₀ ∧ IsCompact Ω₁ ∧ IsCompact Γin ∧ ∃ _hΓout : IsCompact Γout,
        Ω₀ ⊆ interior Ω₁ ∧ Ω₁ ⊆ interior Γin ∧ Γin ⊆ interior Γout ∧
        (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
        (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
        (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
        Γout ⊆ (cubeBadSubspaceUnion (d+1))ᶜ ∧
        (0 : Euclidean (d+1)) ∉ Γout ∧
        (∀ ξ ∈ Γout, determinant (cubeStress (d+1)) ξ = 0 →
          fderiv ℝ (determinant (cubeStress (d+1))) ξ ≠ 0) ∧
      ∃ aperture > (0 : ℝ), (∀ ξ ∈ Γout, ∀ i, |ξ i| < aperture) ∧
      ∃ θ > (0 : ℝ),
        (∀ ξ ∈ Γin, closedBall ξ θ ⊆ interior Γout ∧
          closedBall (-ξ) θ ⊆ interior Γout) ∧
      ∃ ηref > (0 : ℝ), ∀ Gref : FlatReference (d+1), B < Gref.domain.chartRadius →
        (∀ i, cNorm (closedBall (0 : Euclidean (d+1)) b) m
          (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i - cubeStress (d+1) i) < ηref) →
      ∃ Z₀ : Euclidean (d+1) → Fin (d+1) × Fin (d+1) → ℝ, ContDiff ℝ ∞ Z₀ ∧
      ∃ dmap > (0 : ℝ),
      ∃ lift : PrimitiveMapNeighborhood Gref B (m + 2) dmap →
        ProjectedImmersionNeighborhood (embeddingDimension (d+1)) (ball 0 B) (closedBall 0 b) δ,
      (∀ F, (lift F).1 = F.1) ∧
      (∀ F : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
        EqOn (extendedProjectedStress p F.1) (ProjectedStressFrame.projectedStress F.1)
          (closedBall 0 (3 * r)) ∧
        ∀ x a i k, extendedReducedCoefficients p Z₀ F.1 x (.inl (a, i, k)) =
          extendedProjectedStress p F.1 x i a k) ∧
      ∀ S : Set (Euclidean (d+1) × Euclidean (d+1)), IsCompact S →
        (∀ q ∈ S, q.1 ∈ ball 0 r ∧ q.2 ≠ 0 ∧ normalizedCovector q.2 ∈ Ω₀) →
      ∃ lo > (0 : ℝ), ∃ hi > lo, ∃ εterminal > (0 : ℝ),
      ∀ F : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
      let Q := extendedProjectedStress p (lift F).1
      Q = extendedProjectedStress p F.1 ∧
    ∀ {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
      (η₀ : J → Euclidean d) (εroot G : J → ℝ), (∀ j, 0 ≤ G j) →
    ∀ {κ Δ : ℝ}, 0 < κ → 0 ≤ Δ →
    ∀ (i : J → Fin (d+1)) (h : J → RootState (Euclidean d) → ℝ)
      (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d+1)))
      (χsource χout : J → (Euclidean (d+1)) → ℂ),
      (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
      (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
        determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
          ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
          ((coordinateSplit (i j)).symm (h j v, v.2.2))
          ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
      (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2*r) →
      (∀ j v, v ∈ K j → v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
        (1/2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
      (∀ j v, v ∈ U j ∪ K j →
        (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ closedBall 0 r) →
      (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
    ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
      (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
        (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
      (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
      ∀ depth, reachableAt (reflectedProofRelation
        (physicalDirectRelation i h Φ U K W χsource χout Δ)) S depth ⊆
          protectedAnnularCarrier (closedBall 0 r) lo hi εterminal Γout := by
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx,
    hr, hrr₀, hrp, hδ, ha, hA, hε, hτ, hεx,
    Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, hzero, hregular,
    aperture, hAp, hApξ, θ, hθ, houter, s, g, hgr,
    cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, ρ, εw, hρ, hρτ, hεw,
    centers, w, ηref, hηref, hproduce⟩ :=
    exists_primitive_signed_complete_source_terminal_cover hn hD hbB T G assign
      hball p hp0 hpb hr₀ hradius m hm hεlow
  refine ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, hzero, hregular,
    aperture, hAp, hApξ, θ, hθ, houter, ηref, hηref, ?_⟩
  intro Gref hBref href
  obtain ⟨Z₀, hZ₀, dmap, hdmap, lift, hsame, hlow, hclosure, hfreq, hprofile, hcurrent⟩ :=
    hproduce Gref hBref href
  refine ⟨Z₀, hZ₀, dmap, hdmap, lift, hsame, ?_, ?_⟩
  · intro F
    obtain ⟨_, _, _, hprincipal, _, hext, _⟩ := hcurrent F
    exact ⟨hext, hprincipal⟩
  intro S hS hsource
  obtain ⟨lo, hlo, hi, hhi, εterminal, hεterminal, hcarrier⟩ :=
    exists_uniform_reflected_terminal_carrier hS hr hcgraph hCgraph hε
      (fun q hq ↦ ball_subset_closedBall (hsource q hq).1)
      (closedBall_subset_ball (by linarith only [hr]))
      (fun q hq ↦ ⟨(hsource q hq).1, (hsource q hq).2.1,
        interior_subset (hΩnest (hsource q hq).2.2)⟩)
      (hΩΓ.trans (interior_subset.trans hΓnest))
  obtain ⟨Mglobal, hMglobal, hbudget⟩ :=
    exists_uniform_extendedProjectedStress_cNorm_three_bound
      (N := embeddingDimension (d+1)) isOpen_ball
      (isCompact_closedBall (0 : Euclidean (d+1)) b)
      (closedBall_subset_ball hbB) p
      (by rw [hp0]; exact closedBall_subset_closedBall hpb) hδ (2*r)
  refine ⟨lo, hlo, hi, hhi, εterminal, hεterminal, ?_⟩
  intro F Q
  refine ⟨congrArg (extendedProjectedStress p) (hsame F), ?_⟩
  intro J _ ℓ η₀ εroot Gbound hG κ Δ hκ hΔ
    i h Φ U K Droot W χsource χout hDroot hh hroot hKD hW hprimitive hbase hgap
    z Rflow rFlow Tflow hflow htime hUflow
  have hQ : ContDiff ℝ ∞ Q :=
    selected_initialized_extendedPencil_contDiff hbB p hp0 hpb (lift F)
  have hQM : cNorm (closedBall 0 (2*r)) 3 Q ≤ Mglobal := hbudget (lift F)
  obtain ⟨_, _, _, _, _, _, _, charts, hderiv,
    hnorm, _, _, hcover, hbuffer, _⟩ := hcurrent F
  exact hcarrier ℓ η₀ εroot Gbound hG hMglobal hLx hκ hΔ Q hQ hQM
    i h Φ U K Droot W χsource χout hDroot hh hroot hKD hW hprimitive hbase hgap
    z Rflow rFlow Tflow hflow htime hUflow _ g charts
    (fun j ↦ by linarith only [hgr j, hr]) hderiv hnorm hcover
    (fun q hq ↦ (hbuffer q hq).trans (fun ξ hξ ↦
      interior_subset (hΓnest (interior_subset hξ.1))))

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
