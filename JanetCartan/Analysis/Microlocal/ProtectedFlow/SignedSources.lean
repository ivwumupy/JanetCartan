module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.AngularNeighborhood
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ExtendedPhaseCover
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedSignedGeometry

/-!
# The complete source neighborhoods of the retained signed carriers

This instantiates the angular neighborhood construction with the same radially
labelled carrier family returned by `ConstructedSignedGeometry`. No new carrier
chart is chosen. The closure includes all limiting difference chords, and every
pair retains its true beat (`app:ch_regular:thm:no-return`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs

/-- Construct buffered source neighborhoods from primitive frame closeness for
the retained carrier family. This supplies `Ω₁`, its compactness and its actual
forbidden-cone avoidance to `exists_extended_frame_comparison_cover`. The labels,
thresholds, neighborhoods, angular buffer and true-frequency constants precede
the current frame (`app:ch_regular:thm:no-return`). -/
theorem exists_constructed_source_neighborhoods {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    {r : ℝ} (hr : 0 < r) (hradius : ∀ i, r < (T i).physicalRadius) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ δ a A ε : ℝ, 0 < δ ∧ 0 < a ∧ 0 < A ∧ 0 < ε ∧
      ∃ Ω₀ Ω₁ : Set (Euclidean n),
        IsCompact Ω₀ ∧ IsCompact Ω₁ ∧ Ω₀ ⊆ interior Ω₁ ∧
        (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
        (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
        Disjoint Ω₁ (cubeBadSubspaceUnion n) ∧
        (∀ v ∈ Ω₁, closedBall v ε ⊆ (cubeBadSubspaceUnion n)ᶜ) ∧
        ∃ hlow : ∀ (Q : FrameNeighborhood U K δ) i,
          cNorm (closedBall (0 : Euclidean n)
            (T i).data.localReference.stateRadius) 6 (Q.1 - fun _ ↦ cubeStress n) <
              (T i).family.threshold,
        let family := fun p : FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r ↦
          currentGroup T assign R p.1.1 p.1.2.1 (hlow p.1) p.2;
        closure (directionSet family (groupCube D assign)) ⊆ interior Ω₀ ∧
        ∀ p (q : Pair G (Euclidean 3) (groupCube D assign)),
          (∀ L ∈ cubeBadSubspaces n, a * q.beat ≤ ‖projectAway L (q.vector (family p))‖) ∧
          q.vector (family p) ≠ 0 ∧
          ∀ lam : ℝ, 0 ≤ lam →
            a * (lam * q.beat) ≤ ‖lam • q.vector (family p)‖ ∧
            ‖lam • q.vector (family p)‖ ≤ A * (lam * q.beat) := by
  obtain ⟨R, hR, hinj, δ, γ, a, A, hδ, hγ, ha, hA,
    _hcompact, _hsym, _hgap, _hdisj, hlow, hclosure, hfreq⟩ :=
    exists_constructed_signed_geometry hn hD T G assign hK hKU hball hr hradius
  obtain ⟨ε, hε, Ω₀, Ω₁, hΩ₀, hΩ₁, hinner, hnested, hs₀, hs₁,
    hann, hbad, hbuffer⟩ := exists_signed_angular_neighborhoods hγ
  exact ⟨R, hR, hinj, δ, a, A, ε, hδ, ha, hA, hε, Ω₀, Ω₁,
    hΩ₀, hΩ₁, hnested, hs₀, hs₁, hann, hbad, hbuffer, hlow,
    hclosure.trans hinner, hfreq⟩

/-- The fixed physical source cutoff, equal to one on the half-radius core.
Its actual closed support is the source ball in
`app:ch_regular:thm:no-return`. -/
def sourceCutoff {n : ℕ} {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : Euclidean n) :=
  ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

/-- The source ball is the actual topological support, including its boundary
(`app:ch_regular:defn:protected-saturation`). -/
theorem tsupport_sourceCutoff {n : ℕ} {r : ℝ} (hr : 0 < r) :
    tsupport (sourceCutoff (n := n) hr) = closedBall (0 : Euclidean n) r :=
  (sourceCutoff hr).tsupport_eq

/-- Every source amplitude multiplied by this fixed cutoff has its actual
closed support in the complete source ball. No pointwise support sampling is
used (`app:ch_regular:defn:protected-saturation`). -/
theorem tsupport_sourceCutoff_smul_subset {n : ℕ} {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (f : Euclidean n → V) :
    tsupport (fun x ↦ sourceCutoff hr x • f x) ⊆ closedBall (0 : Euclidean n) r := by
  rw [← tsupport_sourceCutoff hr]
  exact tsupport_smul_subset_left (f := (sourceCutoff (n := n) hr : Euclidean n → ℝ))
    (g := f)

end JanetCartan.ProtectedFlow
