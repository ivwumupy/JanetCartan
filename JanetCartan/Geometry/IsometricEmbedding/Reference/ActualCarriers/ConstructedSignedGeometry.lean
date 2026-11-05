module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedSignedGeometry.FrozenBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedSignedGeometry.Comparison

/-!
# Complete signed geometry of the constructed carriers

Step 2 of `app:ch_seed:prop:seed-actual-menu` and
`app:rem:exhaustive-signed-pairs`, for the very same quantitative family
returned by `exists_constructed_carrier_phases`. The labels, common frame
threshold, angular gap and true-frequency constants precede the frame.
Frozen pair bounds and actual comparisons are proved by the imported leaves.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.ConstructedSignedGeometry
open FrozenMenu CurrentFullPhase SignedPairs

/-- Literal radially scaled gradients of the supplied current charts.
No chart, Hamilton family or frozen patch is replaced
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
def currentGroup {n : ℕ} {D : CoverData n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {G : Type*} (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : G → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
        (T i).family.threshold)
    (x : Euclidean n) (g : G) (z : Euclidean 3) : Euclidean n :=
  R g • (T (assign g)).carrierGradient ⟨Q, hQ, hlow (assign g)⟩ x z

/-- Instantiate complete signed-family stability for the actual constructed
carriers, from primitive componentwise frame `C⁶` closeness alone. All groups
refer to literal patch indices, with arbitrary duplicates and empty families
allowed. One compact symmetric `angularSet` contains the closure over *all*
admissible frames and physical points, including limiting short chords, and
is quantitatively separated from `cubeBadSubspaceUnion`.

The lower projection bound and both frequency bounds retain `q.beat`: it is
`‖z-w‖` for distinct-parameter differences and `1` for sums and cross pairs.
The fixed constants thus give the true frequencies `lam * ‖z-w‖` and `lam`,
including doubled plus terms but excluding the repeated-index zero difference
(`app:ch_seed:eq:seed-actual-chord`; `app:rem:exhaustive-signed-pairs`).

The parent construction supplies the same `T` and combines this threshold
with the carrier-rank and singular-gap thresholds. No frozen pair bound,
actual gradient comparison, or angular inclusion is an input here. -/
theorem exists_constructed_signed_geometry {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    {r : ℝ} (_hr : 0 < r) (hradius : ∀ i, r < (T i).physicalRadius) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ δ γ a A : ℝ, 0 < δ ∧ 0 < γ ∧ 0 < a ∧ 0 < A ∧
        IsCompact (angularSet n γ) ∧
        (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
        (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n, γ ≤ dist v w) ∧
        Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) ∧
        ∃ hlow : ∀ (Q : FrameNeighborhood U K δ) i,
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (Q.1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
        let g := fun p : FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r ↦
          currentGroup T assign R p.1.1 p.1.2.1 (hlow p.1) p.2;
        closure (directionSet g (groupCube D assign)) ⊆ angularSet n γ ∧
        ∀ p (q : Pair G (Euclidean 3) (groupCube D assign)),
          (∀ L ∈ cubeBadSubspaces n, a * q.beat ≤ ‖projectAway L (q.vector (g p))‖) ∧
          q.vector (g p) ≠ 0 ∧
          ∀ lam : ℝ, 0 ≤ lam →
            a * (lam * q.beat) ≤ ‖lam • q.vector (g p)‖ ∧
            ‖lam • q.vector (g p)‖ ≤ A * (lam * q.beat) := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨R, hR, hinj, a, A, ha, hA, hl, hu⟩ :=
    exists_frozen_signed_pair_bounds hD G assign
  obtain ⟨_, _, B, _, _, _, hB, hmax⟩ := exists_common_phase_buffers
    (fun _ : G ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) R
    (fun _ ↦ zero_lt_one) (fun _ ↦ zero_lt_one)
  let ε := a / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : 2 * ε < a := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, hlow, hcomp⟩ := exists_common_carrier_comparison_threshold
    hD T hK hKU hball (div_pos hε hB)
  let X := FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r
  let g (p : X) := currentGroup T assign R p.1.1 p.1.2.1 (hlow p.1) p.2
  let P (i : G) := D.patches (assign i).1 (assign i).2
  let f' (i : G) (z : Euclidean 3) := R i • fderiv ℝ (P i).toFun z
  let g' (p : X) (i : G) (z : Euclidean 3) := R i •
    fderiv ℝ ((T (assign i)).carrierGradient
      ⟨p.1.1, p.1.2.1, hlow p.1 (assign i)⟩ p.2) z
  have hP (i : G) : (P i).IsValid c C := (hD.2.2.2.2.1 _ _).1
  have hRp (i : G) : 0 < R i := zero_lt_one.trans_le (hR i)
  have hx (p : X) (i : _) : (p.2 : Euclidean n) ∈ ball (0 : Euclidean n)
      (T i).physicalRadius := closedBall_subset_ball (hradius i) p.2.property
  have hf (i : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign i) :
      HasFDerivWithinAt (frozenGroup D assign R i) (f' i z) (groupCube D assign i) z := by
    have hp := (hP i).2.2.2.1.contDiffAt ((isOpen_parameterInterior _).mem_nhds
      (parameterCube_subset_doubledInterior (hP i).1 hz))
    exact ((hp.differentiableAt (by simp)).hasFDerivAt.const_smul (R i)).hasFDerivWithinAt
  have hg (p : X) (i : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign i) :
      HasFDerivWithinAt (g p i) (g' p i z) (groupCube D assign i) z := by
    have hopen : IsOpen (ball (0 : Euclidean n) (T (assign i)).physicalRadius ×ˢ
        parameterInterior (2 * (P i).radius)) :=
      isOpen_ball.prod (isOpen_parameterInterior (2 * (P i).radius))
    have hjoint : ContDiffAt ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦
        (T (assign i)).carrierGradient ⟨p.1.1, p.1.2.1, hlow p.1 (assign i)⟩ q.1 q.2)
        ((p.2 : Euclidean n), z) :=
      ((T (assign i)).carrierGradient_smooth (hP i)
        ⟨p.1.1, p.1.2.1, hlow p.1 (assign i)⟩).contDiffAt
          (hopen.mem_nhds ⟨hx p (assign i), parameterCube_subset_doubledInterior (hP i).1 hz⟩)
    have hpair : ContDiffAt ℝ ∞ (fun w : Euclidean 3 ↦ ((p.2 : Euclidean n), w)) z :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (((hjoint.comp z hpair).differentiableAt (by simp)).hasFDerivAt.const_smul
      (R i)).hasFDerivWithinAt
  have he (p : X) (i : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign i) :
      ‖g' p i z - f' i z‖ ≤ ε := by
    dsimp only [g', f']
    rw [← smul_sub (R i)
      (fderiv ℝ ((T (assign i)).carrierGradient
        ⟨p.1.1, p.1.2.1, hlow p.1 (assign i)⟩ p.2) z)
      (fderiv ℝ (P i).toFun z), norm_smul, Real.norm_eq_abs, abs_of_pos (hRp i)]
    calc
      _ ≤ B * (ε / B) := mul_le_mul (hmax i).2.2
        (hcomp p.1 (assign i) p.2 (hx p (assign i)) z hz).2 (norm_nonneg _) hB.le
      _ = ε := mul_div_cancel₀ ε hB.ne'
  have hv (p : X) (i : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign i) :
      ‖g p i z - frozenGroup D assign R i z‖ ≤ ε := by
    change ‖R i • _ - R i • _‖ ≤ ε
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hRp i)]
    calc
      _ ≤ B * (ε / B) := mul_le_mul (hmax i).2.2
        (hcomp p.1 (assign i) p.2 (hx p (assign i)) z hz).1 (norm_nonneg _) hB.le
      _ = ε := mul_div_cancel₀ ε hB.ne'
  obtain ⟨hγ, hcompact, hsym, hclosure, hgap, hpairs⟩ := signed_family_stability hn
    (fun i ↦ convex_parameterCube (P i).radius) hε.le hsmall hA hf hg he hv hl hu
  exact ⟨R, hR, hinj, δ, (a - 2 * ε) / (A + 2 * ε), a - 2 * ε, A + 2 * ε,
    hδ, hγ, by linarith, by positivity, hcompact, hsym, hgap,
    angularSet_disjoint_bad hγ, hlow, hclosure, hpairs⟩

end JanetCartan.ActualCarriers.ConstructedSignedGeometry
