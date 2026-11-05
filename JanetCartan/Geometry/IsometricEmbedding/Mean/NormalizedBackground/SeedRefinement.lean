module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedPhase

/-!
# A finite common refinement of the constructed seed transports

The compact original carrier cubes are covered by finitely many fixed balls.
A single physical ball works for all retained patches and all selected local
unit transports, before derivative orders or subsequent source scales are chosen
(`app:ch_background:prop:bg-normalized`). The flow, inverse footpoint, scalar
and selected nullvectors are precisely those constructed in `SeedTransport`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude

/-- Finite carrier refinement and one buffered physical ball for the actual
unit-initial seed transports. The compact inner carrier balls cover every
original carrier cube; their doubled open balls lie in the same genuine flow
tubes (`app:ch_background:prop:bg-normalized`). -/
theorem exists_refined_flat_seed_unit_transports {n : ℕ} {A : Type} [Fintype A]
    (hn : 2 ≤ n) (G₀ : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (hUG : U ⊆ G₀.domain.chart n)
    {P : A → Patch n} {c₀ C₀ : A → ℝ} (hP : ∀ a, (P a).IsValid (c₀ a) (C₀ a))
    (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ K)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ θ : ℝ, 0 < θ ∧ θ < cap ∧ θ ≤ 1 ∧
      ∃ G : FlatReference n, G.domain = G₀.domain ∧ G.map = sourceDilation G₀.map θ ∧
      ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) U,
      ∃ hlow : ∀ a, cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (projectedStress G.map - fun _ ↦ cubeStress n) < (T a).family.threshold,
      ∃ centers : (a : A) → Finset (parameterCube (P a).radius),
      ∃ radius : (a : A) → centers a → ℝ,
        (∀ a j, 0 < radius a j) ∧
        (∀ a, parameterCube (P a).radius ⊆ ⋃ j : centers a,
          ball j.1.1 (radius a j / 4)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ball (0 : Euclidean n) (2 * ε) ⊆ G.domain.chart n ∧
        (∀ a, 2 * ε < (T a).physicalRadius) ∧
        ∀ a : A,
        let T := T a
        let P := P a
        let Q := ⟨projectedStress G.map, hQ, hlow a⟩
        let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
        ∀ j : centers a, let z := j.1.1; let r := radius a j
        ∃ row col : Fin n, ∃ τ R : ℝ, 0 < τ ∧ 0 < R ∧
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ball (0 : Euclidean n) (2 * ε) ×ˢ ball z (r / 2) ⊆ C ⁻¹' D) ∧
          IsOpen D ∧
          Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          C ⁻¹' D ⊆ U ×ˢ parameterInterior (3 * P.radius / 2) ∧
          D ⊆ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
          ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Φ q))
            (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D
            (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), Φ (0, p) = p) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            (Φ (t, p)).2 = p.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            HasDerivAt (fun s ↦ Φ (s, p))
              ((adaptedCoordinates T.data.adapted
                (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          let α := carrierScalarAmplitude T Q G.map row col Φ Y (fun _ ↦ 1)
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
            α (T.data.adapted.embedding p.1, p.2) = 1) ∧
          (∀ w ∈ C ⁻¹' D, 0 < α w ∧ α w • carrierNullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
              carrierTransportPotential T Q G.map row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
              (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator G.map Q.1
            (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) ∧
          ContDiffOn ℝ ∞ (carrierNullvector T Q col) (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (carrierTransportPotential T Q G.map row col) (C ⁻¹' D) ∧
          (∀ w ∈ C ⁻¹' D, carrierAdaptedDenominator T Q row col w ≠ 0) := by
  classical
  obtain ⟨θ, hθ, hcapθ, hθ1, G, hdomain, hmap, hQ, hlow, hlocal⟩ :=
    exists_finite_flat_seed_unit_transports hn G₀ hUG hP T hK hKU hball hcap
  let C a := coordinates (Z := Euclidean 3) (adaptedCoordinates (T a).data.adapted)
  choose row col τ R hτ hR D Φ Y hspec using
    fun a (z : parameterCube (P a).radius) ↦ hlocal a z.1 z.2
  have hneighborhood a (z : parameterCube (P a).radius) :
      ∃ r > 0, ball ((0 : Euclidean n), z.1) r ⊆ C a ⁻¹' D a z := by
    have hΩ : IsOpen (C a ⁻¹' D a z) := (hspec a z).1.preimage (C a).continuous
    have hz : ((0 : Euclidean n), z.1) ∈ C a ⁻¹' D a z := by
      apply (hspec a z).2.1
      simp only [C, coordinates_apply, map_zero, Prod.fst_zero, Prod.snd_zero]
      exact ⟨⟨neg_neg_of_pos (hτ a z), hτ a z⟩,
        mem_ball_self (div_pos (hR a z) (by norm_num))⟩
    exact Metric.isOpen_iff.mp hΩ _ hz
  choose radius hradius hballD using hneighborhood
  have hcover a : parameterCube (P a).radius ⊆
      ⋃ z : parameterCube (P a).radius, ball z.1 (radius a z / 4) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (div_pos (hradius a ⟨z, hz⟩) (by norm_num))⟩
  choose centers hcenters using fun a ↦
    (isCompact_parameterCube (P a).radius).elim_finite_subcover
      (fun z : parameterCube (P a).radius ↦ ball z.1 (radius a z / 4))
      (fun _ ↦ isOpen_ball) (hcover a)
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    (finite_range (fun j : (a : A) × centers a ↦ radius j.1 j.2.1)).isCompact.exists_forall_le'
      continuousOn_id (by rintro x ⟨j, rfl⟩; exact hradius j.1 j.2.1)
  obtain ⟨p₀, hp₀, hphysical⟩ :=
    (finite_range (fun a ↦ (T a).physicalRadius)).isCompact.exists_forall_le'
      continuousOn_id (by rintro x ⟨a, rfl⟩; exact (T a).physicalRadius_pos)
  let ε := min (r₀ / 4) (min (p₀ / 4) (G.domain.chartRadius / 4))
  have hchart : 0 < G.domain.chartRadius := G.domain.coreRadius_pos.trans
    G.domain.coreRadius_lt_chartRadius
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεr : 2 * ε < r₀ := by
    have hh : ε ≤ r₀ / 4 := min_le_left _ _
    linarith
  have hεp : 2 * ε < p₀ := by
    have hh : ε ≤ p₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hεG : 2 * ε < G.domain.chartRadius := by
    have hh : ε ≤ G.domain.chartRadius / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨θ, hθ, hcapθ, hθ1, G, hdomain, hmap, hQ, hlow, centers,
    (fun a j ↦ radius a j.1), (fun a j ↦ hradius a j.1), ?_, ε, hε,
    ball_subset_ball hεG.le, (fun a ↦ hεp.trans_le (hphysical _ ⟨a, rfl⟩)), ?_⟩
  · intro a z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcenters a hz)
    obtain ⟨hj, hzj⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hzj⟩
  · intro a
    dsimp only
    intro j
    refine ⟨row a j.1, col a j.1, τ a j.1, R a j.1, hτ a j.1, hR a j.1,
      D a j.1, Φ a j.1, Y a j.1, ?_, hspec a j.1⟩
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    apply hballD a j.1
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hx).trans (hεr.trans_le (hsmall _ ⟨⟨a, j⟩, rfl⟩)),
      (mem_ball.mp hz).trans (half_lt_self (hradius a j.1))⟩

end JanetCartan.NormalizedBackground
