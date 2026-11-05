module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.LowBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Basic

/-!
# Fixed literal incidence coordinates

The independent variables are `((x,k),t)`. Their coordinate projections and
the affine first-parameter line give fixed smooth pullbacks, with range
containments proved from the elementary coordinate buffers in Step 3 of
`app:ch_seed:prop:seed-actual-menu`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.ConstructedCarrierJets

variable {n : ℕ}

/-- The literal map into physical/patch variables in actual incidence
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def incidenceCarrierMap (z : Euclidean 3) (p : (Euclidean n × Euclidean n) × ℝ) :
    Euclidean n × Euclidean 3 := (p.1.1, incidenceParameter z p.2)

/-- Fixed global smoothness supplies every derivative budget of the
incidence pullback (`app:ch_seed:eq:seed-phase-tame`). -/
theorem incidenceCarrierMap_smooth (z : Euclidean 3) :
    ContDiff ℝ ∞ (incidenceCarrierMap (n := n) z) :=
  (contDiff_fst.fst).prodMk (contDiff_const.add (contDiff_snd.smul contDiff_const))

/-- Product-ball membership gives the physical, covector and scalar
coordinate bounds, before any current frame is chosen
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem incidence_ball_coordinates {a p : (Euclidean n × Euclidean n) × ℝ} {ρ : ℝ}
    (hp : p ∈ closedBall a ρ) :
    p.1.1 ∈ closedBall a.1.1 ρ ∧ p.1.2 ∈ closedBall a.1.2 ρ ∧
      p.2 ∈ Icc (a.2 - ρ) (a.2 + ρ) := by
  have h := mem_closedBall.mp hp
  rw [Prod.dist_eq, Prod.dist_eq, max_le_iff, max_le_iff] at h
  exact ⟨h.1.1, h.1.2, by
    have ht := abs_le.mp (show |p.2 - a.2| ≤ ρ by simpa only [Real.dist_eq] using h.2)
    constructor <;> linarith [ht.1, ht.2]⟩

/-- Elementary coordinate containments put the literal incidence pullback
in the fixed compact physical/parameter buffers. No dynamic range hypothesis
is required (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem incidenceCarrierMap_mapsTo {a : (Euclidean n × Euclidean n) × ℝ} {ρ : ℝ}
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)} (z : Euclidean 3)
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz) :
    MapsTo (incidenceCarrierMap z) (closedBall a ρ) (Kx ×ˢ Kz) := by
  intro p hp
  exact ⟨hx (incidence_ball_coordinates hp).1, hz _ (incidence_ball_coordinates hp).2.2⟩

/-- The physical and carrier coordinate maps have fixed all-order pullback
constants. These are the direct inputs to the frame and gradient budgets
for `exists_cNorm_incidence_root_le_reserve_six`
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_incidence_coordinate_budgets
    (a : (Euclidean n × Euclidean n) × ℝ) (ρ : ℝ)
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)}
    (hKx : IsCompact Kx) (hKz : IsCompact Kz) (z : Euclidean 3)
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz) :
    ∃ A B D : ℕ → ℝ, (∀ m, 0 < A m) ∧ (∀ m, 0 < B m) ∧ (∀ m, 0 < D m) ∧
      (∀ (Q : Euclidean n → Fin n → MetricTensor n),
        (∀ x ∈ Kx, ContDiffAt ℝ ∞ Q x) → ∀ m,
        cNorm (closedBall a ρ) m (fun p ↦ Q p.1.1) ≤ A m * cNorm Kx m Q) ∧
      (∀ (ξ : Euclidean n × Euclidean 3 → Euclidean n),
        (∀ q ∈ Kx ×ˢ Kz, ContDiffAt ℝ ∞ ξ q) → ∀ m,
        cNorm (closedBall a ρ) m (fun p ↦ ξ (p.1.1, incidenceParameter z p.2)) ≤
          B m * cNorm (Kx ×ˢ Kz) m ξ) ∧
      (∀ m, cNorm (closedBall a ρ) m (fun p ↦ p.1.2) ≤ D m) := by
  obtain ⟨A, hA, ha⟩ := exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) (isCompact_closedBall a ρ) hKx
    (ψ := fun p : (Euclidean n × Euclidean n) × ℝ ↦ p.1.1)
    (fun _ _ ↦ contDiff_fst.fst.contDiffAt)
    (fun _ hp ↦ hx (incidence_ball_coordinates hp).1)
  obtain ⟨B, hB, hb⟩ := exists_cNorm_fixed_pullback_le
    (G := Euclidean n) (isCompact_closedBall a ρ) (hKx.prod hKz)
    (fun _ _ ↦ (incidenceCarrierMap_smooth z).contDiffAt)
    (incidenceCarrierMap_mapsTo z hx hz)
  refine ⟨A, B, fun m ↦ 1 + cNorm (closedBall a ρ) m (fun p ↦ p.1.2), hA, hB,
    fun m ↦ by linarith [cNorm_nonneg (closedBall a ρ) m (fun p ↦ p.1.2)], ha, hb, ?_⟩
  intro m
  linarith

end JanetCartan.ActualCarriers.ConstructedCarrierJets
