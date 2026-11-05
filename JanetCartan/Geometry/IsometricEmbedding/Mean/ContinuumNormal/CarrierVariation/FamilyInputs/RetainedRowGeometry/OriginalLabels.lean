module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ChartAdapter
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.CarrierGraph
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedLeading.InitialBuffer

/-!
# Original scalar labels at incidence roots distinct from the cell center

Project the retained full-modulation working cylinder onto the actual carrier
coordinates. A time restriction preserves EVERY zero-position carrier center,
so it preserves the original finite carrier coverage. Forward-flow bounds
then control the original ODE footpoint without changing either center, radius,
minor or map. This supplies label ranges for the retained weighted comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier LeadingPrimitive PositiveReference PositiveReference.FlowConstruction

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The doubled working-ball containment exported by
`ChartCenters.CarrierData`, together with its carrier-graph containment,
puts the SAME carrier coordinates in the ORIGINAL scalar cylinder. The
incidence root is not identified with `zCell`. This is the scalar-domain
input of `exists_original_label_region` (`bg-Psi`, `bg-normalized`, and
`app:ch_waves:eq:joint-tame`). -/
theorem densityCoordinates_mem_original_cylinder
    (zCell : Euclidean 3) {L σ τ : ℝ} (hσ : 0 < σ)
    {E : Set (Euclidean n × CarrierParameter)}
    (hgraph : MapsTo (carrierGraph T) E
      (ball ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) σ))
    (hworking : closedBall ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zCell, T.reference.spatialPatch zCell)) (L / 64))) :
    MapsTo (densityCoordinates T) E
      (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64)) := by
  intro p hp
  have hm := hworking ((closedBall_subset_closedBall (by linarith : σ ≤ 2 * σ))
    (ball_subset_closedBall (hgraph hp)))
  obtain ⟨q, hq, heq⟩ := hm
  have hq' : coordinates (adaptedCoordinates T.data.adapted) (carrierGraph T p) ∈
      Icc (-τ / 2) (τ / 2) ×ˢ
        closedBall ((0 : Euclidean (n - 1)), (zCell, T.reference.spatialPatch zCell)) (L / 64) := by
    rw [← heq, ContinuousLinearEquiv.apply_symm_apply]
    exact hq
  refine ⟨hq'.1, ?_⟩
  have hh := hq'.2
  change ((adaptedCoordinates T.data.adapted p.1).2,
    parameter p.2, T.reference.spatialPatch (parameter p.2)) ∈
      closedBall ((0 : Euclidean (n - 1)), (zCell, T.reference.spatialPatch zCell)) (L / 64) at hh
  change ((adaptedCoordinates T.data.adapted p.1).2, parameter p.2) ∈
    closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64)
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hh ⊢
  exact ⟨hh.1, hh.2.1⟩

/-- Restrict only the physical time in an existing retained cell. ALL its
zero-position carrier centers remain, so the same finite cell cover remains
valid before selecting incidence masks. The original scalar radius `L` and
carrier radius `Rc` are independent. Actual inverse identities and the retained
forward C¹ bound give the original `L/16` label range; inverse continuity is
not an assumption.

The coordinate-range premise is produced by
`densityCoordinates_mem_original_cylinder`. Membership in `c.D` is the original
carrier/full-flow compatibility conclusion in `ChartCenters.CarrierData`,
transferred by `RetainedLeading.chartOfRetainedCarrierData`. No smaller carrier
output cylinder is asserted here. Consumers: the ODE-label part of the retained
weighted comparison (`bg-Psi`, `bg-normalized`, `bg-full-complex-amplitude`). -/
theorem exists_original_label_region {N : ℕ}
    (zCell : Euclidean 3) {L Rc B τ Mc : ℝ}
    (hL : 0 < L) (hRc : 0 < Rc) (hτ : 0 < τ) (hMc : 0 < Mc)
    (hτRc : τ ≤ Rc / 16)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc) K)
    {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E)
    (hlabel : ∀ p ∈ E,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64)) :
    ∃ E' : Set (Euclidean n × CarrierParameter), IsOpen E' ∧ E' ⊆ E ∧
      (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ E' ↔ ((0 : Euclidean n), z) ∈ E) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω K ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F),
        MapsTo (densityCoordinates T) E c.D →
        cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
          1 c.forward ≤ Mc →
        MapsTo (densityCoordinates T) E' c.D ∧
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) E' K ∧
        ContDiffOn ℝ ∞ (densityFootpoint T c.inverse) E' ∧
        MapsTo (densityFootpoint T c.inverse) E'
          (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
  let e := L / (64 * Mc)
  have he : 0 < e := div_pos hL (by positivity)
  let E' := E ∩ (fun p ↦ (densityCoordinates T p).1) ⁻¹' Ioo (-e) e
  have htime : Continuous (fun p ↦ (densityCoordinates T p).1) := (densityCoordinates T).continuous.fst
  refine ⟨E', hE.inter (isOpen_Ioo.preimage htime), inter_subset_left, ?_, ?_⟩
  · intro z
    constructor
    · exact fun h ↦ h.1
    · intro hz
      refine ⟨hz, ?_⟩
      change (adaptedCoordinates T.data.adapted (0 : Euclidean n)).1 ∈ Ioo (-e) e
      simpa only [map_zero, Prod.fst_zero, mem_Ioo, neg_lt_zero] using And.intro he he
  · intro F row col c hdomain hforward
    have hsub : E' ⊆ E := inter_subset_left
    refine ⟨hdomain.mono_left hsub, ?_,
      c.inverse_smooth.comp (densityCoordinates T).contDiff.contDiffOn (hdomain.mono_left hsub), ?_⟩
    · intro p hp
      have hbig := c.subset_big (hdomain hp.1)
      have hcoords : densityCoordinates T p ∈
          closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc := by
        rw [← closedBall_prod_same]
        refine ⟨?_, ball_subset_closedBall ((ball_subset_ball (by linarith : Rc / 4 ≤ Rc)) hbig.2)⟩
        rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
        constructor <;> linarith [hbig.1.1, hbig.1.2]
      have hm := hbuffer hcoords
      change (coordinates (adaptedCoordinates T.data.adapted)).symm
        (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ K at hm
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm
    · intro p hp
      have hdist := ContinuumAdjoint.Canonical.RetainedLeading.inverseFootpoint_dist_le_of_forward_cNorm
        zCell hRc hτ c.forward c.inverse c.D c.inverse_range c.initial c.forward_inverse
        c.forward_buffer_smooth hforward (hdomain hp.1)
      have ht : |(densityCoordinates T p).1| < e := abs_lt.mpr hp.2
      have hstep : Mc * |(densityCoordinates T p).1| < L / 64 := by
        have hm := mul_lt_mul_of_pos_left ht hMc
        have heq : Mc * e = L / 64 := by
          dsimp [e]
          field_simp
        rwa [heq] at hm
      have htri := dist_triangle (densityFootpoint T c.inverse p)
        (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), zCell)
      have hl := mem_closedBall.mp (hlabel p hp.1)
      change dist (c.inverse (densityCoordinates T p)) ((0 : Euclidean (n - 1)), zCell) < L / 16
      change dist (c.inverse (densityCoordinates T p)) ((0 : Euclidean (n - 1)), zCell) ≤
        dist (c.inverse (densityCoordinates T p)) (densityCoordinates T p).2 +
          dist (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), zCell) at htri
      linarith

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
