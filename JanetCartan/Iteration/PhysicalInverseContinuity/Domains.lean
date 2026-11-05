module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Carrier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SelectedVariation

/-!
# The actual selected flow and label buffers for strong adjoint comparison

Derive both original compact-input inclusion and the smaller inverse-label
inclusion directly from the selected buffer geometry, time margin, and the
same forward chart bound used by the normal construction. No inverse map,
mask, or flow is chosen anew. Consumer: finite retained strong adjoint family,
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalInverseContinuity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol

/-- Actual selected flow/parameter margins supply both chart-domain inputs of
the finite-jet original scalar theorem, for reference and current charts alike. -/
theorem retained_region_input_and_footpoint
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ R Mc : ℝ} {row col : Fin n}
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτRc : τ ≤ Rc / 16) (hR : 0 < R) (hMc : 0 < Mc)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (D : CoefficientNormCharts n)
    (hSflow : MapsTo (densityCoordinates T) D.field.region
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    (hlabels : ∀ p ∈ D.field.region, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), z₀) (R / 64))
    (htime : ∀ p ∈ D.field.region, |(densityCoordinates T p).1| < R / (64 * Mc))
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    (hforward : cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
      1 c.forward ≤ Mc) :
    MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.field.region K ∧
    MapsTo (densityFootpoint T c.inverse) D.field.region
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) := by
  have hflow : MapsTo (densityCoordinates T) D.field.region c.D :=
    hSflow.mono_right ((outputCylinder_spec hRc hτ).2.trans c.small_subset)
  constructor
  · intro p hp
    have hbig := c.subset_big (hflow hp)
    have hcoords : densityCoordinates T p ∈
        closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc := by
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
      z₀ hRc hτ c.forward c.inverse c.D c.inverse_range c.initial c.forward_inverse
      c.forward_buffer_smooth hforward (hflow hp)
    have hstep : Mc * |(densityCoordinates T p).1| < R / 64 := by
      have hh := mul_lt_mul_of_pos_left (htime p hp) hMc
      have heq : Mc * (R / (64 * Mc)) = R / 64 := by field_simp
      rwa [heq] at hh
    have htri := dist_triangle (densityFootpoint T c.inverse p)
      (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), z₀)
    have hl := mem_closedBall.mp (hlabels p hp)
    change dist (c.inverse (densityCoordinates T p)) ((0 : Euclidean (n - 1)), z₀) < R / 16
    change dist (c.inverse (densityCoordinates T p)) ((0 : Euclidean (n - 1)), z₀) ≤
      dist (c.inverse (densityCoordinates T p)) (densityCoordinates T p).2 +
      dist (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), z₀) at htri
    linarith

end JanetCartan.PhysicalInverseContinuity
