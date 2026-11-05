module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.RootFlow
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase

/-!
# Both conic time identities for the common root flow

The full time segments of the actual common flow supply both root-domain
memberships. The same coefficient branch's positive homogeneity then gives
both Hamilton--Jacobi identities, for either ordering of the two times.
Consumer: the root substitution in `AmplitudeBounds`, and the characteristic
relation of `app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.UniformGeometry
open ConicPhase
variable {d : ℕ}

/-- Derive both conic eikonal identities from the common actual flow. All
state memberships come from that flow's range and source ball; the two times
may have either order. The parent instantiates `hroot` with `fieldDomain_smul`
and the same `fieldRoot`'s homogeneity, and `hΦ` with the constructed flow.
No eikonal identity is an input (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_conicPhase_eikonal
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    {D : Set (RootState (Euclidean d))} (hRD : closedBall z R ⊆ D)
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ)
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (hsource : C.source ⊆ twoTimeDomain z (R / 2) T)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ domain ℓ C.target) :
    deriv (fun t ↦ phase ℓ C (t, q.2)) q.1 =
      h (q.1, (q.2.2.1,
        gradient (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1)) ∧
    -deriv (fun s ↦ phase ℓ C (q.1, (s, q.2.2))) q.2.1 =
      h (q.2.1, (gradient (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η))))
        q.2.2.2, q.2.2.2)) := by
  let p := normalize ℓ q
  have hp : p ∈ C.target := hq.2
  have hi := hsource (C.map_target hp)
  have hc := twoTimeChart_inverse_coordinates hC hp
  have hout := hΦ.range (C.symm p).2 (ball_subset_closedBall hi.1) _
    (Ioo_subset_Icc_self hi.2)
  have hclock := rootFlow_twoTimeState_clock hΦ hT hi
  have hout' : (q.1, (q.2.2.1, (twoTimeState Φ (C.symm p)).2.2)) ∈ D := by
    have he : (q.1, (q.2.2.1, (twoTimeState Φ (C.symm p)).2.2)) =
        twoTimeState Φ (C.symm p) := by
      exact Prod.ext (hclock.trans hc.1).symm (Prod.ext hc.2.2.2.symm rfl)
    rw [he]
    exact hRD hout
  have hin : (q.2.1, ((C.symm p).2.2.1, p.2.2.2)) ∈ D := by
    have he : (q.2.1, ((C.symm p).2.2.1, p.2.2.2)) = (C.symm p).2 := by
      exact Prod.ext hc.2.1.symm (Prod.ext rfl hc.2.2.1.symm)
    rw [he]
    exact hRD (closedBall_subset_closedBall (by linarith : R / 2 ≤ R)
      (ball_subset_closedBall hi.1))
  exact phase_eikonal_identities ℓ (hdiff p hp) hroot hout' hin hq.1

end JanetCartan.RegularSector.Characteristic.UniformGeometry
