module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.Travel
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Differential

/-!
# Both Hamilton--Jacobi identities on the retained conic domain

The inverse source ball and the original retained state identity discharge
the normalized root-domain obligations. Root homogeneity then gives both
time identities on the full conic domain, without a raw-frequency restriction.
Consumer: zero value of the uniform stationary maps, in
`app:ch_response:eq:response-exact-phase`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral

variable {d : ℕ}
local notation "E" => Euclidean d
local notation "Z" => RootState E
local notation "TC" => TwoTimePoint E

/-- The original chart source ball and retained output-state identity place
both normalized endpoint states in the SAME root domain. All premises are
literal outputs of `UniformAmplitudes.RetainedEvolution`; the initial state
does not require a separate diagonal chart selection
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_chart_root_endpoint_domains
    {Φ : Z × ℝ → Z} {C : OpenPartialHomeomorph TC TC} {z : Z} {a L : ℝ}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    (hsource : C.source = ball (z.1, z) a) (haL : a ≤ L)
    {D : Set Z} (hLD : closedBall z L ⊆ D)
    (hstate : ∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
      (twoTimeState Φ (C.symm q)).1 = q.1)
    {q : TC} (hq : q ∈ C.target) :
    (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) ∈ D ∧
      (q.2.1, ((C.symm q).2.2.1, q.2.2.2)) ∈ D := by
  have hc := twoTimeChart_inverse_coordinates hC hq
  have ho := hstate q hq
  have hi : (C.symm q).2 ∈ closedBall z L := by
    have hs := C.map_target hq
    rw [hsource, mem_ball, Prod.dist_eq, max_lt_iff] at hs
    exact closedBall_subset_closedBall haL (ball_subset_closedBall hs.2)
  constructor
  · have he : (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) =
        twoTimeState Φ (C.symm q) := by
      rw [← ho.2, ← hc.2.2.2]
    exact he ▸ ho.1
  · simpa only [← hc.2.1, ← hc.2.2.1, Prod.eta] using hLD hi

/-- Both conic Hamilton--Jacobi identities follow from the SAME original
root, flow and inverse chart. Unlike a raw-frequency overlap argument,
this applies throughout the normalized annular domain. The root homogeneity
is exactly the retained producer's scalar identity; no additional closure
of the root domain under scaling is assumed
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_conic_eikonal_identities
    (ℓ : E →L[ℝ] ℝ) {h : Z → ℝ} {D : Set Z}
    (hhom : ∀ w ∈ D, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w)
    {Φ : Z × ℝ → Z} {C : OpenPartialHomeomorph TC TC} {z : Z} {a L : ℝ}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    (hsource : C.source = ball (z.1, z) a) (haL : a ≤ L)
    (hLD : closedBall z L ⊆ D)
    (hstate : ∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
      (twoTimeState Φ (C.symm q)).1 = q.1)
    (hphase : ∀ q ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C q) q)
    {q : TC} (hq : q ∈ domain ℓ C.target) :
    deriv (fun t ↦ phase ℓ C (t, q.2)) q.1 =
      h (q.1, (q.2.2.1, gradient (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1)) ∧
    -deriv (fun s ↦ phase ℓ C (q.1, (s, q.2.2))) q.2.1 =
      h (q.2.1, (gradient (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2,
        q.2.2.2)) := by
  have hd := hphase _ hq.2
  obtain ⟨ho, hi⟩ := retained_chart_root_endpoint_domains hC hsource haL hLD hstate hq.2
  rw [gradient_phase_position ℓ hd, gradient_phase_covector ℓ hd hq.1.ne',
    (hasDerivAt_phase_outputTime ℓ hd).deriv, (hasDerivAt_phase_sourceTime ℓ hd).deriv,
    neg_neg]
  constructor
  · exact (hhom _ ho _ hq.1).symm
  · have he := hhom _ hi _ hq.1
    simpa only [ConicPhase.normalize, smul_inv_smul₀ hq.1.ne'] using he.symm

end JanetCartan.ResponseTransfer.RetainedFactors
