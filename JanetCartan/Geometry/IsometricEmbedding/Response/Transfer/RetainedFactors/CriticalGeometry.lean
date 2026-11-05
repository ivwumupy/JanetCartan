module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryCritical
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Locality
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Mixed

/-!
# Local critical geometry on the retained conic chart

Apply the existing stationary-system and averaged-Hessian constructions to a
fixed retained chart. Exact conic/local phase agreement transfers their
derivatives, so no independently selected primary chart is identified with it.
The source ball and initial condition are literal outputs of
`UniformAmplitudes.Construction`; the latter must also be retained by its conic
endpoint when applying this result to the final solver.

Consumer: critical points and inverse averaged Hessians in
`app:ch_response:eq:direct-envelope-profile`. Zero critical value still needs
the same root's primary eikonal equation and the retained flow on the whole
time segment. Uniform history-dependent radii and constants are not claimed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open ConicPhase DirectEvolution

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "Par" => ℝ × (E × Euclidean 3)

/-- The retained source ball supplies the time-domain inclusion required by
the existing stationary construction; both signs of elapsed time are kept
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_source_subset_twoTimeDomain
    {C : OpenPartialHomeomorph T T} {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a) :
    C.source ⊆ twoTimeDomain z a (2 * a) := by
  intro q hq
  rw [hsource, ← ball_prod_same] at hq
  refine ⟨hq.2, ?_⟩
  have ht : dist q.2.1 z.1 < a := by
    have hw := hq.2
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hw
    exact hw.1
  have ht' : dist q.1 z.1 < a := hq.1
  have hdiff : |q.1 - q.2.1| < 2 * a := by
    calc
      _ = dist q.1 q.2.1 := (Real.dist_eq _ _).symm
      _ ≤ dist q.1 z.1 + dist q.2.1 z.1 := dist_triangle_right _ _ _
      _ < 2 * a := by linarith
  exact abs_lt.mp hdiff

/-- On the original convex overlap the conic and local carrier phases have
the SAME joint germ in time, output, primary parameters, source and covector.
Thus the critical equations and Hessian transfer to the literal conic kernel
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_carrier_germ
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hphase : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C p) p)
    {z : RootState (Euclidean d)} {b : ℝ}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (φ : E → Euclidean 3 → ℝ) {q : Par} {w : CarrierVariables (d + 1)}
    (hq : elapsedChartPoint q.1 q.2.1 w.snd ∈
      localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b) ∩
        domain ℓ (localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b))) :
    (fun v : Par × CarrierVariables (d + 1) ↦
      elapsedCarrierPhase (curriedPhase ℓ C) v.1.1 φ v.1.2 v.2) =ᶠ[𝓝 (q, w)]
    (fun v ↦ elapsedCarrierPhase (chartPhase C) v.1.1 φ v.1.2 v.2) := by
  have hsub : localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b) ⊆ C.target := by
    intro p hp
    apply hbuffer
    have hp' : p ∈ ball (z.1, z) b := by
      simpa only [localPatch, mem_ofPred_eq, mem_ball, Prod.dist_eq, max_lt_iff,
        and_assoc] using hp
    exact ball_subset_closedBall hp'
  have he := phase_eventuallyEq_on_overlap ℓ hphase isOpen_ball isOpen_ball
    (convex_ball _ _) hsub hq
  have hc : ContinuousAt (fun v : Par × CarrierVariables (d + 1) ↦
      elapsedChartPoint v.1.1 v.1.2.1 v.2.snd) (q, w) := by
    have ht := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.continuousAt.comp
      (x := (q, w)) continuousAt_fst.snd.fst
    exact ht.prodMk ((ht.sub continuousAt_fst.fst).prodMk
      ((spatialPartCLM.continuous.continuousAt.comp continuousAt_fst.snd.fst).prodMk
        (spatialPartCLM.continuous.continuousAt.comp
          ((WithLp.continuous_snd 2 E E).continuousAt.comp continuousAt_snd))))
  filter_upwards [hc.tendsto.eventually he] with v hv
  simp only [elapsedCarrierPhase, carrierPhase, elapsedPhase, curriedPhase, chartPhase]
  rw [show phase ℓ C (v.1.2.1 0, (v.1.2.1 0 - v.1.1,
    (spatialPart v.1.2.1, spatialPart v.2.snd))) =
      twoTimePhase C (v.1.2.1 0, (v.1.2.1 0 - v.1.1,
        (spatialPart v.1.2.1, spatialPart v.2.snd))) from hv]

/-- The SAME retained conic chart has a smooth local critical map and a
common inverse bound for every segment-averaged Hessian on a convex ball.
The stationary map and gap are constructed by the existing compatible-geometry
lemmas. There is no critical-map, Hessian-gap or transfer-bound hypothesis.

The initial condition is the exact `hinit` output of
`UniformAmplitudes.Construction`; the primary smoothness comes from the original
primary chart. The base overlap must be checked on the chosen retained carrier.
This theorem proves local geometry only, not zero critical value or constants
uniform over histories (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_retained_conic_critical_geometry
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a b : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ w ∈ ball z a, Φ (w, 0) = w)
    (hinverse : ContDiffOn ℝ ∞ C.symm C.target)
    (hsmooth : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hphase : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C p) p)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (fun q ↦ φ q.1 q.2) Ω)
    {x : E} {c : Euclidean 3} (hxc : (x, c) ∈ Ω)
    (hbase : elapsedChartPoint 0 x (gradient (fun y ↦ φ y c) x) ∈
      localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b) ∩
        domain ℓ (localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b))) :
    ∃ κ : Par → CarrierVariables (d + 1),
    ∃ δ > (0 : ℝ), ∃ s > (0 : ℝ), ∃ M > (0 : ℝ),
      let q₀ : Par := (0, (x, c))
      let w₀ : CarrierVariables (d + 1) := WithLp.toLp 2 (x, gradient (fun y ↦ φ y c) x)
      ContDiffOn ℝ ∞ κ (ball q₀ δ) ∧ κ q₀ = w₀ ∧
      MapsTo κ (ball q₀ δ) (ball w₀ s) ∧
      (∀ q ∈ ball q₀ δ,
        gradient (elapsedCarrierPhase (curriedPhase ℓ C) q.1 φ q.2) (κ q) = 0) ∧
      ∀ q ∈ ball q₀ δ, ∀ w ∈ ball w₀ s,
        let H := averagedPhaseHessian
          (fun q : Par ↦ elapsedCarrierPhase (curriedPhase ℓ C) q.1 φ q.2) κ q w
        IsUnit H ∧ ‖Ring.inverse H‖ ≤ M := by
  let q₀ : Par := (0, (x, c))
  let w₀ : CarrierVariables (d + 1) := WithLp.toLp 2 (x, gradient (fun y ↦ φ y c) x)
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let f := fun q : Par ↦ elapsedCarrierPhase (curriedPhase ℓ C) q.1 φ q.2
  let fLocal := fun q : Par ↦ elapsedCarrierPhase (chartPhase C) q.1 φ q.2
  have hq : elapsedChartPoint 0 x (gradient (fun y ↦ φ y c) x) ∈ C.target := by
    apply hbuffer
    apply ball_subset_closedBall
    simpa only [localPatch, mem_ofPred_eq, mem_ball, Prod.dist_eq, max_lt_iff,
      and_assoc] using hbase.1
  have hg := contDiffOn_joint_primaryGradient hΩ hφ
  obtain ⟨V, B, k, hV, hv, hB, hb, hk, hk₀, hmaps, hdata⟩ :=
    exists_elapsedStationary_branch hC (retained_source_subset_twoTimeDomain hsource)
      hi hinverse hΩ hg hxc hq
  let κ : Par → CarrierVariables (d + 1) := fun q ↦ e.symm (k q)
  have hkbase : κ q₀ = w₀ := by rw [show κ q₀ = e.symm (k q₀) from rfl, hk₀]; rfl
  have he : Function.uncurry f =ᶠ[𝓝 (q₀, w₀)] Function.uncurry fLocal :=
    retained_conic_carrier_germ ℓ hphase hbuffer φ hbase
  have hfLocal : ContDiffAt ℝ ∞ (Function.uncurry fLocal) (q₀, w₀) :=
    contDiffAt_joint_elapsedCarrierPhase (hsmooth.contDiffAt (C.open_target.mem_nhds hq))
      (hφ.contDiffAt (hΩ.mem_nhds hxc)) (hφ.contDiffAt (hΩ.mem_nhds hxc))
  have hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q₀, w₀) :=
    hfLocal.congr_of_eventuallyEq he
  have he₀ : f q₀ =ᶠ[𝓝 w₀] fLocal q₀ :=
    (continuousAt_const.prodMk continuousAt_id).tendsto.eventually he
  have huLocal : IsUnit (fderiv ℝ (gradient (fLocal q₀)) w₀) :=
    isUnit_fderiv_gradient_elapsedCarrierPhase hphase hinverse hΩ hφ hg hxc hq
      (hdata q₀ hv (x, gradient (fun y ↦ φ y c) x) hb).2.2.1
  have hu : IsUnit (fderiv ℝ (gradient (f q₀)) w₀) := by
    rw [he₀.gradient.fderiv_eq]
    exact huLocal
  obtain ⟨η, hη, M, hM, hgap⟩ := exists_local_averaged_carrierHessian_gap hf hu
  have hkcont : ContinuousAt κ q₀ :=
    e.symm.continuous.continuousAt.comp (hk.contDiffAt (hV.mem_nhds hv)).continuousAt
  have hgraph : Tendsto (fun q ↦ (q, κ q)) (𝓝 q₀) (𝓝 (q₀, w₀)) := by
    simpa only [hkbase, id_eq] using (continuousAt_id.prodMk hkcont).tendsto
  have hcritical : ∀ᶠ q in 𝓝 q₀, gradient (f q) (κ q) = 0 := by
    filter_upwards [hV.mem_nhds hv, hgraph.eventually he.eventuallyEq_nhds] with q hqV heq
    have hd := hdata q hqV (k q) (hmaps hqV)
    have heslice : f q =ᶠ[𝓝 (κ q)] fLocal q :=
      (continuousAt_const.prodMk continuousAt_id).tendsto.eventually heq
    rw [heslice.gradient_eq]
    change gradient (elapsedCarrierPhase (chartPhase C) q.1 φ q.2) (κ q) = 0
    rw [gradient_elapsedCarrierPhase (φ := φ) (c := q.2.2) (x := q.2.1)
      (w := κ q) (hphase _ hd.2.1)
      (((hφ.contDiffAt (hΩ.mem_nhds hd.1)).comp (k q).1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))]
    change WithLp.toLp 2 (elapsedStationarySystem C φ (q, k q)) = 0
    rw [hd.2.2.2.mpr rfl]
    rfl
  have hkmem : ∀ᶠ q in 𝓝 q₀, κ q ∈ ball w₀ η := by
    apply hkcont.preimage_mem_nhds
    rw [hkbase]
    exact ball_mem_nhds w₀ hη
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (ball_mem_nhds q₀ hη)
      (Filter.Eventually.and (hV.mem_nhds hv) (hkmem.and hcritical)))
  refine ⟨κ, δ, hδ, η, hη, M, hM,
    e.symm.contDiff.comp_contDiffOn (hk.mono (fun q hq ↦ (hd hq).2.1)),
    hkbase, (fun q hq ↦ (hd hq).2.2.1), (fun q hq ↦ (hd hq).2.2.2), ?_⟩
  intro q hqδ w hw
  exact hgap q (hd hqδ).1 (κ q) (hd hqδ).2.2.1 w hw

end JanetCartan.ResponseTransfer.RetainedFactors
