module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.HistoryBranches
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.StationaryValue.Differential

/-!
# Zero values of the uniform retained stationary maps

The signed stationary maps of `HistoryBranches` have identically zero critical
value for both literal orientations of the SAME conic phase. Stationarity
removes the branch derivative, the retained Hamilton--Jacobi identities remove
the elapsed derivative, and the original chart's diagonal fixes the constant.
The signed interval is unchanged. Consumers: the parent's critical-map assembly
and both integrated-envelope endpoints in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.RetainedFactors
open DirectEvolution RegularSector.Characteristic ConicPhase EvolutionIntegral ArbitraryAccuracy
variable {d : ℕ}
local notation "W" => CarrierVariables (d + 1)
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "Par" => ℝ × (E × Euclidean 3)
private theorem stationary_curve_hasDerivAt_zero
    {F : ℝ × W → ℝ} {k : ℝ → W} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, k t)) (hk : DifferentiableAt ℝ k t)
    (hstat : gradient (fun w ↦ F (t, w)) (k t) = 0)
    (htime : HasDerivAt (fun s ↦ F (s, k t)) 0 t) :
    HasDerivAt (fun s ↦ F (s, k s)) 0 t := by
  let L := fderiv ℝ F (t, k t)
  have hs : fderiv ℝ (fun w ↦ F (t, w)) (k t) = 0 := by
    have hh := congrArg (InnerProductSpace.toDual ℝ W) hstat
    simpa [gradient] using hh
  have hpartial := (hF.hasFDerivAt.comp (k t) (hasFDerivAt_prodMk_right t (k t))).fderiv
  have hv : L (0, deriv k t) = 0 := by
    have hh := congrArg (fun D : W →L[ℝ] ℝ ↦ D (deriv k t)) (hpartial.symm.trans hs)
    simpa [L] using hh
  have ht : L (1, 0) = 0 := by
    exact (hF.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (k t)))).unique htime
  have hd := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hk.hasDerivAt)
  have he : ((1 : ℝ), deriv k t) = (1, (0 : W)) + (0, deriv k t) := by simp
  change HasDerivAt _ (L (1, deriv k t)) t at hd
  rwa [he, map_add, ht, hv, add_zero] at hd

/-- Zero critical value on the entire signed interval of the uniform smooth
stationary maps, for BOTH literal orientations of the SAME retained conic phase.

The branch smoothness, initial diagonal and stationary gradient are the outputs
of `exists_uniform_retained_primary_stationary_maps`. Its signed-carrier
inclusions, `retainedSignedCarrier_geometry`, and the original primary-domain
buffer supply `hgraph`, `hsrc`, and `hUΩ`. The primitive chart/root premises are
exactly those of `UniformAmplitudes.RetainedEvolution`; both conic eikonal
identities are derived from them, never assumed for another chart. The primary
eikonal equation is supplied by `HistoryBranches` on its larger parameter
buffer. No extra smallness, travel, action-equality or zero-value premise is
introduced, and `τ` is not shrunk.

This is the downstream deduction used by the parent's final critical-map
assembly and the zero-value inputs of both `IntegratedEnvelope.Assembly`
endpoints (`app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`). Actual substitution of the
original family remains the parent's construction obligation. -/
theorem retained_uniform_stationary_value_eq_zero
    (ℓ : Euclidean d →L[ℝ] ℝ) {h : Z → ℝ} {D : Set Z}
    (hhom : ∀ w ∈ D, ∀ s : ℝ, 0 < s → h (w.1, (w.2.1, s • w.2.2)) = s * h w)
    {Φ : Z × ℝ → Z} {C : OpenPartialHomeomorph TC TC} {z : Z} {a L : ℝ}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    (hsource : C.source = ball (z.1, z) a) (haL : a ≤ L)
    (hLD : closedBall z L ⊆ D)
    (hi : ∀ w ∈ ball z a, Φ (w, 0) = w)
    (hstate : ∀ b ∈ C.target, twoTimeState Φ (C.symm b) ∈ D ∧
      (twoTimeState Φ (C.symm b)).1 = b.1)
    (hCsm : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hphase : ∀ b ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C b) b)
    (φ : E → Euclidean 3 → ℝ) {Ω U₀ : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    (he : ∀ q ∈ Ω, rootSuspension h (q.1, gradient (fun y ↦ φ y q.2) q.1) = 0)
    (hU₀ : IsOpen U₀) (hUΩ : U₀ ⊆ Ω) {τ : ℝ} (hτ : 0 < τ)
    (κ : Bool → Par → W)
    (hκ : ∀ adj, ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀))
    (hdiag : ∀ adj q, q ∈ U₀ → κ adj (0, q) =
      WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1))
    (hstat : ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ →
      gradient (fun w ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ (p, w)) (κ adj p) = 0)
    (hsrc : ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ → ((κ adj p).fst, p.2.2) ∈ Ω)
    (hgraph : ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ →
      carrierGraphPoint adj (p, κ adj p) ∈ domain ℓ C.target) :
    ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ →
      jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ (p, κ adj p) = 0 := by
  intro adj p hp
  let k : ℝ → W := fun s ↦ κ adj (s, p.2)
  let F : ℝ × W → ℝ := fun v ↦
    jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((v.1, p.2), v.2)
  have ht0 : (0 : ℝ) ∈ Ioo (-2 * τ) (2 * τ) := ⟨by linarith, by linarith⟩
  have hd (s : ℝ) (hs : s ∈ Ioo (-2 * τ) (2 * τ)) :
      HasDerivAt (fun r ↦ F (r, k r)) 0 s := by
    have hsp : (s, p.2) ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ := ⟨hs, hp.2⟩
    have hsrcφ := hφ.contDiffAt (hΩ.mem_nhds (hsrc adj _ hsp))
    have houtφ := hφ.contDiffAt (hΩ.mem_nhds (hUΩ hp.2))
    have hj : ContDiffAt ℝ ∞ (jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ)
        ((s, p.2), k s) :=
      contDiffAt_jointRetainedCarrierPhase adj ℓ C hCsm φ
        (hgraph adj (s, p.2) hsp) hsrcφ houtφ
    have hpath : ContDiffAt ℝ ∞ (fun v : ℝ × W ↦ ((v.1, p.2), v.2)) (s, k s) :=
      (contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd
    have hF : DifferentiableAt ℝ F (s, k s) := by
      change DifferentiableAt ℝ
        (jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ∘
          fun v : ℝ × W ↦ ((v.1, p.2), v.2)) (s, k s)
      exact (hj.differentiableAt (by simp)).comp (s, k s)
        (hpath.differentiableAt (by simp))
    have hkfull : DifferentiableAt ℝ (κ adj) (s, p.2) :=
      ((hκ adj).contDiffAt ((isOpen_Ioo.prod hU₀).mem_nhds hsp)).differentiableAt (by simp)
    have hk : DifferentiableAt ℝ k s := by
      change DifferentiableAt ℝ (κ adj ∘ fun r : ℝ ↦ (r, p.2)) s
      exact hkfull.comp s (differentiableAt_id.prodMk (differentiableAt_const p.2))
    have hφslice : DifferentiableAt ℝ (fun y ↦ φ y p.2.2) (k s).fst := by
      change DifferentiableAt ℝ (Function.uncurry φ ∘ fun y : E ↦ (y, p.2.2)) (k s).fst
      exact (hsrcφ.differentiableAt (by simp)).comp (k s).fst
        (differentiableAt_id.prodMk (differentiableAt_const p.2.2))
    apply stationary_curve_hasDerivAt_zero (F := F) (k := k) hF hk (hstat adj (s, p.2) hsp)
    exact retained_conic_stationary_hasDerivAt_zero adj ℓ hhom hC hsource haL hLD hstate
      hCsm hphase φ (hgraph adj _ hsp)
      hφslice (he _ (hsrc adj _ hsp)) (hstat adj _ hsp)
  have hconst : F (p.1, k p.1) = F (0, k 0) :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-2 * τ) (2 * τ)).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd s hs).deriv) hp.1 ht0
  change F (p.1, k p.1) = 0
  rw [hconst]
  have hg0 := hgraph adj (0, p.2) ⟨ht0, hp.2⟩
  rw [hdiag adj p.2 hp.2] at hg0
  have hg : elapsedChartPoint 0 p.2.1 (gradient (fun y ↦ φ y p.2.2) p.2.1) ∈
      domain ℓ C.target := by
    cases adj <;> simpa only [carrierGraphPoint, Bool.false_eq_true, ↓reduceIte,
      WithLp.toLp_fst, WithLp.toLp_snd, elapsedChartPoint] using hg0
  have hv := retained_conic_elapsedPhase_zero ℓ hC hsource hi hg
  dsimp only [F, k]
  rw [hdiag adj p.2 hp.2]
  cases adj <;> simp only [jointRetainedCarrierPhase, Bool.false_eq_true, ↓reduceIte,
    elapsedCarrierPhase, carrierPhase, CompactTransfer.adjointCarrierPhase,
    WithLp.toLp_fst, WithLp.toLp_snd, hv, sub_self, zero_add]

end JanetCartan.ResponseTransfer.RetainedFactors
