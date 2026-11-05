module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.StationaryValue

/-!
# Zero critical value for the original full source

For each fixed full source parameter, restrict the already constructed jointly
smooth branch to that literal slice and apply the original Hamilton--Jacobi
argument. The branch, chart and elapsed interval stay unchanged. The chart
differential, root homogeneity and endpoint state identities are actual outputs
of the retained-evolution producer. Consumer:
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.FullSourceStationary
open ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)

/-- Zero critical value for both original full-source orientations on the
ENTIRE signed stationary interval. The same branch is restricted only for the
pointwise Hamilton--Jacobi proof; no independent covector choices are identified.
The root/chart differential premises are those produced by
`exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution`, and
the actual root equation and stationary maps are supplied by `HistoryMaps`
(`app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_uniform_stationary_value_eq_zero
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
    (φ : E → Param → ℝ) {Ω U₀ : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    (he : ∀ q ∈ Ω, rootSuspension h (q.1, gradient (fun y ↦ φ y q.2) q.1) = 0)
    (hU₀ : IsOpen U₀) (hUΩ : U₀ ⊆ Ω) {τ : ℝ} (hτ : 0 < τ)
    (κ : Bool → Par → W)
    (hκ : ∀ adj, ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀))
    (hdiag : ∀ adj q, q ∈ U₀ → κ adj (0, q) =
      WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1))
    (hstat : ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ →
      gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ (p, w)) (κ adj p) = 0)
    (hsrc : ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ → ((κ adj p).fst, p.2.2) ∈ Ω)
    (hgraph : ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ →
      fullSourceGraphPoint adj (p, κ adj p) ∈ domain ℓ C.target) :
    ∀ adj p, p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ →
      fullSourceJointPhase adj (curriedPhase ℓ C) φ (p, κ adj p) = 0 := by
  intro adj p hp
  let F : E × Euclidean 3 → E × Param := fun q ↦ (q.1, p.2.2)
  let ι : (ℝ × (E × Euclidean 3)) → Par := fun q ↦ (q.1, F q.2)
  let φ₀ : E → Euclidean 3 → ℝ := fun y _ ↦ φ y p.2.2
  let κ₀ : Bool → (ℝ × (E × Euclidean 3)) → W := fun o q ↦ κ o (ι q)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk contDiff_const
  have hι : ContDiff ℝ ∞ ι := contDiff_fst.prodMk (hF.comp contDiff_snd)
  have hιU : MapsTo ι (Ioo (-2 * τ) (2 * τ) ×ˢ (F ⁻¹' U₀))
      (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) := fun _ hq ↦ hq
  have hv := retained_uniform_stationary_value_eq_zero ℓ hhom hC hsource haL hLD hi
    hstate hCsm hphase φ₀ (hΩ.preimage hF.continuous)
    (hφ.comp hF.contDiffOn (fun _ hq ↦ hq))
    (fun q hq ↦ he (F q) hq) (hU₀.preimage hF.continuous)
    (fun _ hq ↦ hUΩ hq) hτ κ₀
    (fun o ↦ (hκ o).comp hι.contDiffOn hιU)
    (fun o q hq ↦ hdiag o (F q) hq)
    (fun o q hq ↦ hstat o (ι q) (hιU hq))
    (fun o q hq ↦ hsrc o (ι q) (hιU hq))
    (fun o q hq ↦ hgraph o (ι q) (hιU hq)) adj (p.1, (p.2.1, 0)) hp
  exact hv

end JanetCartan.FullSourceStationary
