module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.AnnularDomain
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AnnularMasks
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Buffered integration domains for the retained primary diagonal

The source domain is larger than the physical mask support. Its frequency
factor retains the entire annulus. Compactness gives a fixed metric margin
around a compact set of possible primary diagonals; the actual coefficient
comparison is supplied in `DiagonalBuffers`.

Consumer: the quantitative stationary branch and both envelope endpoints in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)
local notation "Z" => RootState (Euclidean d)

/-- The integration domain uses a larger physical source box and the full
open annular frequency buffer (`app:ch_response:eq:direct-envelope-profile`). -/
def retainedOpenIntegrationDomain (z : Z) (ε : ℝ) (O : Set E) : Set W :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹' (elapsedPhysicalBox z ε ×ˢ O)

/-- The buffered integration domain is open and convex and has compact
closure. Its closure retains both factor inclusions needed for the joint
phase jets (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedOpenIntegrationDomain_geometry (z : Z) (ε : ℝ)
    {O : Set E} (hO : IsOpen O) (hOc : Convex ℝ O) (hOK : IsCompact (closure O)) :
    IsOpen (retainedOpenIntegrationDomain z ε O) ∧
      Convex ℝ (retainedOpenIntegrationDomain z ε O) ∧
      IsCompact (closure (retainedOpenIntegrationDomain z ε O)) ∧
      ∀ w ∈ closure (retainedOpenIntegrationDomain z ε O),
        w.fst ∈ closure (elapsedPhysicalBox z ε) ∧ w.snd ∈ closure O := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let K := e ⁻¹' (closure (elapsedPhysicalBox z ε) ×ˢ closure O)
  have hX : IsCompact (closure (elapsedPhysicalBox z ε)) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      isCompact_closure_retained_physicalBox z (2 * ε)
  have hK : IsCompact K := by
    have he : K = e.symm '' (closure (elapsedPhysicalBox z ε) ×ˢ closure O) := by
      ext w
      exact ⟨fun hw ↦ ⟨e w, hw, e.symm_apply_apply w⟩,
        by rintro ⟨v, hv, rfl⟩; simpa [K] using hv⟩
    rw [he]
    exact (hX.prod hOK).image e.symm.continuous
  have hsub : closure (retainedOpenIntegrationDomain z ε O) ⊆ K :=
    closure_minimal (fun _ hw ↦ ⟨subset_closure hw.1, subset_closure hw.2⟩) hK.isClosed
  exact ⟨((isOpen_elapsedPhysicalBox z ε).prod hO).preimage e.continuous,
    ((convex_elapsedPhysicalBox z ε).prod hOc).linear_preimage e.toLinearMap,
    hK.of_isClosed_subset isClosed_closure hsub, fun _ hw ↦ hsub hw⟩

/-- A fixed fourfold metric margin around every possible primary diagonal.
Only fixed physical/frequency sets occur here; the actual primary gradients
are placed in the frequency ball by `RootDomain` in the consuming theorem
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_retained_integration_diagonal_margin (z : Z) {ε : ℝ} (hε : 0 < ε)
    {O : Set E} (hO : IsOpen O) (θ₀ : E) {s : ℝ}
    (hsO : closedBall θ₀ s ⊆ O) :
    ∃ ρ > (0 : ℝ), ∀ x ∈ closure (elapsedPhysicalBox z (ε / 2)),
      ∀ θ ∈ closedBall θ₀ s,
        closedBall (WithLp.toLp 2 (x, θ)) (4 * ρ) ⊆
          retainedOpenIntegrationDomain z ε O := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let K := e.symm '' (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ closedBall θ₀ s)
  have hK : IsCompact K :=
    ((isCompact_closure_retained_physicalBox z ε).prod (isCompact_closedBall _ _)).image
      e.symm.continuous
  have hKO : K ⊆ retainedOpenIntegrationDomain z ε O := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hv.1, hsO hv.2⟩
  obtain ⟨ρ, hρ, hthick⟩ := hK.exists_cthickening_subset_open
    (((isOpen_elapsedPhysicalBox z ε).prod hO).preimage e.continuous) hKO
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro x hx θ hθ
  rw [show 4 * (ρ / 4) = ρ by ring]
  exact (closedBall_subset_cthickening (show WithLp.toLp 2 (x, θ) ∈ K from
    ⟨(x, θ), ⟨hx, hθ⟩, rfl⟩) ρ).trans hthick

/-- The entire closed source/annular carrier lies in the open integration
domain. No radial interval is shortened
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_annular_integration_subset (z : Z) {ε : ℝ} (hε : 0 < ε)
    {F O : Set E} (hFO : F ⊆ O) :
    WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
        (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ F) ⊆
      retainedOpenIntegrationDomain z ε O :=
  fun _ hw ↦ ⟨UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hw.1, hFO hw.2⟩

/-- The closure of the larger integration domain lies in one of the exact
closed carriers consumed by `HistoryAnnularHessian`; the elapsed interval is
buffered independently of the operator's source radius
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedOpenIntegrationDomain_mem_closedCarrier (z : Z) (ε : ℝ)
    {O : Set E} (hO : IsOpen O) (hOc : Convex ℝ O) (hOK : IsCompact (closure O))
    {Par : Set (Euclidean 3)} {t : ℝ} (ht : t ∈ Icc 0 (2 * ε))
    {q : E × Euclidean 3} (hq : q ∈ closure (elapsedPhysicalBox z ε) ×ˢ Par)
    {w : W} (hw : w ∈ closure (retainedOpenIntegrationDomain z ε O)) :
    ((t, q), w) ∈ retainedClosedCarrier z (2 * ε) Par (closure O) := by
  have h := (retainedOpenIntegrationDomain_geometry z ε hO hOc hOK).2.2.2 w hw
  change (t ∈ Icc 0 (2 * ε) ∧
    q ∈ closure (elapsedPhysicalBox z ((2 * ε) / 2)) ×ˢ Par) ∧
    w.fst ∈ closure (elapsedPhysicalBox z ((2 * ε) / 2)) ∧ w.snd ∈ closure O
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ⟨⟨ht, hq⟩, h⟩

end JanetCartan.ResponseTransfer.RetainedFactors
