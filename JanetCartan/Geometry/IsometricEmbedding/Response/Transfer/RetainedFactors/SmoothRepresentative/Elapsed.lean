module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.Phase
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.NormalGeometry

/-!
# Smooth elapsed phase, annular carriers and whole-segment agreement

These are the literal `hSPhase`, `hΨcont` and `hΘ` signatures used by both
orientations of the integrated envelope assembly. The frequency carrier has
both a positive spatial lower bound and a finite full-frequency upper bound.
Agreement is on the whole physical chart, so the averaged-gradient segments
are preserved, not just the amplitude's nonzero locus.
Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase EvolutionIntegral FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- The constructed representative in the original two-time phase convention
(`app:ch_response:eq:fixed-factor-transfer`). -/
def curriedRepresentative (ℓ : Euclidean d →L[ℝ] ℝ) (δ : ℝ) (hδ : 0 < δ)
    (χ F : T → ℝ) : TwoTimePhase d :=
  fun t s y η ↦ representative ℓ δ hδ χ F (t, (s, (y, η)))

/-- Global smoothness supplies the literal fixed-elapsed-time `hSPhase` input
of both envelope orientations (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_elapsed_representative (ℓ : Euclidean d →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) {χ F : T → ℝ} {U : Set T}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hU : IsOpen U) (hs : tsupport χ ⊆ U) (hF : ContDiffOn ℝ ∞ F U) (t : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t)) :=
  (contDiff_elapsedPhase_of_joint_phase (contDiff_representative ℓ hδ hχ hc hU hs hF)).comp
    (contDiff_const.prodMk contDiff_id)

/-- The same constructed phase supplies the literal regrouped joint continuity
input `hΨcont` (`app:ch_response:eq:direct-envelope-profile`). -/
theorem continuous_regrouped_representative (ℓ : Euclidean d →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) {χ F : T → ℝ} {U : Set T}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hU : IsOpen U) (hs : tsupport χ ⊆ U) (hF : ContDiffOn ℝ ∞ F U) :
    Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      curriedRepresentative ℓ δ hδ χ F p.1.1 p.1.2 p.2.1 p.2.2) :=
  (contDiff_representative ℓ hδ hχ hc hU hs hF).continuous.comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

/-- Joint germ agreement includes elapsed time, output position and full
frequency. This is also valid at every point of a supplied output/source
segment, provided its normalized point lies in the common buffer
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsed_representative_joint_eventuallyEq
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    {t : ℝ} {x ξ : E}
    (hp : (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (hfreq : δ ≤ ‖spatialPart ξ‖) :
    (fun p : ℝ × (E × E) ↦
      elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) p.1 p.2.1 p.2.2)
      =ᶠ[𝓝 (t, (x, ξ))]
    (fun p ↦ elapsedPhase (curriedPhase ℓ C) p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun p : ℝ × (E × E) ↦
      (p.2.1 0, (p.2.1 0 - p.1, (spatialPart p.2.1, spatialPart p.2.2)))) := by
    change Continuous (fun p : ℝ × (E × E) ↦
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1,
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1 - p.1,
          (spatialPartCLM p.2.1, spatialPartCLM p.2.2))))
    fun_prop
  filter_upwards [(representative_eventuallyEq_phase ℓ C hδ he hp hfreq).comp_tendsto
    (hc.tendsto (t, (x, ξ)))] with p hp
  exact congrArg (fun a ↦ (p.2.1 0 - p.1) * p.2.2 0 + a) hp

/-- The fixed-time joint germ retains all physical and frequency derivatives
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsed_representative_eventuallyEq
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    {t : ℝ} {x ξ : E}
    (hp : (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (hfreq : δ ≤ ‖spatialPart ξ‖) :
    Function.uncurry (elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t)
      =ᶠ[𝓝 (x, ξ)] Function.uncurry (elapsedPhase (curriedPhase ℓ C) t) :=
  (elapsed_representative_joint_eventuallyEq ℓ C hδ he hp hfreq).comp_tendsto
    (continuous_const.prodMk continuous_id).continuousAt

/-- Exact restricted radial identity, including the full time-frequency
pairing (`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsed_representative_smul (ℓ : Euclidean d →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) (χ F : T → ℝ) (t : ℝ) (x θ : E)
    (hθ : δ ≤ ‖spatialPart θ‖) {lam : ℝ} (hlam : 1 ≤ lam) :
    elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t x (lam • θ) =
      lam * elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t x θ := by
  have he := representative_smul ℓ hδ χ F
    (p := (x 0, (x 0 - t, (spatialPart x, spatialPart θ)))) hθ hlam
  simp only [elapsedPhase, curriedRepresentative, SymbolBudgets.spatialPart_smul]
  change (x 0 - t) * (lam * θ 0) + _ = _
  rw [he]
  ring

/-- A closed bounded frequency carrier at scale `lam`. Its lower bound is on
SPATIAL frequency, so the smoothing transition is avoided even when the full
covector has a temporal component (`app:ch_response:eq:direct-envelope-profile`). -/
def annularFrequencyCarrier (δ R lam : ℝ) : Set E :=
  {ξ | lam * δ ≤ ‖spatialPart ξ‖ ∧ ‖ξ‖ ≤ lam * R}

/-- Closedness required by the literal envelope assembly (`app:ch_response:eq:direct-envelope-profile`). -/
theorem isClosed_annularFrequencyCarrier (δ R lam : ℝ) :
    IsClosed (annularFrequencyCarrier (d := d) δ R lam) :=
  (isClosed_le continuous_const spatialPartCLM.continuous.norm).inter
    (isClosed_le continuous_norm continuous_const)

/-- Boundedness allows the original compact normal geometry to contain this
carrier (`app:ch_response:eq:direct-envelope-profile`). -/
theorem isCompact_annularFrequencyCarrier (δ R lam : ℝ) :
    IsCompact (annularFrequencyCarrier (d := d) δ R lam) :=
  (isCompact_closedBall (0 : E) (lam * R)).of_isClosed_subset
    (isClosed_annularFrequencyCarrier δ R lam) (fun _ h ↦ by simpa using h.2)

/-- The carrier excludes zero, as required by both literal orientations
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem zero_notMem_annularFrequencyCarrier {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : 1 ≤ lam) (R : ℝ) : (0 : E) ∉ annularFrequencyCarrier δ R lam := by
  intro h
  have hpos := mul_pos (zero_lt_one.trans_le hlam) hδ
  have hz : lam * δ ≤ 0 := by
    simpa only [show spatialPart (0 : E) = 0 from map_zero spatialPartCLM, norm_zero] using h.1
  linarith

/-- Every normalized annular frequency satisfying the primitive lower and
upper bounds lands in the chosen physical carrier (`app:ch_response:eq:direct-envelope-profile`). -/
theorem smul_mem_annularFrequencyCarrier {δ R lam : ℝ} (hlam : 0 ≤ lam)
    {θ : E} (hl : δ ≤ ‖spatialPart θ‖) (hu : ‖θ‖ ≤ R) :
    lam • θ ∈ annularFrequencyCarrier δ R lam := by
  simp only [annularFrequencyCarrier, mem_ofPred_eq, SymbolBudgets.spatialPart_smul,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  exact ⟨mul_le_mul_of_nonneg_left hl hlam, mul_le_mul_of_nonneg_left hu hlam⟩

/-- The literal `hΘ` signature follows from membership in the closed carrier;
it holds uniformly for every elapsed time and physical output
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsed_representative_smul_on_carrier (ℓ : Euclidean d →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) (χ F : T → ℝ) (R : ℝ) {lam : ℝ} (hlam : 1 ≤ lam)
    (t : ℝ) (x θ : E) (hθ : lam • θ ∈ annularFrequencyCarrier δ R lam) :
    elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t x (lam • θ) =
      lam * elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t x θ := by
  apply elapsed_representative_smul ℓ hδ χ F t x θ ?_ hlam
  have hpos := zero_lt_one.trans_le hlam
  have h := hθ.1
  rw [SymbolBudgets.spatialPart_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at h
  exact (mul_le_mul_iff_right₀ hpos).mp h

/-- Whole-chart agreement preserves averaged gradients along the entire
output/source segment; no smaller amplitude support is substituted
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedGradient_elapsed_representative
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    {X D : Set E} (hX : IsOpen X) (hcX : Convex ℝ X) (t : ℝ)
    (hbuffer : ∀ x ∈ X, ∀ ξ ∈ D,
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (hfreq : ∀ ξ ∈ D, δ ≤ ‖spatialPart ξ‖)
    {x y ξ : E} (hx : x ∈ X) (hy : y ∈ X) (hξ : ξ ∈ D) :
    NormalComparison.averagedGradient
        (elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t) x y ξ =
      NormalComparison.averagedGradient (elapsedPhase (curriedPhase ℓ C) t) x y ξ := by
  apply averagedGradient_phase_congr hX hcX (fun p hp ↦
    (elapsed_representative_eventuallyEq ℓ C hδ he
      (hbuffer p.1 hp.1 p.2 hp.2) (hfreq p.2 hp.2)).eq_of_nhds) hx hy hξ

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
