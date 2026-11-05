module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Elapsed
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.Selector

/-!
# The actual annular amplitude and diagonal endpoint

The carrier contains the closed support of the same normalized annular
amplitude, including both selector shoulders. The diagonal identity is
retained wherever the original physical kernel uses it.
Source: `app:ch_response:eq:fixed-factor-transfer` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase EvolutionIntegral FourierIntegral
open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.AnnularComplement
variable {d q p : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- Intersect the quantitative annular carrier with the ORIGINAL multiplier
support, retaining its angular patch and high-pass shoulder
(`app:ch_response:eq:direct-envelope-profile`). -/
def retainedFrequencyCarrier (δ R lam : ℝ) (β : E → ℂ) : Set E :=
  annularFrequencyCarrier δ R lam ∩ tsupport β

/-- The actual retained carrier is closed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem isClosed_retainedFrequencyCarrier (δ R lam : ℝ) (β : E → ℂ) :
    IsClosed (retainedFrequencyCarrier δ R lam β) :=
  (isClosed_annularFrequencyCarrier δ R lam).inter (isClosed_tsupport β)

/-- Its compactness follows from the actual annular upper bound
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem isCompact_retainedFrequencyCarrier (δ R lam : ℝ) (β : E → ℂ) :
    IsCompact (retainedFrequencyCarrier δ R lam β) :=
  (isCompact_annularFrequencyCarrier δ R lam).inter_right (isClosed_tsupport β)

/-- The retained carrier excludes zero (`app:ch_response:eq:direct-envelope-profile`). -/
theorem zero_notMem_retainedFrequencyCarrier {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : 1 ≤ lam) (R : ℝ) (β : E → ℂ) :
    (0 : E) ∉ retainedFrequencyCarrier δ R lam β :=
  fun h ↦ zero_notMem_annularFrequencyCarrier hδ hlam R h.1

/-- The literal `hΘ` signature on the carrier retaining the original
multiplier's angular patch (`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsed_representative_smul_on_retainedCarrier
    (ℓ : Euclidean d →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 < δ) (χ F : T → ℝ)
    (R : ℝ) (β : E → ℂ) {lam : ℝ} (hlam : 1 ≤ lam)
    (t : ℝ) (x θ : E) (hθ : lam • θ ∈ retainedFrequencyCarrier δ R lam β) :
    elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t x (lam • θ) =
      lam * elapsedPhase (curriedRepresentative ℓ δ hδ χ F) t x θ :=
  elapsed_representative_smul_on_carrier ℓ hδ χ F R hlam t x θ hθ.1

/-- The actual closed normalized-amplitude support lands in the compact
physical carrier. The only extra input is the primitive positive SPATIAL
frequency bound on the original multiplier/annular carrier; the upper bound
is derived from the original selector, including its shoulders
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedAnnularAmplitude_mem_frequencyCarrier
    (W : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (t : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) (order : ℤ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (δ : ℝ)
    (hfreq : ∀ θ : E, lam • θ ∈ tsupport β →
      θ ∈ tsupport (annularSelector a b ha hb) → δ ≤ ‖spatialPart θ‖)
    {v : (E × Euclidean p) × CarrierVariables (d + 1)}
    (hv : v ∈ tsupport (Function.uncurry (normalizedAnnularElapsedAmplitude
      W χout χsource β (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t lam order))) :
    lam • v.2.snd ∈ retainedFrequencyCarrier δ (2 * b) lam β := by
  have hs := tsupport_normalizedAnnularElapsedAmplitude_subset W χout χsource β
    (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t (zero_lt_one.trans_le hlam).ne' order hv
  have hπ := tsupport_comp_subset Complex.ofReal_zero (annularSelector a b ha hb) hs.2.2.2
  exact ⟨smul_mem_annularFrequencyCarrier (zero_le_one.trans hlam)
    (hfreq v.2.snd hs.2.2.1 hπ)
    (tsupport_annularSelector_subset a b ha hb hπ).2, hs.2.2.1⟩

/-- The original diagonal phase is retained on the required supported cone.
The normalized diagonal identity is the one supplied by `ConicConstruction`,
for the same inverse chart (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem representative_diagonal
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    {s : ℝ} {y η : Euclidean d}
    (hp : (s, (s, (y, η))) ∈ domain ℓ K) (hfreq : δ ≤ ‖η‖)
    (hdiag : twoTimePhase C (s, (s, (y, (ℓ η)⁻¹ • η))) = ⟪y, (ℓ η)⁻¹ • η⟫_ℝ) :
    representative ℓ δ hδ χ (twoTimePhase C) (s, (s, (y, η))) = ⟪y, η⟫_ℝ :=
  (representative_eventuallyEq_phase ℓ C hδ he hp hfreq).eq_of_nhds.trans
    (phase_diagonal ℓ C hp.1.ne' hdiag)

/-- At elapsed time zero the supported full phase is the literal spacetime
pairing, preserving the upper PDO endpoint (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsed_representative_zero
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (x ξ : E)
    (hp : (x 0, (x 0, (spatialPart x, spatialPart ξ))) ∈ domain ℓ K)
    (hfreq : δ ≤ ‖spatialPart ξ‖)
    (hdiag : twoTimePhase C
      (x 0, (x 0, (spatialPart x, (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ))) =
        ⟪spatialPart x, (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ⟫_ℝ) :
    elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) 0 x ξ = ⟪x, ξ⟫_ℝ := by
  simp only [elapsedPhase, sub_zero, curriedRepresentative,
    representative_diagonal ℓ C hδ he hp hfreq hdiag, inner_eq_time_add_spatial]

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
