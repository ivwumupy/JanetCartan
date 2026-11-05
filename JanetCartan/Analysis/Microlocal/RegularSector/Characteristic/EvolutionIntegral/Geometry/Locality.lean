module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Differential
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.Locality
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.PhaseLocality
/-!
# Supported regularity and locality for elapsed phases

The spatial phase need only be smooth where the spatial covector is nonzero.
A nonzero spacetime covector can still have zero spatial part, so the global
hypotheses of `SobolevBounds.IntegerBounds` cannot be inferred. The existing
`SupportedSobolev.IntegerBounds` instead uses the supported regularity and
homogeneity proved here, together with supported mixed invertibility.

The auxiliary globally smooth phase below is actually constructed and its
full graph is identified with the original elapsed graph. Global homogeneity
or invertibility of that extension is neither required nor asserted.
Source: `app:ch_regular_base:lem:retarded-kernel` and its fixed-time representation.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral NormalComparison
variable {d q : ℕ}

/-- Primitive regularity of the two-time phase gives the open-domain
regularity required by the whole-image graph constructor. The frequency
domain is the inverse image of the original **spatial** domain. -/
theorem elapsedPhase_contDiffOn (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d + 1))} {D : Set (Euclidean d)}
    (h : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η))) :
    ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r))
      (X ×ˢ (spatialPart ⁻¹' D)) := by
  intro p hp
  exact (contDiffAt_elapsedPhase Ψ r
    (contDiffAt_elapsedSpatialPhase Ψ r (h _ hp.1 _ hp.2))).contDiffWithinAt

/-- The precise regularity input of the supported integer Sobolev theorem
follows from the original two-time phase, without any assertion at spatial
covector zero. Source: the retarded-kernel fixed-time representation. -/
theorem elapsedPhase_supportedPhaseRegularity (Ψ : TwoTimePhase d) (r : ℝ)
    {X Y : Set (Euclidean (d + 1))} {D : Set (Euclidean d)}
    (h : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η))) :
    SupportedPhaseRegularity (elapsedPhase Ψ r) ((X ×ˢ Y) ×ˢ (spatialPart ⁻¹' D)) := by
  intro p hp _
  exact contDiffAt_elapsedPhase Ψ r
    (contDiffAt_elapsedSpatialPhase Ψ r (h _ hp.1.1 _ hp.2))

/-- Degree-one spatial homogeneity gives degree-one spacetime homogeneity
of the literal phase in the fixed-time representation. -/
theorem elapsedPhase_smul (Ψ : TwoTimePhase d) (r a : ℝ)
    (x ξ : Euclidean (d + 1))
    (h : Ψ (x 0) (x 0 - r) (spatialPart x) (a • spatialPart ξ) =
      a * Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) :
    elapsedPhase Ψ r x (a • ξ) = a * elapsedPhase Ψ r x ξ := by
  have hs : spatialPart (a • ξ) = a • spatialPart ξ :=
    spatialPartCLM.map_smul a ξ
  simp only [elapsedPhase, hs, PiLp.smul_apply, smul_eq_mul, h]
  ring

/-- The local radial germ required by the supported integer theorem follows
from primitive homogeneity on the open physical chart. No global phase
extension is used in this homogeneity assertion. -/
theorem elapsedPhase_supportedPhaseHomogeneity (Ψ : TwoTimePhase d) (r : ℝ)
    {X Y : Set (Euclidean (d + 1))} {D : Set (Euclidean d)} (hX : IsOpen X)
    (h : ∀ x ∈ X, ∀ η ∈ D, ∀ a : ℝ, 0 < a →
      Ψ (x 0) (x 0 - r) (spatialPart x) (a • η) =
        a * Ψ (x 0) (x 0 - r) (spatialPart x) η) :
    SupportedPhaseHomogeneity (elapsedPhase Ψ r) ((X ×ˢ Y) ×ˢ (spatialPart ⁻¹' D)) := by
  intro p hp _
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
  filter_upwards [hX.mem_nhds hp.1.1] with x hx
  exact elapsedPhase_smul Ψ r a x p.2 (h x hx _ hp.2 a ha)

/-- Construct a genuinely smooth auxiliary phase from the primitive
buffered spatial chart and identify its full graph with the original
elapsed graph, retaining both physical masks and the Fourier multiplier.
This is the locality route used by the supported integer Sobolev API in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_smooth_elapsedPhase_extension (Ψ : TwoTimePhase d) (r : ℝ)
    {X X₀ F₀ : Set (Euclidean (d + 1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hX₀ : IsCompact X₀) (hF₀ : IsClosed F₀)
    (hXX : X₀ ⊆ X) (hFD : ∀ ξ ∈ F₀, spatialPart ξ ∈ D)
    (h : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η))) :
    ∃ S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ (Function.uncurry S') ∧
      (∀ x ∈ X₀, ∀ ξ ∈ F₀,
        Function.uncurry S' =ᶠ[𝓝 (x, ξ)] Function.uncurry (elapsedPhase Ψ r)) ∧
      ∀ (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ),
        (∀ x, x ∉ X₀ → χout x = 0) → (∀ ξ, ξ ∉ F₀ → β ξ = 0) →
        FullLowBounds.fullGraphOperator S' (elapsedAmplitude b χout χsource β r) =
          elapsedGraph Ψ b χout χsource β r := by
  obtain ⟨S', hs, he⟩ := exists_smooth_phase_extension (elapsedPhase Ψ r)
    (hX₀.isClosed.prod hF₀) (hX.prod (hD.preimage spatialPartCLM.continuous))
    (fun p hp ↦ ⟨hXX hp.1, hFD _ hp.2⟩) (elapsedPhase_contDiffOn Ψ r h)
  refine ⟨S', hs, fun x hx ξ hξ ↦ he (x, ξ) ⟨hx, hξ⟩, ?_⟩
  intro b χout χsource β hχ hβ
  apply FullLowBounds.fullGraphOperator_phase_congr
  intro x y ξ hA
  apply (he (x, ξ) ⟨?_, ?_⟩).eq_of_nhds
  · by_contra hx
    exact hA (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ (Or.inl (hχ x hx)))
  · by_contra hξ
    exact hA (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ (Or.inr (Or.inr (hβ ξ hξ))))
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
