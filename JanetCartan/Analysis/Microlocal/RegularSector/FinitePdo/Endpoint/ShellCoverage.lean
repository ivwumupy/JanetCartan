module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Geometry

/-!
# Retaining endpoint frequency coverage from the actual finite shell producer

The retarded finite cover already covers the entire physical multiplier.
Evaluate its elapsed-image inclusion at elapsed time zero to retain the
normalized spatial covector in the SAME radial band. The representative
uses `R = 1 + ‖ζ‖`; no permutation invariance of the radial cutoff is used.
All original cover conclusions are returned alongside this extra inclusion.
Consumer: the strengthened physical retarded constructor, then `hcover` in
`EndpointPdoBounds.exists_supported_endpoint_pdo_budgets`.
Source: `app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.ResidualCoordinates FiniteMasks FiniteEvolution
open FourierIntegral FourierIntegral.PrimitiveProfiles
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "P" => (E × E) × E

/-- Strengthen the primitive finite cover without choosing a different band.
The nonempty physical carrier is supplied by the common source/output
plateaux. The last conclusion is the actual normalized frequency inclusion
for the exact physical multiplier; all earlier retarded conclusions remain
available for the SAME witnesses (`fixed-time-representation`). -/
theorem exists_physical_finite_shell_cover_with_diagonal
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε : ℝ} (hε : 0 < ε)
    {X : Set (E × E)} (hXc : IsCompact X) (hXne : X.Nonempty)
    (hX : ∀ x ∈ X, x.1 ∈ elapsedPhysicalBox z (ε / 2))
    (i : Fin (d+1)) (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : ∀ ξ ∈ tsupport (mask ∘ physicalCoordinates i) ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2)) :
    ∃ ra > (0 : ℝ), ∃ rb > ra,
    ∃ (s : Finset (normalizedMaskCarrier X (mask ∘ physicalCoordinates i)))
      (δ : normalizedMaskCarrier X (mask ∘ physicalCoordinates i) → ℝ),
      (∀ p, 0 < δ p) ∧
      (∀ p ∈ s, closedBall (p : P) (δ p) ⊆ retainedGraphDomain ℓ z ε) ∧
      (∀ r ∈ Icc 0 ε, ∀ p ∈ s,
        MapsTo (elapsedPoint r) (closedBall (p : P) (δ p))
          (bufferedJetSet ℓ z ε ra rb)) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p ∈ s, ∀ m,
        BoundedNormalizedSeminorm (closedBall (p : P) (δ p)) m
          (jointMultiplier (fun ξ ↦ (dilatedConicMask
            (mask ∘ physicalCoordinates i) L ξ : ℂ)))) ∧
      (∀ L : ℝ, 1 ≤ L →
        ∀ p ∈ X ×ˢ tsupport (fun ξ ↦ (dilatedConicMask
          (mask ∘ physicalCoordinates i) L ξ : ℂ)),
          ∃ q ∈ s, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ closedBall (q : P) (δ q),
            p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t ∧ t ≤ 1 * (1 + ‖p.2‖)) ∧
      ∀ L : ℝ, 1 ≤ L →
        ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask mask (2*L)
          (physicalCoordinates i ξ) : ℂ)),
          ∃ R : ℝ, 1 ≤ R ∧ ∃ η ∈ radialSectionBand ℓ z.2.2 ε ra rb,
            spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R := by
  obtain ⟨ra, hra, rb, hrab, s, δ, hδ, hball, hmap, hbound, hcover⟩ :=
    exists_retained_finite_shell_cover ℓ z hε hXc hX
      (mask ∘ physicalCoordinates i) (hm.comp (physicalCoordinates i).contDiff) hcarrier
  refine ⟨ra, hra, rb, hrab, s, δ, hδ, hball, hmap, hbound, hcover, ?_⟩
  intro L hL ζ hζ
  obtain ⟨v₀, hv₀⟩ := hXne
  have hcanonical := PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
    mask i (zero_lt_one.trans_le hL) hζ
  obtain ⟨q, hq, R, hR, v, hv, he, hnorm, _⟩ := hcover L hL (v₀, ζ) ⟨hv₀, hcanonical⟩
  have hJ := hmap 0 ⟨le_rfl, hε.le⟩ q hq hv
  have hband : spatialPart v.2 ∈ radialSectionBand ℓ z.2.2 ε ra rb := by
    simpa only [elapsedPoint_eq] using hJ.2
  have hζeq : ζ = R • v.2 := congrArg Prod.snd he
  refine ⟨R, hR, spatialPart v.2, hband, ?_, ?_⟩
  · rw [hζeq, spatialPart_smul]
  · exact (norm_spatialPart_le ζ).trans ((le_add_of_nonneg_left zero_le_one).trans hnorm)

end JanetCartan.RegularSector.FinitePdo
