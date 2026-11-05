module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.IntegerBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.LocalPairing

/-!
# Signed integer estimates for the same primitive retarded operator

This theorem retains every primitive hypothesis and conclusion of the positive
constructor and adds negative integer estimates for its SAME operator and
literal adjoint. Both uncut test actions, both masks, the lower buffer and the
slab factor `Δ` remain in the statement. Constants precede the varying phase
and amplitude. The extra fiber factor is exactly `q²`; the single high phase
and amplitude sum is evaluated with the fixed reserve
`fullLowReserve (d+1)+2+o` (at most `fullLowReserve (d+1)+3`).

The attained norm is the shared Euclidean Fourier norm on vector L² classes.
In particular, `o=1, k=0` gives `H⁻¹ → L²` on L² data. No distribution
completion extension is asserted. The sector owner still supplies its actual
Hamilton phase, transport amplitudes, masks and finite sums. The algebraic PDO
terms already have negative estimates in `PdoRealization.NegativeBounds`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 6400000
open Set MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral SymbolBudgets KernelIdentification UncutTestAction
open FullLowBounds WholeImageGeometry FullAmplitudePrimitiveBudget
open FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open LowBounds.FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "P" => ℝ × ℝ × Euclidean d

/-- Primitive realization with positive AND negative integer bounds for one
retarded operator and its literal Hilbert adjoint. The negative conclusion is
proved by actual weighted Fourier duality, not assumed. Its `o=1, k=0`
instance is the residual endpoint used by the original finite inverse.
Sources: `app:ch_regular_base:eq:negative-duality`,
`app:ch_regular_base:lem:retarded-kernel`, and
`app:ch_regular_base:eq:energy-complete-residual`.
-/
theorem exists_retardedOperator_signed_integer_bounds_of_primitive_data
    (R ℓ Btime Bφ Δ : ℝ) (hΔ : 0 ≤ Δ) (hBφ : 0 ≤ Bφ)
    (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2) {ε : ℝ} (hε : 0 < ε)
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hβzero : (0 : E) ∉ tsupport β)
    (hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (hβbound : ∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j
      (jointMultiplier β))
    (c : ℝ) (hc : 1 ≤ c)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t ∧ t ≤ c * (1 + ‖p.2‖))
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J) :
    ∃ a > 0, ∃ b > a, ∃ C₀ > 0,
      ∀ (Ug : ι → Set (Point (d + 1))) (Vg : Set (Point (d + 1))),
        (∀ i, IsOpen (Ug i)) → IsOpen Vg →
        (∀ i, Metric.closedBall (z i) (δ i) ⊆ Ug i) →
        (∀ i, ∀ t : ℝ, 1 ≤ t → ∀ p ∈ Ug i, (p.1, t • p.2) ∈ Vg) →
      ∀ (Xouter X Dnormal : Set E) (Douter Dcore : Set (Euclidean d)) (Ω : Set P),
        IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
        IsOpen X → IsOpen Dnormal → Convex ℝ X → IsOpen Ω →
        IsOpen Dcore → Convex ℝ Dcore → Dcore ⊆ Douter →
        closure X ⊆ Xouter → closure Dnormal ⊆ spatialPart ⁻¹' Dcore →
        (∀ t : ℝ, 0 < t → ∀ η ∈ Douter, t • η ∈ Douter) →
        (∀ t : ℝ, 0 < t → ∀ η ∈ Dcore, t • η ∈ Dcore) →
        (∀ p ∈ Vg, p.1.1 ∈ X ∧ spatialPart p.2 ∈ Dcore) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, (x 0, x 0-r, spatialPart x) ∈ Ω) →
        (∀ x ∈ X, ‖x‖ ≤ R) → (∀ ξ ∈ Dnormal, ε < ‖ξ‖) →
        U ⊆ Ω ×ˢ Douter →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Dcore,
          ∃ t : ℝ, 0 < t ∧ ∃ ζ ∈ Douter,
            ((x 0, x 0-r, spatialPart x), ζ) ∈ J ∧ η = t • ζ) →
        tsupport χout ⊆ X → tsupport β ⊆ Dnormal →
      ∀ M : ℝ, 0 ≤ M → ∀ o : ℕ, (o = 0 ∨ o = 1) →
      ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ K : Set (Point (d + 1)), IsCompact K →
        phaseTimeConstant K (wholeImagePhaseReserve (d + 1)) Δ ≤ Btime →
        (∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) a b,
          phasePairInclusion p ∈ K) →
        (∀ r ∈ Icc 0 Δ, MapsTo (elapsedPoint r) K J) →
      ∀ Ψ : TwoTimePhase d,
        ContDiffOn ℝ ∞ (jointPhase Ψ) (Ω ×ˢ Douter) →
        (∀ t : ℝ, 0 < t → ∀ p ∈ Ω, ∀ η ∈ Douter,
          Ψ p.1 p.2.1 p.2.2 (t • η) = t * Ψ p.1 p.2.1 p.2.2 η) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
          ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2) →
        cNorm J (max (wholeImagePhaseReserve (d + 1)) (fullLowReserve (d + 1) + o + 2))
          (jointPhase Ψ) ≤ Bφ →
      ∀ b : TwoTimeAmplitude d q, ContDiff ℝ ∞ (jointAmplitude b) →
        (∀ j, BoundedTwoTimeOrderSeminorm o J j b) →
        twoTimeOrderSeminorm o J (fullLowReserve (d + 1) + o) b ≤ M →
      ∀ a₀ : ℝ, (∀ x, χout x ≠ 0 → x 0 ∈ Icc a₀ (a₀ + Δ)) →
        (∀ t s y η, s ≤ a₀ → b t s y η = 0) →
      (∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ C₀ * M) ∧
      (∀ u, AEStronglyMeasurable (fun r ↦ elapsedGraph Ψ b χout χsource β r u)
        (volume.restrict (Icc 0 Δ))) ∧
      (∀ u, AEStronglyMeasurable (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
        (volume.restrict (Icc 0 Δ))) ∧
      (∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
        elapsedGraph Ψ b χout χsource β r (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (χout x • graphOperator (Ψ (x 0) (x 0-r))
            (fun y _ η ↦ b (x 0) (x 0-r) y η)
            (fun z ↦ physicalMultiplierIntegral β
              (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
              (timeSpacePoint (x 0-r) z)) (spatialPart x))) ∧
      ∃ Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        ‖Q‖ ≤ Δ * (C₀ * M) ∧
        (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
        (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
        (∀ s : ℕ, ∀ W : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
          (W = Q ∨ W = Q.adjoint) → ∀ u : SpacetimeL2 d q,
          MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
            MemVectorFourierSobolev (s : ℝ) (W u) ∧
            vectorFourierSobolevNorm (s : ℝ) (W u) ≤ (Δ * C s) *
              (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
                (1 + twoTimeOrderSeminorm o J (s + (fullLowReserve (d + 1) + 2)) b +
                  cNorm J (s + (fullLowReserve (d + 1) + 2)) (jointPhase Ψ)) * ‖u‖)) ∧
        (∀ k : ℕ, ∀ W : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
          (W = Q ∨ W = Q.adjoint) → ∀ u : SpacetimeL2 d q,
            MemVectorFourierSobolev (-(k : ℝ)) (W u) ∧
            vectorFourierSobolevNorm (-(k : ℝ)) (W u) ≤
              ((q : ℝ) * q * (Δ * C (k+o))) *
                (2 + twoTimeOrderSeminorm o J (k+o+(fullLowReserve (d+1)+2)) b +
                  cNorm J (k+o+(fullLowReserve (d+1)+2)) (jointPhase Ψ)) *
                vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u) ∧
        ∀ u : graphTestSpace (d + 1) q,
          (Q (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (retardedPhysicalIntegral Ψ b χout χsource β hs a₀ u x)) ∧
          ∀ v : graphTestSpace (d + 1) q,
            Integrable (fun ξ ↦ inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
              (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
              (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
                (fun x ↦ (u.val x).ofLp) a₀ (a₀ + Δ) ξ))) ∧
            inner ℂ (graphTestToLp v) (Q.adjoint (graphTestToLp u)) =
              ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ∫ ξ,
                inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
                  (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
                  (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
                    (fun x ↦ (u.val x).ofLp) a₀ (a₀ + Δ) ξ)) := by
  obtain ⟨a, ha, b, hab, C₀, hC₀, h⟩ :=
    exists_retardedOperator_integer_bounds_of_primitive_data
      (q := q) R ℓ Btime Bφ Δ hΔ hBφ hℓ hRcell hε z δ hδ hJ hU hJU
      χout χsource β ho hs hβ hocs hscs hβzero hYbox hβbound c hc hcover hmap
  refine ⟨a, ha, b, hab, C₀, hC₀, ?_⟩
  intro Ug Vg hUg hVg hball hrad Xouter X Dnormal Douter Dcore Ω
    hXouter hDouter hcXouter hcDouter hX hDn hcX hΩ hDcore hcDcore hCoreSub
    hXX hDDcore hcone hcoreCone hchart hposition hR hcollar hUΩ hcoverMixed
    hXsub hFsub M hM o ho'
  obtain ⟨C, hC, h⟩ := h Ug Vg hUg hVg hball hrad Xouter X Dnormal Douter Dcore Ω
    hXouter hDouter hcXouter hcDouter hX hDn hcX hΩ hDcore hcDcore hCoreSub
    hXX hDDcore hcone hcoreCone hchart hposition hR hcollar hUΩ hcoverMixed
    hXsub hFsub M hM o ho'
  refine ⟨C, hC, ?_⟩
  intro K hK htime hshell hmapK Ψ hΨ hhom hnear hφ b hb hbfinite hbM a₀ hout hzero
  obtain ⟨hlow, hmeas, hmeasAdj, hfixed, Q, hnorm, hQ, hQadj, hpos, htest⟩ :=
    h K hK htime hshell hmapK Ψ hΨ hhom hnear hφ b hb hbfinite hbM a₀ hout hzero
  refine ⟨hlow, hmeas, hmeasAdj, hfixed, Q, hnorm, hQ, hQadj, hpos, ?_, htest⟩
  intro k W hW u
  have hnegative := retarded_negative_integer_bounds_of_positive Q o
    (fullLowReserve (d+1)+2) hΔ C
    (fun j ↦ 1 + twoTimeOrderSeminorm o J j b + cNorm J j (jointPhase Ψ))
    (fun s ↦ (hC s).le)
    (fun j ↦ add_nonneg (add_nonneg zero_le_one
      (twoTimeOrderSeminorm_nonneg o J j b)) (cNorm_nonneg J j (jointPhase Ψ))) hpos k W hW u
  simpa only [← add_assoc, one_add_one_eq_two] using hnegative

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
