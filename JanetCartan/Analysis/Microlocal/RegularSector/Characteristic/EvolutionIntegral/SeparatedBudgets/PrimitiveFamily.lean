module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveMixed
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SeparatedBudgets.WholeImageFamily

/-!
# Elapsed graph families with separated budgets

The source annulus is chosen from the mixed derivative budget before the
annular phase-jet budget. This companion leaves the original constructor unchanged.
The consumer is the signed retarded constructor in `EvolutionIntegral.SeparatedBudgets`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 6400000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral SymbolBudgets FullLowBounds WholeImageGeometry NormalComparison
open FullAmplitudePrimitiveBudget FirstOutputJets
open LowBounds FrequencyCutoff SourceExpansion AmplitudeBound
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- The degree-zero mixed bound fixes the source annulus before the time and
normalized phase-jet budgets, and hence before the compact carrying those jets.
Consumer: the separated retarded low construction.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_elapsedGraphFamily_of_primitive_phase_separated_budgets
    (R ℓ Bmix Δ : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a, ∀ Btime Bphase : ℝ, ∃ C > 0,
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
        (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∃ χ : ℕ → E → ℂ,
        (∀ j, ContDiff ℝ ∞ (χ j)) ∧ (∀ j, HasCompactSupport (χ j)) ∧
        (∀ j, (0 : E) ∉ tsupport (χ j)) ∧
        (∀ (A : FullAmplitude (d + 1) q), (∀ x y η, η ∉ F₀ → A x y η = 0) →
          ∀ j, frequencyCutFullAmplitude (χ j) A =
            frequencyCutFullAmplitude (complexPhysicalCutoff j) A) ∧
      ∀ (Xouter : Set E) (Douter : Set (Euclidean d)) (X Dnormal : Set E),
        IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
        IsOpen X → IsOpen Dnormal → Convex ℝ X →
        closure X ⊆ Xouter → closure Dnormal ⊆ spatialPart ⁻¹' Douter →
        X₀ ⊆ X → F₀ ⊆ Dnormal → (∀ x ∈ X, ‖x‖ ≤ R) →
        (∀ ξ ∈ Dnormal, ε < ‖ξ‖) →
      ∀ (K : Set (FullAmplitudePrimitiveBudget.Local.Point (d + 1)))
        (J U : Set (TwoTimePoint d)), IsCompact K → IsCompact J → IsOpen U → J ⊆ U →
        phaseTimeConstant K (wholeImagePhaseReserve (d + 1)) Δ ≤ Btime →
        (∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) a b,
          phasePairInclusion p ∈ K) →
        (∀ r ∈ Icc 0 Δ, MapsTo (elapsedPoint r) K J) →
      ∀ (Ψ : TwoTimePhase d),
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
          ContDiffAt ℝ ∞ (jointPhase Ψ) ((x 0, x 0-r, spatialPart x), η)) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
          ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Douter, ∀ t : ℝ, 0 < t →
          Ψ (x 0) (x 0-r) (spatialPart x) (t • η) =
            t * Ψ (x 0) (x 0-r) (spatialPart x) η) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Douter,
          ‖fderiv ℝ (fun η ↦ fderiv ℝ
            (fun p : ℝ × ℝ × Euclidean d ↦ Ψ p.1 p.2.1 p.2.2 η)
            (x 0, x 0-r, spatialPart x)) η‖ ≤ Bmix) →
        (∀ j : ℕ, ContDiffOn ℝ ∞
          (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) U) →
        (∀ j : ℕ, cNorm J (wholeImagePhaseReserve (d + 1))
          (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) ≤ Bphase) →
      ∀ r ∈ Icc 0 Δ,
      (∀ (A : FullAmplitude (d + 1) q), ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
        ∀ B : ℝ, HasFullSourceSymbolBound A (fullLowReserve (d + 1)) B →
        ∃ Treg : ℕ → H →L[ℂ] H,
          ‖fullGraphOperator (elapsedPhase Ψ r) A‖ ≤ C * B ∧ ‖(fullGraphOperator (elapsedPhase Ψ r) A).adjoint‖ ≤ C * B ∧
          (∀ j, ‖Treg j‖ ≤ C * B) ∧
          (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
            graphTestOutput (elapsedPhase Ψ r) (frequencyCutFullAmplitude (χ j) A) u) ∧
          (∀ j (u : graphTestSpace (d + 1) q), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
            fun y ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ r)
              (frequencyCutFullAmplitude (fun η ↦ star (χ j η))
                (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (u.val x).ofLp) y)) ∧
          (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (fullGraphOperator (elapsedPhase Ψ r) A u))) ∧
          (∀ u, Tendsto (fun j ↦ (Treg j).adjoint u) atTop
            (𝓝 ((fullGraphOperator (elapsedPhase Ψ r) A).adjoint u))) ∧
          (∀ u, fullGraphOperator (elapsedPhase Ψ r) A (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r) A u) ∧
          GraphDistributionalRealization (graphOperator (elapsedPhase Ψ r)) χ A (fullGraphOperator (elapsedPhase Ψ r) A) ∧
          GraphDistributionalRealization (reverseGraphOperator (elapsedPhase Ψ r)) (fun j η ↦ star (χ j η))
            (fun x y η ↦ (A x y η).conjTranspose) (fullGraphOperator (elapsedPhase Ψ r) A).adjoint) := by
  obtain ⟨gap, hgap, hgeometry⟩ := exists_elapsedPhase_buffered_geometry d
  obtain ⟨a, ha, b, hab, hfamily⟩ :=
    exists_fullGraphFamily_of_wholeImage_phase_separated_budgets (r := q) (Nat.succ_pos d)
      R ℓ (1 + Bmix) hℓ hRcell hgap hε
  refine ⟨a, ha, b, hab, ?_⟩
  intro Btime Bphase
  obtain ⟨C, hC, hfamily⟩ := hfamily (Btime + Bphase)
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hX₀ hYbox hF₀ hFzero
  obtain ⟨χ, hχ, hχcs, hχzero, hχeq, hf⟩ := hfamily X₀ Y₀ F₀ hX₀ hYbox hF₀ hFzero
  refine ⟨χ, hχ, hχcs, hχzero, hχeq, ?_⟩
  intro Xouter Douter X Dnormal hXouter hDouter hcXouter hcDouter hX hDn hcX
    hXX hDD hXsub hFsub hR hcollar K J U hK hJ hU hJU htime hchart hmap
    Ψ hΨ hnear hhom hmix hnormalized hbudget r hr
  have hs : ∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0-r), (spatialPart x, η)) := by
    intro r hr x hx η hη
    exact (hΨ r hr x hx η hη).comp ((x 0, x 0-r), (spatialPart x, η))
      (f := fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ ((p.1.1, p.1.2, p.2.1), p.2.2))
      ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd.fst)).prodMk
        contDiffAt_snd.snd)
  obtain ⟨hO, hbuffer, hgeom⟩ := hgeometry Ψ Δ Xouter Douter
    hXouter hDouter hcXouter hcDouter hs hnear X Dnormal hXX hDD
  have hsp : ∀ ξ ∈ Dnormal, spatialPart ξ ∈ Douter :=
    fun ξ hξ ↦ hDD (subset_closure hξ)
  have hXX' : X ⊆ Xouter := subset_trans subset_closure hXX
  have hphase := wholeImagePhaseReserve_elapsedPhase hK hJ hU hJU Ψ hnormalized
    hbudget a b hchart hr (hmap r hr)
  exact (hf X Dnormal (Xouter ×ˢ (spatialPart ⁻¹' Douter)) (elapsedPhase Ψ r)
    hX hDn hcX hO hbuffer (hgeom r hr).1
    (fun x hx ξ hξ t ht _ ↦ elapsedPhase_smul Ψ r t x ξ (hhom r hr x hx _ (hsp ξ hξ) t ht))
    (fun x hx ξ hξ ↦ (norm_elapsedPhase_mixed_fderiv_le Ψ r x ξ hDouter (hsp ξ hξ)
      (hΨ r hr x (hXX' hx))).trans (add_le_add le_rfl (hmix r hr x hx _ (hsp ξ hξ))))
    (fun x hx y hy ↦ ((hgeom r hr).2 x hx y hy).1)
    (fun x hx y hy ξ hξ ↦ ((hgeom r hr).2 x hx y hy).2 ξ hξ)
    hcollar (fun j p hp k hk ↦ (hphase j p hp k hk).trans (add_le_add htime le_rfl))
    hR hXsub hFsub).1

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
