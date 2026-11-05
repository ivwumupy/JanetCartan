module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SeparatedBudgets.PrimitiveRetarded
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Kernels

/-!
# Retaining the primitive elapsed graph regularizations

The primitive retarded construction normally consumes its graph regularizations
internally. Here they are retained for the selected-chart application of
`completeResidual_operators_of_graph_regularizations`. Cutoff preservation
identifies both literal kernels with the same `complexPhysicalCutoff` sequence.
The inputs are spatial phase geometry and amplitude budgets, not strong limits.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullLowBounds WholeImageGeometry
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open LowBounds FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- Construct the actual forward graph regularizations and literal adjoints
with uniform low bounds and both strong limits. The fixed physical cutoff is
common to all amplitudes, so it can also be used by the four PDO terms of
`completeResidual_operators_of_graph_regularizations` (`energy-complete-residual`).
The primitive inputs are supplied on the retained chart, before replacing the
conic phase with its supported smooth extension. -/
theorem exists_primitive_elapsed_graph_regularizations
    (R ℓ Bmix Δ : ℝ)
    (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a, ∀ (Btime Bphase : ℝ)
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J U : Set (TwoTimePoint d)} (_hJ : IsCompact J) (_hU : IsOpen U) (_hJU : J ⊆ U)
    (χout χsource β : E → ℂ)
    (_ho : ContDiff ℝ ∞ χout) (_hs : ContDiff ℝ ∞ χsource) (_hβ : ContDiff ℝ ∞ β)
    (_hocs : HasCompactSupport χout)
    (_hβzero : (0 : E) ∉ tsupport β)
    (_hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (_hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t)
    (_hβbound : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1)) (jointMultiplier β))
    (_hmap : ∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J),
    ∃ C > 0,
      ∀ (Xouter : Set E) (Douter : Set (Euclidean d)) (X Dnormal : Set E),
        IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
        IsOpen X → IsOpen Dnormal → Convex ℝ X →
        closure X ⊆ Xouter → closure Dnormal ⊆ spatialPart ⁻¹' Douter →
        tsupport χout ⊆ X → tsupport β ⊆ Dnormal → (∀ x ∈ X, ‖x‖ ≤ R) →
        (∀ ξ ∈ Dnormal, ε < ‖ξ‖) →
      ∀ K : Set (Point (d + 1)), IsCompact K →
        phaseTimeConstant K (wholeImagePhaseReserve (d + 1)) Δ ≤ Btime →
        (∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) a b,
          phasePairInclusion p ∈ K) →
        (∀ r ∈ Icc 0 Δ, MapsTo (elapsedPoint r) K J) →
      ∀ Ψ : TwoTimePhase d,
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
      ∀ (o : ℕ) (M : ℝ) (b : TwoTimeAmplitude d q),
        ContDiff ℝ ∞ (jointAmplitude b) →
        BoundedTwoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b →
        twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b ≤ M →
      ∃ Treg : ℕ → ℝ → H →L[ℂ] H,
        (∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ C * M) ∧
        (∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C * M) ∧
        (∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
          Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
            (frequencyCutFullAmplitude (complexPhysicalCutoff j)
              (elapsedAmplitude b χout χsource β r)) u) ∧
        (∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
          (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
            (reverseGraphOperator (elapsedPhase Ψ r)
              (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
                (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose))
              (fun x ↦ (u.val x).ofLp) y)) ∧
        (∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
          (𝓝 (elapsedGraph Ψ b χout χsource β r u))) ∧
        (∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
          (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u))) := by
  classical
  obtain ⟨a, ha, b, hab, hf⟩ := exists_elapsedGraphFamily_of_primitive_phase_separated_budgets
    (q := q) R ℓ Bmix Δ hℓ hRcell hε
  refine ⟨a, ha, b, hab, ?_⟩
  intro Btime Bphase z δ J U hJ hU hJU χout χsource β ho hs hβ hocs
    hβzero hYbox hcover hβbound hmap
  obtain ⟨Cg, hCg, hf⟩ := hf Btime Bphase
  obtain ⟨Ca, hCa, hbudget⟩ := exists_elapsed_fullLowReserve_constant
    (q := q) z δ hJ hU hJU χout χsource β ho hs hβ isClosed_univ
    (fun p hp ↦ hcover p ⟨hp.1, hp.2.1⟩) hβbound Δ hmap
  refine ⟨Cg * Ca, mul_pos hCg (lt_of_lt_of_le zero_lt_one hCa), ?_⟩
  intro Xouter Douter X Dnormal hXouter hDouter hcXouter hcDouter hX hDn hcX
    hXX hDD hXsub hFsub hR hcollar K hK htime hchart hmapK Ψ hΨ hnear hhom hmix
    hnormalized hphase o M b hb hbfinite hbM
  obtain ⟨χ, hχ, hχcs, _hχzero, hχeq, hf⟩ := hf
    (tsupport χout) (tsupport χsource) (tsupport β) hocs hYbox (isClosed_tsupport _) hβzero
  have hf := hf Xouter Douter X Dnormal hXouter hDouter hcXouter hcDouter
    hX hDn hcX hXX hDD hXsub hFsub hR hcollar K J U hK hJ hU hJU htime hchart
    hmapK Ψ hΨ hnear hhom hmix hnormalized hphase
  have hl (r : ℝ) (hr : r ∈ Icc 0 Δ) := hf r hr
    (elapsedAmplitude b χout χsource β r)
    (elapsedAmplitude_forwardAdmissible b χout χsource β hb ho hs hβ r) (Ca * M)
    (hbudget o M b hb (fun _ _ _ _ h ↦ (h (mem_univ _)).elim) hbfinite hbM r hr)
  choose T ht hta htr hreal hrealAdj hlim hlimAdj htest hdist hdistAdj using hl
  let Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q :=
    fun j r ↦ if hr : r ∈ Icc 0 Δ then T r hr j else 0
  have hcut (r : ℝ) (j : ℕ) := hχeq (elapsedAmplitude b χout χsource β r)
    (fun x y ξ hξ ↦ elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ
      (Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport hξ)))) j
  have hcutAdj (r : ℝ) (j : ℕ) :
      frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
          (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose) =
        frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
          (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose) := by
    rw [← frequencyCutFullAmplitude_conjTranspose, ← frequencyCutFullAmplitude_conjTranspose,
      hcut r j]
  refine ⟨Treg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simpa only [elapsedGraph, mul_assoc] using ht r hr
  · intro j r hr
    simpa only [Treg, dite_eq_left hr, mul_assoc] using htr r hr j
  · intro j r hr u
    simpa only [Treg, dite_eq_left hr, hcut r j] using hreal r hr j u
  · intro j r hr u
    simpa only [Treg, dite_eq_left hr, hcutAdj r j] using hrealAdj r hr j u
  · intro r hr u
    simpa only [Treg, dite_eq_left hr, elapsedGraph] using hlim r hr u
  · intro r hr u
    simpa only [Treg, dite_eq_left hr, elapsedGraph] using hlimAdj r hr u

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
