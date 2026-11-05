module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.SourceBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothReal

/-!
# Single smooth realizations of the actual normalized source

Apply the proved signed source estimates to obtain one complex linear map
and one real linear map, valid at every derivative order. Their pointwise
inclusion agrees on the same real tests. Sources: `sector-theorem-identity`,
`real-sector-normalization`, `resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks.ActualFamily FiniteAssembly EllipticComplement Realization
open FourierIntegral FourierIntegral.LowBounds Characteristic.EvolutionIntegral
open Pseudodifferential ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- Construct one all-order smooth realization of the actual complete
normalized source and its literal real compression. Membership follows from
the actual Fourier source and physical masks; no regularity or estimate of
the desired source operator is assumed (`sector-theorem-identity`,
`resolved-angular-tail`). -/
theorem exists_pairedSource_smooth_realizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) {L : ℝ} (hL : f.radialThreshold ≤ L) :
    ∃ A : graphTestSpace (d+1) (d+1) →ₗ[ℂ] (E → F),
    ∃ AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → RF),
      (∀ u, ContDiff ℝ ∞ (A u) ∧ A u =ᵐ[volume]
        pairedSource f hK L output ho.continuous hob (graphTestToLp u)) ∧
      (∀ u, ContDiff ℝ ∞ (AR u) ∧ AR u =ᵐ[volume]
        realSource f hK L output ho.continuous hob (realSectorTestToLp u) ∧
        (fun y ↦ euclideanComplexInclusion (AR u y)) = A (realSectorTestInclusion u)) := by
  obtain ⟨_, _, hbounds⟩ := exists_pairedSource_order_zero_constants f hK output ho hoc hob
  have hmem (u : graphTestSpace (d+1) (d+1)) (s : ℕ) :
      MemVectorFourierSobolev (s : ℝ)
        (pairedSource f hK L output ho.continuous hob (graphTestToLp u)) :=
    ((hbounds L hL s (pairedSource f hK L output ho.continuous hob) (Or.inl rfl)).1
      (graphTestToLp u) (graphTest_memVectorFourierSobolev s u)).1
  obtain ⟨A, hA⟩ := exists_smooth_linear_graph_realization
    (pairedSource f hK L output ho.continuous hob) hmem
  let T : H →L[ℂ] H := (1/2 : ℂ) • (sourceCutMultiplier output ho.continuous hob).comp
    (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L)
  obtain ⟨AR, hAR⟩ := exists_smooth_real_physical_pair T A hA
  exact ⟨A, AR, hA, hAR⟩

end JanetCartan.RegularSector.NormalizedSolver
