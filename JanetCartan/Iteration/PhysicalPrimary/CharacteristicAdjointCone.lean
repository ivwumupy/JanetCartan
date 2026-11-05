module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedKernels

/-!
# The original full elapsed window stays in the same phase target

The native root/flow momentum estimate is valid on the original chart target.
The retained cone and physical box place every required normalized elapsed point
there, throughout `0 ≤ t ≤ src`, without shortening the operator's original
`0 ≤ t ≤ 3*src/4` interval or changing its frequency mask.
Consumer: `CharacteristicAdjointMomentum` and the actual inactive adjoint gap
in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped Topology
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open HamiltonPhase RegularSector.Characteristic ConicPhase EvolutionIntegral UniformEvolution
open FourierIntegral SourceExpansion SymbolBudgets
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The original geometric data supply the normalized target membership used
by the same native flow, even on the full `src` radial-comparison window.
No analytic momentum or kernel estimate is assumed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem full_elapsedPoint_mem_retained_phase_target
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (C : OpenPartialHomeomorph TC TC)
    {ε src targetRadius aperture : ℝ} (hε : 0 < ε) (hsrc : src ≤ ε)
    (hεtarget : 4*ε ≤ targetRadius)
    (hbuffer : closedBall (z.1,z) targetRadius ⊆ C.target)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) src) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε/2))
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1/2)) :
    (x 0,(x 0-t,(spatialPart x,spatialPart ξ))) ∈ domain ℓ C.target := by
  have htime : dist (x 0-t) z.1 ≤ 4*ε := by
    calc
      _ ≤ dist (x 0-t) (x 0)+dist (x 0) z.1 := dist_triangle _ _ _
      _ = |t|+dist (x 0) z.1 := by
        rw [Real.dist_eq]
        congr 1
        ring_nf
        exact abs_neg t
      _ ≤ 4*ε := by
        rw [abs_of_nonneg ht.1]
        have hx' : dist (x 0) z.1 < ε/2 := hx.1
        linarith only [ht.2,hsrc,hx',hε]
  refine ⟨hξ.1.1.1,?_⟩
  apply hbuffer
  apply closedBall_subset_closedBall hεtarget
  change (x 0,(x 0-t,(spatialPart x,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ))) ∈
    closedBall (z.1,z) (4*ε)
  simp only [mem_closedBall,Prod.dist_eq,max_le_iff]
  exact ⟨hx.1.le.trans (by linarith only [hε]),htime,
    hx.2.le.trans (by linarith only [hε]),
    hξ.1.1.2.le.trans (by linarith only [hε])⟩

end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
