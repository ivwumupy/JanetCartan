module

public import JanetCartan.Iteration.PhysicalSamplingShells.Row

/-!
# The unchanged realification of the same sampled complex row

The scalar precursor is complex-linear. The physical canonical row still uses
`2 Re`, both original complex input quadratures, and factor four in its normal.
The shell realization does not modify any of these conventions.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalSamplingShells
open Sampling SamplingKernelBounds SeparatedSampling CanonicalRowComparison

variable {A : Type*} [Fintype A] {n J p : ℕ}
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- The original real sampled row is exactly `2 Re` of the original complex
row, on the unchanged input retaining both quadratures
(`app:ch_osc:eq:osc-factor-four`). -/
theorem sampledRefinedRow_realQuadrature_eq
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ) :
    realQuadratureChannel (sampledRefinedRow B ψ w h U D L) =
      CanonicalRow.weightedRow (sampleWeight B ψ w h U)
        (sampledComponent B ψ w h U (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [realQuadratureChannel_apply, sampledRefinedRow_apply, CanonicalRow.weightedRow_apply]
  simp only [map_sum, Finset.smul_sum, sampledComponent, realQuadratureChannel_apply]
  apply Finset.sum_congr rfl
  intro i _
  let v := refinedKernelPrefix (D i.1) L (color p i.2.val.1, node h (U i.1) i.2) (f i)
  have hs : (Real.sqrt (sampleWeight B ψ w h U i) : ℂ) • v =
      Real.sqrt (sampleWeight B ψ w h U i) • v :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  calc
    _ = (2 : ℝ) • l2RealPart volume (Real.sqrt (sampleWeight B ψ w h U i) • v) :=
      congrArg (fun z : Output n ↦ (2 : ℝ) • l2RealPart volume z) hs
    _ = _ := by
      rw [map_smul]
      exact smul_comm _ _ _

/-- The SAME complex sampled normal gives the original physical real normal,
with the required factor four unchanged. This is separate from the scalar
amplitude-test bound, which has no realification factor. -/
theorem sampledRefinedRow_real_normal
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (hμ : ∀ i : SampleIndex p B ψ w h U, 0 ≤ sampleWeight B ψ w h U i) :
    let Arow := CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (sampledComponent B ψ w h U (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)))
    Arow.comp Arow.adjoint = (4 : ℝ) • realOutputCompression
      (NormalPerturbation.normal (sampledRefinedRow B ψ w h U D L)) := by
  dsimp only
  rw [sampledRefinedRow_normal B ψ w h U D L hμ]
  exact sampled_weightedRow_normal B ψ w h U
    (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) hμ

end JanetCartan.PhysicalSamplingShells
