module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.DirectOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothReal
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.SectorEquations

/-!
# The physical source and the analytic residual on the same finite family

Separate the actual source from the three analytic residual terms after the
physical `S+cSc` pairing. The complete real error subtracts the identity once,
after pairing. The protected measured constructor uses the final theorem to
give its smooth real equation the form `P S = A + R`.

Sources: `sector-theorem-identity`, `prop:complete-residual`, and
`energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.EvolutionIntegral FourierIntegral LowBounds Realization
open FiniteMasks.ActualFamily
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp RF 2 (volume : Measure E)

/-- The full actual physical source, with the original source mask and the
same final radial threshold, compressed from its plus pair
(`sector-theorem-identity`). -/
def selectedFiniteRealSource (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    RH →L[ℝ] RH :=
  realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
    (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L)))

/-- The real physical pair of all three analytic residual terms. Its gain
does not include the angular identity defect (`energy-complete-residual`). -/
def selectedFiniteRealResidual (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) : RH →L[ℝ] RH :=
  realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
    selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁))

/-- Complete real error with one identity subtraction after physical
pairing (`prop:complete-residual`). -/
def selectedFiniteRealCompleteError (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) : RH →L[ℝ] RH :=
  (selectedFiniteRealSource f L output ho hob - 1) +
    selectedFiniteRealResidual f L Q B W₁ output ho hob retardedPW₁

/-- The same real right side is exactly the full physical source plus the
analytic residual, without dropping or duplicating an identity term
(`sector-theorem-identity`, `energy-complete-residual`). -/
theorem selectedFiniteRealSource_add_residual
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) :
    selectedFiniteRealSource f L output ho hob +
      selectedFiniteRealResidual f L Q B W₁ output ho hob retardedPW₁ =
    realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
      1 + selectedFiniteCompleteError f L Q B W₁ output ho hob retardedPW₁)) := by
  rw [← selectedFiniteCompleteError_identity f L Q B W₁ output ho hob retardedPW₁,
    physicalPairedSectorSum_add]
  ext1 u
  simp [selectedFiniteRealSource, selectedFiniteRealResidual, realCompression]

/-- The final real complete error has exactly one identity subtraction;
the source discrepancy remains separate from the gain-one residual
(`prop:complete-residual`). -/
theorem selectedFiniteRealCompleteError_identity
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) :
    1 + selectedFiniteRealCompleteError f L Q B W₁ output ho hob retardedPW₁ =
    realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
      1 + selectedFiniteCompleteError f L Q B W₁ output ho hob retardedPW₁)) := by
  rw [← selectedFiniteRealSource_add_residual f L Q B W₁ output ho hob retardedPW₁]
  unfold selectedFiniteRealCompleteError
  abel

/-- Subtracting the SAME smooth analytic residual from the already constructed
smooth right side realizes the actual physical source. The protected measured
constructor supplies both representatives, so no new source or solver is chosen
(`sector-theorem-identity`). -/
theorem selectedFiniteRealSource_smooth_realization
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H)
    (S J : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → RF))
    (hS : ∀ u, ContDiff ℝ ∞ (S u) ∧ S u =ᵐ[volume]
      selectedFiniteRealResidual f L Q B W₁ output ho hob retardedPW₁ (realSectorTestToLp u))
    (hJ : ∀ u, ContDiff ℝ ∞ (J u) ∧ J u =ᵐ[volume]
      realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
        1 + selectedFiniteCompleteError f L Q B W₁ output ho hob retardedPW₁))
          (realSectorTestToLp u)) :
    ∀ u, ContDiff ℝ ∞ ((J-S) u) ∧ (J-S) u =ᵐ[volume]
      selectedFiniteRealSource f L output ho hob (realSectorTestToLp u) := by
  intro u
  refine ⟨(hJ u).1.sub (hS u).1, ?_⟩
  have hj := (hJ u).2
  rw [← selectedFiniteRealSource_add_residual f L Q B W₁ output ho hob retardedPW₁] at hj
  filter_upwards [hj, (hS u).2,
    Lp.coeFn_add (selectedFiniteRealSource f L output ho hob (realSectorTestToLp u))
      (selectedFiniteRealResidual f L Q B W₁ output ho hob retardedPW₁ (realSectorTestToLp u))]
    with y hy hs ha
  change J u y - S u y = _
  change J u y = (selectedFiniteRealSource f L output ho hob (realSectorTestToLp u) +
    selectedFiniteRealResidual f L Q B W₁ output ho hob retardedPW₁ (realSectorTestToLp u)) y at hy
  rw [hy, hs, ha, Pi.add_apply, add_sub_cancel_right]

end JanetCartan.RegularSector.FiniteAssembly
