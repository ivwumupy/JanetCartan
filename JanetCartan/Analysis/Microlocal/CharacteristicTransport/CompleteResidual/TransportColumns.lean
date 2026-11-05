module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.FiniteIdentity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalKernel

/-!
# Identifying the actual correction columns with the residual amplitude

The physical kernel producer gives a columnwise identity whose right side is
P applied to the very same correction column. The finite residual uses the
matrix amplitude P W₁. This file proves their equality, retaining B₀, and
connects the direct-correction/null-transport producer to the precise column
input of `firstOrderApply_cutDirectSolver`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The matrix residual P W₁ has exactly the physical correction derivatives
as its columns. Its source-time and spatial-frequency arguments are frozen,
as in the physical kernel producer and the retarded derivative
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem twoTimePhysicalApply_column
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (W : TwoTimeAmplitude d q)
    (s : ℝ) (η : Euclidean d) (x : E)
    (hW : DifferentiableAt ℝ (fun y ↦ W (y 0) s (spatialPart y) η) x) (j : Fin q) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y i ↦ W (y 0) s (spatialPart y) η i j) x =
      fun i ↦ twoTimePhysicalApply A B W (x 0) s (spatialPart x) η i j := by
  let L : Mat →L[ℝ] FV := ContinuousLinearMap.pi fun i ↦
    (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap
  have hd (a : Fin (d + 1)) :
      partialDeriv (fun y i ↦ W (y 0) s (spatialPart y) η i j) x a =
        fun i ↦ partialDeriv (fun y ↦ W (y 0) s (spatialPart y) η) x a i j := by
    change fderiv ℝ (L ∘ (fun y ↦ W (y 0) s (spatialPart y) η)) x _ = _
    rw [(L.hasFDerivAt.comp x hW.hasFDerivAt).fderiv]
    rfl
  have hx : timeSpacePoint (x 0) (spatialPart x) = x :=
    timeSpaceMeasurableEquiv.symm_apply_apply x
  ext i
  simp only [twoTimePhysicalApply, hx, physicalSymbolApply, WKB.firstOrderApply,
    Matrix.mulVecLin_apply, hd, Matrix.mulVec, dotProduct, Matrix.add_apply,
    Pi.add_apply, Finset.sum_apply, Matrix.sum_apply, Matrix.mul_apply]

/-- Null transport and the literal direct correction produce the exact
column premise used by the finite complete residual. The correction equality
is its definition W₁ = i b₋₁ P W₀, not a residual equation. The complement
and row hypotheses are the outputs of the root/minor and signed-transport
construction. This specializes the existing checked direct-correction theorem
and identifies its RHS with the actual matrix P W₁
(`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem twoTimeColumn_cancellation_of_directCorrection
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bphase : E → FV →L[ℂ] FV) (s : ℝ) (η : Euclidean d) (x : E)
    (hA : ∀ a, DifferentiableAt ℝ
      (fun y ↦ (A y a).mulVecLin.toContinuousLinearMap) x)
    (hB : DifferentiableAt ℝ (fun y ↦ (B y).mulVecLin.toContinuousLinearMap) x)
    (hb : DifferentiableAt ℝ bphase x)
    (hΨ : DifferentiableAt ℝ (fun y ↦ Ψ (y 0) s (spatialPart y) η) x)
    (hW₀ : ∀ j, ContDiffAt ℝ 2 (fun y i ↦ W₀ (y 0) s (spatialPart y) η i j) x)
    (hW₁ : DifferentiableAt ℝ (fun y ↦ W₁ (y 0) s (spatialPart y) η) x)
    (proj : FV →ₗ[ℂ] FV)
    (hnull : ∀ j, WKB.principalSymbol (fun y a ↦ (A y a).mulVecLin)
      (fun y ↦ Ψ (y 0) s (spatialPart y) η) x
      (fun i ↦ W₀ (x 0) s (spatialPart x) η i j) = 0)
    (hcomp : ∀ w, WKB.principalSymbol (fun y a ↦ (A y a).mulVecLin)
      (fun y ↦ Ψ (y 0) s (spatialPart y) η) x (bphase x w) = w - proj w)
    (hrow : ∀ j, proj (WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin)
      (fun y ↦ (B y).mulVecLin) (fun y i ↦ W₀ (y 0) s (spatialPart y) η i j) x) = 0)
    (hcorr : ∀ j, (fun y i ↦ W₁ (y 0) s (spatialPart y) η i j) =
      directCorrection (fun y a ↦ (A y a).mulVecLin.toContinuousLinearMap)
        (fun y ↦ (B y).mulVecLin.toContinuousLinearMap) bphase
        (fun y i ↦ W₀ (y 0) s (spatialPart y) η i j)) (j : Fin q) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply A B W₁ (x 0) s (spatialPart x) η i j) := by
  have hid := firstOrder_directCorrection_identity hA hB hb hΨ (hW₀ j) proj
    (hnull j) hcomp (hrow j)
  rw [← hcorr j] at hid
  have he := twoTimePhysicalApply_column A B W₁ s η x hW₁ j
  calc
    _ = Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
          (fun y i ↦ W₁ (y 0) s (spatialPart y) η i j) x := hid
    _ = _ := congrArg (Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) • ·) he

end JanetCartan.CharacteristicTransport.CompleteResidual
