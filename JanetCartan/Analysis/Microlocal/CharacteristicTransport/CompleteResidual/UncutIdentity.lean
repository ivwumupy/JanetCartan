module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.MaskedKernels
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.StrongLimits

/-!
# Passing the assembled complete residual through strong L² limits

Source: `app:ch_regular_base:eq:energy-complete-residual`.

The inputs below are separate regularization representatives and strong limits
for the retarded solver, algebraic PDO, principal PDO, endpoint PDO, retarded
P W₁ and derivative PDO. They are not a solver equation. The retarded inputs
are the outputs of `exists_retardedOperator_of_regularizations`; `MaskedKernels`
identifies their literal kernels. The canonical graph/PDO realization supplies
the four PDO inputs with the same frequency cutoff and masks. Actual primitive
budget instantiation and compatibility with the physical PDO producer remain
construction obligations, not consequences of the following implication.

The finite equation is proved by `firstOrderApply_cutDirectSolver_on_plateau`.
The formal test action and its weak closure are proved in `StrongLimits`.
Thus neither a successful uncut equation nor pointwise differentiation of its
output is assumed. The a.e. conclusion requires the same output's actual weak
derivative, as supplied by graph/PDO H¹ regularity on smooth source data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "C2" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

private theorem representative_add {f g : C2} {u v : E → FV}
    (hf : f =ᵐ[volume] fun x ↦ WithLp.toLp 2 (u x))
    (hg : g =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x)) :
    f + g =ᵐ[volume] fun x ↦ WithLp.toLp 2 (u x + v x) := by
  filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx
  simp only [Pi.add_apply, hfx, hgx] at hx
  exact hx

private theorem representative_smul (z : ℂ) {f : C2} {u : E → FV}
    (hf : f =ᵐ[volume] fun x ↦ WithLp.toLp 2 (u x)) :
    z • f =ᵐ[volume] fun x ↦ WithLp.toLp 2 (z • u x) := by
  filter_upwards [Lp.coeFn_smul z f, hf] with x hx hfx
  simp only [Pi.smul_apply, hfx] at hx
  exact hx

/-- The complete finite-cutoff identity passes to the uncut tested equation
and, for the same output's weak derivative, to the local a.e. equation.
Each of the six limits is a separate primitive graph/PDO realization output;
all three residual terms and the principal Op(α) survive. The common v is
exactly the source-masked datum identified in `MaskedKernels`.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
This conditional implication does not instantiate the sector's primitive
realizations, coefficient-family budgets or H¹ estimates. -/
theorem completeResidual_test_and_ae_of_component_limits
    (A : E → Fin (d + 1) → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (proj : E → Euclidean d → Mat) (β χout : E → ℂ)
    (θ : ℕ → E → ℂ) (a : ℝ) (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₀ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₀ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₁ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₁ p.1.1 p.1.2 p.2.1 p.2.2))
    (hc : ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bminus σ β)))
    (hβ : ContDiff ℝ ∞ β) (ho : ContDiff ℝ ∞ χout)
    (hθ : ∀ k, ContDiff ℝ ∞ (θ k)) (hθcs : ∀ k, HasCompactSupport (θ k))
    (hvcs : HasCompactSupport (v : E → FV))
    {U : Set E} (hU : IsOpen U)
    (hσ : ∀ x ∈ U, Continuous (σ x))
    (hplateau : ∀ x ∈ U, χout =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ))
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η)
    (hlead : ∀ x ∈ U, ∀ η,
      ((A x 0).map Complex.ofReal) * W₀ (x 0) (x 0) (spatialPart x) η = σ x η • proj x η)
    (hcomp : ∀ x ∈ U, ∀ ξ, β ξ ≠ 0 →
      (∑ j, (ξ j : ℂ) • (A x j).map Complex.ofReal) * bminus x ξ =
        1 - proj x (spatialPart ξ))
    (hcancel : ∀ x ∈ U, ∀ s η j, WKB.firstOrderApply
      (fun y i ↦ ((A y i).map Complex.ofReal).mulVecLin)
      (fun y ↦ ((B y).map Complex.ofReal).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply (fun y j ↦ (A y j).map Complex.ofReal)
          (fun y ↦ (B y).map Complex.ofReal) W₁ (x 0) s (spatialPart x) η i j))
    (tReg cReg pReg eReg rReg dReg : ℕ → C2) (t c p e r b : C2)
    (htrep : ∀ k, tReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (χout x • ∫ s in a..x 0, cutFixedTimeFourier Ψ (W₀ + W₁) β (θ k) v
        (x 0) s (spatialPart x)))
    (hcrep : ∀ k, cReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (χout x • cutPhysicalPDO (θ k) (directAlgebraicSymbol bminus σ β) v x))
    (hprep : ∀ k, pReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (χout x • cutPhysicalPDO (θ k)
        (fun y ξ ↦ (σ y (spatialPart ξ) * β ξ) • (1 : Mat)) v x))
    (herep : ∀ k, eReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (χout x • cutPhysicalPDO (θ k) (fun y ξ ↦ β ξ •
        ((A y 0).map Complex.ofReal * W₁ (y 0) (y 0) (spatialPart y) (spatialPart ξ))) v x))
    (hrrep : ∀ k, rReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (χout x • ∫ s in a..x 0, cutFixedTimeFourier Ψ
        (twoTimePhysicalApply (fun y j ↦ (A y j).map Complex.ofReal)
          (fun y ↦ (B y).map Complex.ofReal) W₁) β (θ k) v (x 0) s (spatialPart x)))
    (hdrep : ∀ k, dReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (χout x • cutPhysicalPDO (θ k)
        (physicalSymbolApply (fun y j ↦ (A y j).map Complex.ofReal)
          (fun y ↦ (B y).map Complex.ofReal) (directAlgebraicSymbol bminus σ β)) v x))
    (htlim : Tendsto tReg atTop (𝓝 t)) (hclim : Tendsto cReg atTop (𝓝 c))
    (hplim : Tendsto pReg atTop (𝓝 p)) (helim : Tendsto eReg atTop (𝓝 e))
    (hrlim : Tendsto rReg atTop (𝓝 r)) (hdlim : Tendsto dReg atTop (𝓝 b)) :
    let u := t + (1 / Complex.I) • c
    let g := p + (e + r + (1 / Complex.I) • b)
    (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ i, physicalTestAction A B (fun x ↦ (u x).ofLp) φ i = ∫ x, φ x • g x i) ∧
    (∀ du : E → E →L[ℝ] FV,
      Mollification.HasWeakFDerivOn volume (fun x ↦ (u x).ofLp) du U →
      physicalWeakApply A B (fun x ↦ (u x).ofLp) du =ᵐ[volume.restrict U]
        fun x ↦ (g x).ofLp) := by
  let AC := fun y j ↦ (A y j).map Complex.ofReal
  let BC := fun y ↦ (B y).map Complex.ofReal
  let f := fun k ↦ cutDirectSolver Ψ W₀ W₁ bminus σ β (θ k) χout a v
  let z := fun k x ↦ χout x • (cutPhysicalPDO (θ k)
    (fun y ξ ↦ (σ y (spatialPart ξ) * β ξ) • (1 : Mat)) v x +
    cutCompleteResidual AC BC Ψ W₁ bminus σ β (θ k) a v x)
  let uReg := fun k ↦ tReg k + (1 / Complex.I) • cReg k
  let gReg := fun k ↦ pReg k + (eReg k + rReg k + (1 / Complex.I) • dReg k)
  have huf : ∀ k, uReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (f k x) := by
    intro k
    have hh := representative_add (htrep k) (representative_smul (1 / Complex.I) (hcrep k))
    simpa only [uReg, f, cutDirectSolver, cutDirectCore, smul_add,
      smul_comm (χout _) (1 / Complex.I)] using hh
  have hgz : ∀ k, gReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2 (z k x) := by
    intro k
    have hh := representative_add (hprep k) (representative_add
      (representative_add (herep k) (hrrep k)) (representative_smul (1 / Complex.I) (hdrep k)))
    simpa only [gReg, z, cutCompleteResidual, AC, BC, smul_add,
      smul_comm (χout _) (1 / Complex.I)] using hh
  have hf : ∀ k, ContDiff ℝ 1 (f k) := by
    intro k
    exact (ho.smul (contDiff_cutDirectCore Ψ W₀ W₁ bminus σ β (θ k) a v
      hΨ (hW₀.add hW₁) hc hβ (hθ k) (hθcs k) hvcs)).of_le (by simp)
  have hfinite : ∀ k, WKB.firstOrderApply
      (fun y j ↦ (AC y j).mulVecLin) (fun y ↦ (BC y).mulVecLin) (f k) =ᵐ[volume.restrict U]
      z k := by
    intro k
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hid := firstOrderApply_cutDirectSolver_on_plateau AC BC Ψ W₀ W₁ bminus σ proj
      β (θ k) χout a v x hΨ hW₀ hW₁ hc (hσ x hx) hβ (hθ k) (hθcs k) hvcs
      (hplateau x hx) hdiag (hlead x hx) (hcomp x hx) (hcancel x hx)
    simpa only [f, z, (hplateau x hx).eq_of_nhds, one_smul] using hid
  have huLim : Tendsto uReg atTop (𝓝 (t + (1 / Complex.I) • c)) :=
    htlim.add (hclim.const_smul (1 / Complex.I))
  have hgLim : Tendsto gReg atTop (𝓝 (p + (e + r + (1 / Complex.I) • b))) :=
    hplim.add ((helim.add hrlim).add (hdlim.const_smul (1 / Complex.I)))
  constructor
  · intro φ hφ hφcs hφU i
    exact firstOrderApply_test_of_strongL2 A B hA hB hU.measurableSet uReg gReg _ _ f z hf
      huf hgz huLim hgLim hfinite hφ hφcs hφU i
  · intro du hdu
    exact physicalWeakApply_ae_of_strongL2 A B hA hB hU uReg gReg _ _ f z hf
      huf hgz huLim hgLim hfinite du hdu

end JanetCartan.CharacteristicTransport.CompleteResidual
