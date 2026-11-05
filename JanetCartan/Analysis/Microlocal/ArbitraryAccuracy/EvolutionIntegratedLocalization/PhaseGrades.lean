module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.Stationarity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Phase

/-!
# Joint two-time phase grades for half-space integration

The elapsed time is a differentiated integration variable in
`app:ch_regular:eq:chain-tail`. The original two-time phase is pulled back by
one fixed linear map; the remaining phase is a fixed quadratic polynomial.
This proves the joint gradient grades needed by the half-space kernel estimate,
without replacing them by estimates for fixed elapsed times.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}

attribute [local fun_prop] ContDiff.inner

/-- The single linear coordinate map retaining both original times and all
joint integration variables. Its norm is fixed independently of frequency,
coefficient scale and accuracy (`app:ch_regular:eq:high-phase`). -/
def elapsedJointCoordinates : (ℝ × JointVariables (Euclidean (d + 1))) →L[ℝ]
    SymbolBudgets.TwoTimePoint d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ ((p.2.1.1 0, p.2.1.1 0 - p.1, spatialPart p.2.1.1),
        spatialPart p.2.2.1)
      map_add' := by
        intro p w
        ext <;> simp [spatialPart]
        ring
      map_smul' := by
        intro a p
        ext <;> simp [spatialPart, mul_sub] }

/-- Removing the original two-time phase leaves a fixed smooth polynomial
in the joint variables (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_jointElapsedPhase_zero (backward : Bool) (x y : Euclidean (d + 1)) :
    ContDiff ℝ ∞ (jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y) := by
  unfold jointElapsedPhase jointPhase forwardPhase reversePhase elapsedPhase
  cases backward <;>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> fun_prop

private theorem jointElapsedPhase_split (backward : Bool) (Ψ : TwoTimePhase d)
    (x y : Euclidean (d + 1)) :
    jointElapsedPhase backward Ψ x y =
      (if backward then -(SymbolBudgets.jointPhase Ψ ∘ elapsedJointCoordinates)
        else SymbolBudgets.jointPhase Ψ ∘ elapsedJointCoordinates) +
      jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y := by
  funext p
  cases backward <;>
    simp only [jointElapsedPhase, jointPhase, Bool.false_eq_true, ↓reduceIte,
      forwardPhase, reversePhase, elapsedPhase, Pi.add_apply, Pi.neg_apply,
      Function.comp_apply, SymbolBudgets.jointPhase, elapsedJointCoordinates,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] <;> ring

/-- A smooth original joint two-time phase produces a smooth joint elapsed
phase. Applied to a supported smooth extension, this is the phase-smoothness
input of `norm_integral_regularizedElapsedKernel_le`
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem contDiff_jointElapsedPhase (backward : Bool) (Ψ : TwoTimePhase d)
    (x y : Euclidean (d + 1)) (hΨ : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ)) :
    ContDiff ℝ ∞ (jointElapsedPhase backward Ψ x y) := by
  rw [jointElapsedPhase_split]
  have hc := hΨ.comp (elapsedJointCoordinates (d := d)).contDiff
  cases backward
  · exact hc.add (contDiff_jointElapsedPhase_zero false x y)
  · exact hc.neg.add (contDiff_jointElapsedPhase_zero true x y)

/-- Original joint two-time gradient grades imply the full elapsed-gradient
grades. The linear pullback costs only a fixed norm to the derivative order;
the fixed polynomial contributes a compact seminorm and NO extra power of
the coefficient scale. This is the precise phase input to the half-space
estimate in `app:ch_regular:eq:chain-tail`. -/
theorem norm_iteratedFDeriv_jointElapsedPhase_gradient_le
    (backward : Bool) (Ψ : TwoTimePhase d) (x y : Euclidean (d + 1))
    (hΨ : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ))
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    {L : ℝ} (hL : 1 ≤ L) (P : ℕ → ℝ)
    (p : ℝ × JointVariables (Euclidean (d + 1))) (hp : p ∈ K)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase Ψ))
      (elapsedJointCoordinates p)‖ ≤ P j * L ^ j) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward Ψ x y)) p‖ ≤
      (P j * ‖elapsedJointCoordinates (d := d)‖ ^ (j + 1) +
        cNorm K (j + 1) (jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y)) * L ^ j := by
  let f := SymbolBudgets.jointPhase Ψ ∘ elapsedJointCoordinates (d := d)
  let Q := jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y
  have hf : ContDiff ℝ ∞ f := hΨ.comp (elapsedJointCoordinates (d := d)).contDiff
  have hQ : ContDiff ℝ ∞ Q := contDiff_jointElapsedPhase_zero backward x y
  have hfb : ‖iteratedFDeriv ℝ (j + 1) f p‖ ≤
      (P j * ‖elapsedJointCoordinates (d := d)‖ ^ (j + 1)) * L ^ j := by
    dsimp only [f]
    rw [(elapsedJointCoordinates (d := d)).iteratedFDeriv_comp_right hΨ p (by simp)]
    apply ((iteratedFDeriv ℝ (j + 1) (SymbolBudgets.jointPhase Ψ)
      (elapsedJointCoordinates p)).norm_compContinuousLinearMap_le
        (fun _ ↦ elapsedJointCoordinates)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hbj := hb j
    rw [norm_iteratedFDeriv_fderiv] at hbj
    exact (mul_le_mul_of_nonneg_right hbj (pow_nonneg (norm_nonneg _) _)).trans_eq (by ring)
  have hqb : ‖iteratedFDeriv ℝ (j + 1) Q p‖ ≤ cNorm K (j + 1) Q * L ^ j :=
    (norm_iteratedFDeriv_le_cNorm hK (hQ.of_le (by simp)) hp le_rfl).trans
      (le_mul_of_one_le_right (cNorm_nonneg _ _ _) (one_le_pow₀ hL))
  rw [norm_iteratedFDeriv_fderiv, jointElapsedPhase_split]
  have hsum : ‖iteratedFDeriv ℝ (j + 1) (if backward then -f else f) p‖ ≤
      (P j * ‖elapsedJointCoordinates (d := d)‖ ^ (j + 1)) * L ^ j := by
    cases backward
    · exact hfb
    · simpa only [↓reduceIte, iteratedFDeriv_neg_apply, norm_neg] using hfb
  have hsm : ContDiff ℝ ∞ (if backward then -f else f) := by
    cases backward
    · exact hf
    · exact hf.neg
  rw [iteratedFDeriv_add_apply (hsm.contDiffAt.of_le (by simp)) (hQ.contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans ((add_le_add hsum hqb).trans_eq (by dsimp only [Q]; ring))

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
