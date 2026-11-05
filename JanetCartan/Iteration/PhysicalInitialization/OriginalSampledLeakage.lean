module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedObservedResidual.CompleteSignedLeakage
public import JanetCartan.Iteration.PhysicalPrimary.OriginalOperatorProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public meta import Lean

/-!
# Actual leakage budgets for the original signed-product inverse

The fixed retarded and elliptic factors, their collars and the original
Q/full-B budgets from the physical history are supplied to the complete
leakage estimate on the original (non-universal) coefficient ball. The
result precedes all currents. The terminal annulus supplies its two radii;
the resulting positive times determine the oriented proof-mask bands
ra/thi and ra/tlo (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalSampledLeakage
/-- The single prehistory budget for both actual matrix coefficient fields. -/
def coefficientBudget (AQ AB : ℕ → ℝ) : ℕ → ℝ := fun k ↦ max (AQ k) (AB k)
theorem coefficientBudget_nonneg (AQ AB : ℕ → ℝ) (h : ∀ k, 0 ≤ AQ k) :
    ∀ k, 0 ≤ coefficientBudget AQ AB k := fun k ↦ (h k).trans (le_max_left _ _)
theorem profiles_at_slow_scale {n : ℕ} {D : Set (Euclidean n)}
    {Q : Euclidean n → Fin n → MetricTensor n} {B : Euclidean n → MetricTensor n}
    {reserve : ℕ} {T L : ℝ} {AQ AB : ℕ → ℝ} (hAQ : ∀ k, 0 ≤ AQ k)
    (hT : 0 ≤ T) (hL : T ≤ L)
    (hp : HasDerivativeProfile D Q reserve T AQ ∧ HasDerivativeProfile D B reserve T AB) :
    HasDerivativeProfile D Q reserve L (coefficientBudget AQ AB) ∧
      HasDerivativeProfile D B reserve L (coefficientBudget AQ AB) := by
  constructor <;> intro k
  · exact (hp.1 k).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hT hL _)
      (pow_nonneg hT _) (coefficientBudget_nonneg AQ AB hAQ k))
  · exact (hp.2 k).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ hT hL _)
      (pow_nonneg hT _) (coefficientBudget_nonneg AQ AB hAQ k))
theorem actual_scale_nonneg {S R : ℝ} (hS : 2 ≤ S) (hR : S ≤ R) (j : ℕ) :
    0 ≤ currentCoefficientScale R j :=
  zero_le_one.trans (one_le_currentCoefficientScale ((by norm_num : (1:ℝ) ≤ 2).trans (hS.trans hR)) j)
theorem open_ball_zero (n : ℕ) (r : ℝ) : IsOpen (ball (0 : Euclidean n) r) := isOpen_ball
theorem norm_of_unit_range {E : Type} (a : E → ℝ) (h : ∀ y, a y ∈ Icc (0:ℝ) 1) :
    ∀ y, ‖a y‖ ≤ 1 := fun y ↦ (Real.norm_of_nonneg (h y).1).trans_le (h y).2
end JanetCartan.PhysicalInitialization.OriginalSampledLeakage
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledLeakage
open Lean Meta Elab Command OriginalProtectedTemplate
private def base := `JanetCartan.PhysicalInitialization.OriginalSampledLeakage
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def mk (name : Name) (x : Array Expr) := mkAppN (mkConst name) x
private def part (h : Expr) : Nat → Expr
  | 0 => .proj ``And 0 h
  | k+1 => part (.proj ``And 1 h) k

/- On the actual native33 coefficient budget, retain the constants for all
   terminal annuli. The colored terminal supplies a,b next; ra/rb always
   remain the original retarded operator's bands. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (op ++ `AQ)).type (some 33) fun x _ => do
    let s := x[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) x[0]!
    let hn := x[1]!
    let ordinary := #[n] ++ x[1:21].toArray
    let get (k : Name) := mk (reg ++ k) s
    let total (k : Name) := mk (op ++ k) x
    let mask (k : Name) := mk (`JanetCartan.PhysicalPrimary.OriginalSourceMasks ++ k) s
    let q (k : Name) := mk (`JanetCartan.PhysicalInitialization.OriginalProtected ++ k) ordinary
    let capped := mk `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,ordinary[20]!]
    let seed := ordinary.set! 20 capped
    let μ := mk `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure seed
    let hμ := mk `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure seed
    let screened := mk (reg ++ `screenedRadius) #[n,hn,q `r,μ]
    let hp := mk (reg ++ `screened_pos) #[n,hn,q `r,μ,q `fact2,hμ]
    let core := mk (reg ++ `core_spec) #[n,hn,screened,hp]
    let f := get `f
    let a := (← inferType f).getAppArgs
    unless a.size == 7 do throwError "missing the original finite family"
    let hΩ := mk ``open_ball_zero #[n,mk `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,hn]]
    let hχ₂ := mask `χ₂_smooth
    let hχ₃ := mask `χ₃_smooth
    let χ₂ := (← inferType hχ₂).appArg!
    let χ₃ := (← inferType hχ₃).appArg!
    let hb₂ ← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[get `χ₂]
    let hb₃ ← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[get `χ₃]
    let input ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask #[f]
    let hinput ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask_range #[f]
    let E := (← inferType input).bindingDomain!
    let hin := mk ``norm_of_unit_range #[E,input,hinput]
    let hout := mk ``norm_of_unit_range #[E,get `output,get `fact18]
    let hband ← forallBoundedTelescope (← inferType (get `fact34)) (some 1) fun p _ => do
      mkLambdaFVars p (← mkAppM ``le_of_lt #[mkAppN (get `fact34) p])
    let hplateau ← forallBoundedTelescope (← inferType (get `fact24)) (some 1) fun p _ => do
      let h ← mkAppM ``le_refl #[get `L]
      mkLambdaFVars p (.proj ``And 0 (mkAppN (get `fact24) (p ++ #[get `L,h])))
    let budget ← store (base ++ `Aprofile) x (mk ``coefficientBudget #[total `AQ,total `AB]) true
    let hbudget ← store (base ++ `Aprofile_nonneg) x (mk ``coefficientBudget_nonneg #[total `AQ,total `AB,total `fact1])
    let name := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.exists_retained_prescribed_complete_residual_leakage_constants
    let info ← getConstInfo name
    let data := mkAppN (mkConst name (info.levelParams.map (fun _ => .zero)))
      #[x[0]!,a[1]!,hΩ,a[2]!,a[3]!,part core 0,part core 2,a[4]!,a[5]!,a[6]!,f,q `fact14,get `fact6,
        budget,hbudget,χ₂,χ₃,hχ₂,hχ₃,mask `χ₂_compact,mask `χ₃_compact,hb₂,hb₃,
        get `L,get `hL,get `angular,get `χout,get `χsource,get `hs,get `output,get `fact17,get `fact19,get `fact20,
        hout,hin,get `fact23,get `fact22,get `base,get `cost,get `Rbox,get `Dpdo,get `Dgain,get `Gain,
        get `ra,get `rb,get `amplitudeCost,get `fact33,hband,get `fact35,get `fact36,hplateau,get `fact37,get `fact15]
    discard <| store (base ++ `on_native_inverse) x data
    logInfo "Complete residual leakage constants on the actual physical coefficient domain, finite inverse and native33 prehistory Q/full B budget, for every terminal annulus."

/- The two transport times are selected after the terminal annulus, but
   before the primitive or reflected chain, any history or frequency. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  let key := base ++ `on_native_inverse
  forallBoundedTelescope (← getConstInfo key).type (some 36) fun x _ => do
    select (base ++ `Window) x (mk key x)

/- No coefficient premise at the later history: both original fields obey the
   SAME fixed budget used above, on every compact including the solver ball. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  let key := op ++ `continuation
  forallBoundedTelescope (← getConstInfo key).type (some 39) fun x _ => do
    let fixed := x[:33].toArray
    let total (k : Name) := mk (op ++ k) fixed
    let h := mk key x
    let hp := Expr.proj ``And 1 (.proj ``And 1 h)
    let nonneg := mk ``actual_scale_nonneg #[total `S,x[33]!,total `fact0,x[34]!,x[35]!]
    let T := (← inferType nonneg).appArg!
    forallBoundedTelescope (← inferType hp) (some 2) fun D _ => do
      let p := mkAppN hp D
      let raw := (← inferType (.proj ``And 0 p)).getAppArgs
      let rawB := (← inferType (.proj ``And 1 p)).getAppArgs
      -- Read Q and B from their actual declared profiles; no equality search
      -- through a reconstructed physical history or matrix norm.
      let Q := raw[raw.size-4]!
      let B := rawB[rawB.size-4]!
      withLocalDeclD `L (mkConst ``Real) fun L => do
        withLocalDeclD `hL (← mkAppM ``LE.le #[T,L]) fun hL => do
          let n := mkApp (mkConst ``Nat.succ) x[0]!
          let v := mk ``profiles_at_slow_scale #[n,D[0]!,Q,B,x[28]!,T,L,total `AQ,total `AB,total `fact1,nonneg,hL,p]
          discard <| store (base ++ `current_coefficients) (x ++ D ++ #[L,hL]) v
end JanetCartan.PhysicalInitialization.OriginalSampledLeakage
end
