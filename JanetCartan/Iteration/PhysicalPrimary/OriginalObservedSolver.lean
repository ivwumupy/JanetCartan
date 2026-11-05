module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSolver
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutObservation
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! # The native uncut solver is the complete observed inverse
Use the *actual* series identity of the normalized weak current to identify
its real inverse with the real compression's Neumann inverse. No localization
is introduced; in particular the admitted source is not multiplied by χ₂.
These are the ordinary positive operator estimates required to realize the
Sobolev classes of the graded observation as classical joint derivatives. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
namespace JanetCartan.PhysicalPrimary.OriginalObservedSolver

/-- Uniqueness of the native sum, rather than a new inverse choice. -/
theorem inverse_eq_of_native_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (K K' Inv : E →L[ℝ] E) (he : K = K')
    (hs : HasSum (fun j : ℕ ↦ (-K')^j) Inv) : Inv = neumannInverse K := by
  rw [he]
  exact hs.tsum_eq.symm

/-- Nonnegativity for the actual half-contraction's native inverse grade. -/
theorem inverse_grade_nonneg {C : ℕ → ℝ} (hC : ∀ s, 0 ≤ C s) (s : ℕ) :
    0 ≤ inverseTameConstant (1/2 : ℝ) C s :=
  (inverseTameConstant_pos (by norm_num) hC s).le

end JanetCartan.PhysicalPrimary.OriginalObservedSolver
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalObservedSolverTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalObservedSolver
private def cur := `JanetCartan.PhysicalInitialization.OriginalRegular.Current
private def inv := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native
private def paired := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Paired
private def uncut := `JanetCartan.PhysicalPrimary.OriginalUncutSolver
private def normPair := `JanetCartan.RegularSector.NormalizedSolver.normalizedPair
private def appl (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (key : Name) (xs : Array Expr) (v : Expr) (data := false)
    (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ key) xs v data t
  addDocStringCore (ns ++ key) "Same actual weak38 smooth solver, complex residual and full paired operator: the uncut chi3-localized full inverse and its original quadratic tame bounds (app:ch_regular:eq:inverse-remainder; app:ch_response:eq:response-actual-solver-formula)."
  return h
private def body (e : Expr) : MetaM Expr := do
  let some v := (← getConstInfo e.getAppFn.constName!).value? (allowOpaque := true)
    | throwError "native observed solver: lost body {e.getAppFn}"
  Core.betaReduce (v.beta e.getAppArgs)
private def substOp (h fromOp eq : Expr) (literal : Option Expr := none) : MetaM Expr := do
  let t ← inferType h
  let old ← if let some op := literal then pure op
    else if (t.find? fun e => e == fromOp).isSome then pure fromOp else body fromOp
  unless (t.find? fun e => e == old).isSome do
    throwError "native observed solver: missing exact native Inv in {h.getAppFn}"
  let P ← withLocalDeclD `A (← inferType fromOp) fun A => do
    mkLambdaFVars #[A] (t.replace fun e => if e == old then some A else none)
  mkAppM ``Eq.mp #[← mkAppM ``congrArg #[P,eq],h]

elab "identify_original_uncut_inverse_operator" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (cur ++ `normalized_solver)).type (some 38) fun xs _ => do
    let c (name : Name) := appl (cur ++ name) xs
    let n (name : Name) := appl (inv ++ name) xs
    let K ← mkAppM `JanetCartan.realOutputCompression #[n `Rcomplex]
    let he := n `real_compression
    let h ← mkAppM (ns ++ `inverse_eq_of_native_sum) #[K,c `Kloc,c `Inv,he,c `fact7]
    let h ← emit `native_inverse_eq xs h
    let ae ← substOp (appl (uncut ++ `uncut_solver_ae) xs) (c `Inv) h
    let S := n `pairedSolver
    let aeType ← inferType ae
    let some old := aeType.find? fun e => e.isAppOf `JanetCartan.CharacteristicTransport.CompleteResidual.physicalPairedSectorSum
      | throwError "native observed solver: missing the literal uncut half-pair in the smooth realization"
    let t := aeType.replace fun e => if e == old then some S else none
    discard <| emit `smooth_solver_ae xs ae false (some t)
    let pair ← body (← body S)
    unless pair.isAppOf normPair do throwError "native observed solver: complex full pair is {pair.getAppFn}"
    let hreal ← mkAppM `JanetCartan.RegularSector.NormalizedSolver.normalizedPair_conjugation #[pair.getAppArgs.back!]
    let rt := (← inferType hreal).replace fun e => if e.isAppOf normPair then some S else none
    discard <| emit `solver_real xs hreal false (some rt)
    let literal ← forallBoundedTelescope (← inferType (c `fact13)) (some 3) fun v _ => do
      let mem ← inferType (.proj ``And 0 (mkAppN (c `fact13) v))
      let image := mem.appArg!
      unless image.isAppOf `DFunLike.coe do throwError "native observed solver: unexpected inverse image head {image.getAppFn}"
      return image.getAppArgs[image.getAppArgs.size-2]!
    let invBound ← substOp (c `fact13) (c `Inv) h (some literal)
    discard <| emit `native_inverse_tame xs invBound
  logInfo "native uncut real inverse identified from its own Neumann HasSum; the same complex full paired operator represents every smooth input after chi3, with no chi2 or output recut"

private def mulLeft (e : Expr) : Expr := e.getAppArgs[e.getAppArgs.size-2]!
private def ordinary (xs : Array Expr) (h : Expr) (pref : Name) : MetaM Unit := do
  let (C,H,fnn) ← forallBoundedTelescope (← inferType h) (some 3) fun args _ => do
    let hs := mkAppN h args
    let rhs := (← inferType (.proj ``And 1 hs)).appArg!
    let cs := mulLeft rhs
    let high := mulLeft rhs.appArg!.appArg!
    unless rhs.isAppOf ``HMul.hMul && rhs.appArg!.isAppOf ``HAdd.hAdd && rhs.appArg!.appArg!.isAppOf ``HMul.hMul do
      throwError "native observation: tame bound changed on {pref}"
    let s := args[0]!
    let cNN ← if pref == `I then
        mkAppM (ns ++ `inverse_grade_nonneg) #[appl (inv ++ `gain_cost_nonneg) xs[:23].toArray,s]
      else pure (mkApp (appl (paired ++ `fact0) xs[:23].toArray) s)
    let hn ← if pref == `I then do
        let coeff := high.appArg!
        let nn := mkApp (appl (inv ++ `coefficient_nonneg) xs) coeff.appArg!
        mkAppM `add_nonneg #[← mkAppOptM `zero_le_one #[some (mkConst `Real),none,none,none,none],nn]
      else do
        let cn (v : Expr) := mkAppN (mkConst `JanetCartan.cNorm_nonneg v.getAppFn.constLevels!) v.getAppArgs
        let two := cn (mulLeft high).appArg!
        let three := cn high.appArg!
        let zeroOne ← mkAppOptM `zero_le_one #[some (mkConst `Real),none,none,none,none]
        mkAppM `add_nonneg #[← mkAppM `add_nonneg #[zeroOne,two],three]
    let nn ← mkAppM ``And.intro #[cNN,hn]
    return (← mkLambdaFVars #[s] cs,← mkLambdaFVars #[s] high,← mkLambdaFVars #[s] nn)
  let C ← emit (pref ++ `cost) xs C true
  let H ← emit (pref ++ `high) xs H true
  forallBoundedTelescope (← inferType fnn) (some 1) fun ss _ => do
    let zero ← mkNumeral (mkConst `Real) 0
    let z := mkAppN fnn ss
    for (key,p,op) in #[(`cost_nonneg,Expr.proj ``And 0 z,C),(`high_nonneg,Expr.proj ``And 1 z,H)] do
      let tp ← mkForallFVars ss (← mkAppM ``LE.le #[zero,mkAppN op ss])
      discard <| emit (pref ++ key) xs (← mkLambdaFVars ss p) false (some tp)
  discard <| emit (pref ++ `bound) xs h

elab "retain_original_uncut_ordinary_costs" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (cur ++ `normalized_solver)).type (some 38) fun xs _ => do
    ordinary xs (appl (ns ++ `native_inverse_tame) xs) `I
    ordinary xs (appl (inv ++ `paired_solver_tame) xs) `S
  logInfo "ordinary native inverse and paired solver costs and coefficient highs, with all nonnegativity premises closed"

end JanetCartan.PhysicalPrimary.OriginalObservedSolverTemplate
end

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
identify_original_uncut_inverse_operator
retain_original_uncut_ordinary_costs
