module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalRegularTemplate

/-! Specialize the original native endpoint and algebraic certificates; select
only the already-proved algebraic tuple before any source contraction/history.
The fixed-center majorants change no symbol, normal witness or signed gain. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPdoProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
open PhysicalInitialization.OriginalRegularTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def target := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
private def algebraic := target ++ `Algebraic

private def tail (e : Expr) : Nat → Expr
  | 0 => e
  | i+1 => tail (.proj ``And 1 e) i

private def part (e : Expr) (i : Nat) : Expr := .proj ``And 0 (tail e i)

/-- Check only the literal function application spine. In particular never
WHNF an already exposed ContDiff/normal-amplitude goal. -/
private def applyChecked (f : Expr) (args : Array Expr) : MetaM Expr := do
  let mut result := f
  let mut type ← inferType f
  for arg in args do
    let type' ← whnf type
    let .forallE _ dom body _ := type' | throwError "native PDO application spine ended early"
    unless ← isDefEq (← inferType arg) dom do
      throwError "native PDO argument mismatch: {← inferType arg}\nexpected: {dom}"
    result := mkApp result arg
    type := body.instantiate1 arg
  return result

private def smoothOn (domain proof : Expr) : MetaM Expr := do
  let name := `ContDiff.contDiffOn
  let rec options (type : Expr) : Array (Option Expr) :=
    match type with
    | .forallE n _ body _ =>
      #[if n == `s then some domain else if n == `h then some proof else none] ++ options body
    | .mdata _ body => options body
    | _ => #[]
  let args := options (← getConstInfo name).type
  unless (args.filter Option.isSome).size == 2 do
    throwError "native smoothness application expects original s/h binders"
  mkAppOptM name args

private def retainMajorant (name : Name) (fixed : Array Expr) (D : Expr) : MetaM Unit := do
  let raw ← mkAppM (target ++ `finite_profile_majorant) #[D]
  let major ← store (target ++ name) fixed raw true
  let hnonneg ← mkAppM (target ++ `finite_profile_majorant_nonneg) #[D]
  let hle ← mkAppM (target ++ `le_finite_profile_majorant) #[D]
  let fold (type : Expr) := type.replace fun e ↦ if e == raw then some major else none
  discard <| store (target ++ Name.mkSimple s!"{name}_nonneg") fixed hnonneg false
    (some (fold (← inferType hnonneg)))
  discard <| store (target ++ Name.mkSimple s!"le_{name}") fixed hle false
    (some (fold (← inferType hle)))

private def existsAbstract (name : Name) (witness proof : Expr) : MetaM Expr := do
  let type ← inferType witness
  let proposition ← inferType proof
  let predicate ← withLocalDeclD name type fun x ↦ do
    mkLambdaFVars #[x] (proposition.replace fun e ↦ if e == witness then some x else none)
  mkAppOptM ``Exists.intro #[some type,some predicate,some witness,some proof]

/-- Retain the original fact15 algebraic epsilon/box/normal/three profiles ONCE
on the original23+sector prefix. No physical history or Q/B is an argument. -/
elab "retain_original_pdo_static_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `fact15)).type (some 24) fun pars _ => do
    unless pars.size == 24 do throwError "original algebraic choice: expected original23 plus sector"
    let all := mkAppN (mkConst (regular ++ `fact15)) pars
    let native ← store (algebraic ++ `exists_data) pars (tail all 2)
    selectCompact algebraic pars native
  forallBoundedTelescope (← getConstInfo (regular ++ `f)).type (some 23) fun fixed _ => do
    unless fixed.size == 23 do throwError "original PDO profiles: expected pre-contraction original23"
    retainMajorant `Dendpoint fixed (mkAppN (mkConst (regular ++ `Dpdo)) fixed)
    retainMajorant `Dalgebraic fixed (mkAppN (mkConst (algebraic ++ `C)) fixed)
  logInfo "native original23 endpoint and algebraic profiles: original fact15 chosen once before sigma/history; two fixed finite-center majorants, no new analytic premise"

/-- Apply actual current chartData26 and the once-selected original algebraic
continuation at twice the native threshold, to the SAME full current Q/B. -/
elab "apply_original_current_pdo_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `fact4)).type (some 39) fun pars _ => do
    unless pars.size == 39 do throwError "actual native PDO profiles: expected current38 plus sector"
    let x := pars[:38].toArray
    let fixed := x[:23].toArray
    let p := pars[38]!
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) x
    let chosen (name : Name) := mkAppN (mkConst (algebraic ++ name)) (fixed.push p)
    let hM ← mkAppM `le_of_lt #[stat `fact0]
    let hD := mkAppN (mkConst (target ++ `le_Dendpoint)) (fixed.push p)
    let endpoint := part (mkAppN (mkConst (current ++ `fact4)) pars) 26
    let endpoint ← mkAppM (target ++ `endpoint_profile_mono) #[hM,hD,endpoint]
    discard <| store (target ++ `endpoint) pars endpoint
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    unless fa.size == 7 do throwError "original finite mask family changed"
    let Ω := fa[1]!
    let center := fa[2]!
    let radius := fa[3]!
    let L := stat `L
    let twice ← mkAppM ``HMul.hMul #[← mkNumeral (mkConst `Real) 2,L]
    let hrad ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.radialThreshold_ge_one #[f]
    let htwice ← mkAppM (target ++ `twice_admitted_threshold) #[hrad,stat `hL]
    let hQon ← smoothOn Ω (cur `hQ)
    let hBon ← smoothOn Ω (cur `hB)
    let hsub ← mkAppM `Set.subset_univ #[Ω]
    let hmap ← mkAppM `Set.MapsTo.mono_left #[cur `fact0,hsub]
    let KQ ← mkAppM `Metric.closedBall #[center,radius]
    let hKQ ← mkAppM `ProperSpace.isCompact_closedBall #[center,radius]
    let low ← applyChecked (cur `fact2) #[KQ,hKQ]
    let actual ← applyChecked (chosen `continuation)
      #[twice,htwice,cur `Q,cur `B,hQon,hBon,hmap,part low 0,part low 1]
    let actual ← store (target ++ `algebraic_native_application) pars actual
    withLocalDeclD `o (mkApp (mkConst ``Fin) (mkNatLit 2)) fun o => do
      let full := pars.push o
      let symbol ← mkAppM `JanetCartan.RegularSector.FiniteAssembly.selectedAlgebraicSymbol
        #[f,p,twice,cur `Q,cur `B,o]
      let membership ← mkAppM (target ++ `selected_algebraic_symbol_mem)
        #[f,p,twice,cur `Q,cur `B,o]
      let pair ← applyChecked (tail actual 5) #[symbol,membership]
      let pair ← mkAppM ``And.intro #[part pair 1,part pair 2]
      let hC := mkAppN (mkConst (target ++ `le_Dalgebraic)) (fixed.push p)
      let bound ← mkAppM (target ++ `algebraic_profile_mono) #[hC,pair]
      let bound ← store (target ++ `algebraic_bounds) full bound
      let normal := (← inferType bound).getAppArgs[0]!
      let na := normal.getAppArgs
      let packaged ← existsAbstract `N na[na.size-1]! bound
      let packaged ← existsAbstract `R na[na.size-2]! packaged
      discard <| store (target ++ `algebraic) full packaged
  logInfo "actual current38+sector endpoint chartData26 and BOTH original algebraic b/pb symbols at 2*nativeL: unchanged full Q/B/W1/source/masks/normal boxes/gains; only the fixed profiles are majorized"

end JanetCartan.PhysicalPrimary.OriginalPdoProfilesTemplate
end
