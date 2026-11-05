module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Exact current38+sector projections of the original retarded primitives.
Only the existing native proofs and fixed coordinate regrouping are used;
there is no choice of an operator, regular family, threshold or source cap. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedSymbolsTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def target := `JanetCartan.PhysicalPrimary.OriginalRetardedSymbols

private def tail (e : Expr) : Nat → Expr
  | 0 => e
  | i+1 => tail (.proj ``And 1 e) i

private def part (e : Expr) (i : Nat) : Expr := .proj ``And 0 (tail e i)

private def retain (name : Name) (params : Array Expr) (proof : Expr)
    (type : Option Expr := none) : MetaM Expr := do
  let name := target ++ name
  let result ← store name params proof false type
  addDocStringCore name "Actual same-current native retarded primitive, retaining the full extended Q/B, original phases, chart, masks and operator. Consumer: physical measured residual/paired solver hstep (retarded-kernel; energy-complete-residual)."
  return result

/-- Emit only exact projections and the two finite algebraic deductions from
native Current.fact4. Its entire original input telescope is unchanged. -/
elab "retain_original_current_retarded_symbols" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `fact35)).type (some 23) fun fixed _ => do
    unless fixed.size == 23 do throwError "retarded symbols: expected original23 static prefix"
    let hpos := mkAppN (mkConst (regular ++ `fact35)) fixed
    discard <| retain `amplitude_cost_pos fixed hpos
    forallBoundedTelescope (← inferType hpos) (some 2) fun data _ => do
      unless data.size == 2 do throwError "retarded symbols: expected native center and order"
      let hnonneg ← mkAppM `le_of_lt #[mkAppN hpos data]
      discard <| retain `amplitude_cost_nonneg (fixed ++ data) hnonneg
  forallBoundedTelescope (← getConstInfo (current ++ `fact4)).type (some 39) fun params _ => do
    unless params.size == 39 do throwError "retarded symbols: expected current38 and original sector"
    let fixed := params[:23].toArray
    let now := params[:38].toArray
    let p := params[38]!
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) now
    let native := mkApp (cur `fact4) p
    for (name, index) in #[( `chart_buffer, 7), (`chart_phase_smooth, 8),
        (`chart_phase_differential, 9), (`chart_inverse_coordinates, 10),
        (`chart_mixed_near, 13), (`chart_phase_profile, 14),
        (`global_phase_smooth, 17), (`global_phase_diagonal, 18),
        (`solver_phase_germ, 19), (`residual_phase_germ, 20),
        (`solver_retarded_bounds, 23), (`residual_retarded_bounds, 24),
        (`physical_residual_retarded_bounds, 25), (`endpoint_native, 26),
        (`full_physical_pencil_identity, 27)] do
      discard <| retain name params (part native index)
    let hcoordinates := mkAppN (mkConst (target ++ `chart_inverse_coordinates)) params
    forallBoundedTelescope (← inferType hcoordinates) (some 2) fun q _ => do
      let value := part (mkAppN hcoordinates q) 1
      let proof ← mkLambdaFVars q value
      discard <| retain `chart_source_time params proof
    let rawFs ← mkAppM `JanetCartan.RegularSector.FiniteAssembly.selectedBufferedAmplitude
      #[stat `f,p,cur `Q,cur `B,mkApp (cur `Φ) p,mkApp (cur `C) p]
    let rawWs ← mkAppM `JanetCartan.RegularSector.FiniteAssembly.selectedConicAmplitude
      #[stat `f,p,cur `Q,cur `B,mkApp (cur `Φ) p,mkApp (cur `C) p,mkApp (stat `angular) p]
    discard <| store (target ++ `Fs) params rawFs true
    discard <| store (target ++ `Ws) params rawWs true
    addDocStringCore (target ++ `Fs) "Literal original buffered amplitudes on the same full Q/B and native flow/chart, including index two's full physical derivative (energy-complete-residual)."
    addDocStringCore (target ++ `Ws) "Literal original conic amplitudes on the same full Q/B, flow/chart and angular mask; no symbol is reselected (retarded-kernel)."
    let fsdata := tail native 28
    forallBoundedTelescope (← inferType fsdata) (some 1) fun js _ => do
      unless js.size == 1 do throwError "retarded symbols: expected original Fin3 amplitude"
      let all := params ++ js
      let data := mkAppN fsdata js
      for (name, index) in #[(`buffered_smooth, 0), (`buffered_compact, 1),
          (`buffered_support, 2), (`buffered_ball_support, 3),
          (`collared_smooth, 4), (`collared_support, 5),
          (`collared_zero_before, 6), (`buffered_pencil_germ, 7)] do
        discard <| retain name all (part data index)
      discard <| retain `conic_seminorms all (tail data 8)
      let hs := mkAppN (mkConst (target ++ `collared_smooth)) all
      let hjoint ← mkAppM (target ++ `joint_smooth_of_matrix_smooth) #[hs]
      discard <| retain `conic_joint_smooth all hjoint
    let fin3 := mkApp (mkConst ``Fin) (mkNatLit 3)
    let one3 ← mkNumeral fin3 1
    let w1 := mkApp (cur `W₁) p
    let hjoint := mkAppN (mkConst (target ++ `conic_joint_smooth)) (params.push one3)
    let jointType ← inferType hjoint
    unless jointType.isAppOf `ContDiff do throwError "retarded symbols: expected literal ContDiff head"
    let jointW1 ← mkAppM `JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.jointAmplitude #[w1]
    discard <| retain `W1_joint_smooth params hjoint (some (mkApp jointType.appFn! jointW1))
    let hseminorm := mkAppN (mkConst (target ++ `conic_seminorms)) (params.push one3)
    forallBoundedTelescope (← inferType hseminorm) (some 1) fun ms _ => do
      let proof := mkAppN hseminorm ms
      let type ← inferType proof
      unless type.isAppOfArity ``And 2 do throwError "retarded symbols: expected bounded/budget pair"
      let oldW := type.getAppArgs[0]!.appArg!
      let expected := type.replace fun e ↦ if e == oldW then some w1 else none
      discard <| retain `W1_seminorms (params ++ ms) proof (some expected)
    let h0 := mkAppN (mkConst (target ++ `solver_retarded_bounds)) params
    let h1 := mkAppN (mkConst (target ++ `residual_retarded_bounds)) params
    let h0args := (← inferType h0).getAppArgs
    unless h0args.size == 17 do throwError "retarded symbols: native retained-bound argument spine changed"
    let fin2 := mkApp (mkConst ``Fin) (mkNatLit 2)
    let base ← withLocalDeclD `o fin2 fun o ↦ mkLambdaFVars #[o] (mkAppN (stat `base) #[o,p])
    let cost ← withLocalDeclD `o fin2 fun o ↦ mkLambdaFVars #[o] (mkAppN (stat `cost) #[o,p])
    let op ← withLocalDeclD `o fin2 fun o ↦ mkLambdaFVars #[o] (mkAppN (cur `Op) #[o,p])
    let both ← mkAppM (target ++ `retained_signed_bounds_both_orders)
      #[h0args[12]!,rawWs,base,cost,op,h0,h1]
    discard <| retain `retained_signed_bounds params both
  logInfo "actual current38+sector retarded primitives: exact chart/phase/germs, all three full-Q/B buffered/collared/conic symbols and seminorms, native W1 and BOTH retained signed operators; no new choice or threshold"

end JanetCartan.PhysicalPrimary.OriginalRetardedSymbolsTemplate
end
