module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSolverTemplate
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Actual source-only instantiation of the native smooth source discrepancy.
The command consumes the SAME current38 source packet and the SAME uncut
chi3*Inv realization; it does not select a new source, inverse, or cutoff. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancyTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def uncut := `JanetCartan.PhysicalPrimary.OriginalUncutSolver

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

private def storeDoc (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) (target : Option Expr := none) : MetaM Expr := do
  let full := ns ++ name
  let result ← store full params value isDef target
  addDocStringCore full
    "Actual source discrepancy from the native real-source realization minus the identity on the same chi3*Inv representative; no second chi2, new inverse, source identity, or global zero-extension smoothness premise."
  return result

private def bodyAt (name : Name) (params : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? | throwError "source discrepancy: no body for {name}"
  return value.beta params

private def closed (target : Expr) (name : Name) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  let goals ← goal.mvarId!.apply (← mkConstWithFreshMVarLevels name)
  unless goals.isEmpty do throwError "source discrepancy: {name} left primitive goals"
  instantiateMVars goal

private def chooseRealization (name specName : Name) (params : Array Expr)
    (h : Expr) : MetaM (Expr × Expr) := do
  let t ← whnf (← inferType h)
  unless t.isAppOfArity ``Exists 2 do
    throwError "source discrepancy: missing native witness for {name}"
  let .lam _ _ body _ := t.appArg!
    | throwError "source discrepancy: native witness predicate changed for {name}"
  let v ← storeDoc name params (← mkAppM ``Classical.choose #[h]) true
  let spec ← storeDoc specName params (← mkAppM ``Classical.choose_spec #[h]) false
    (some (body.instantiate1 v))
  return (v,spec)

elab "construct_original_source_discrepancy" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun x _ => do
    unless x.size == 38 do throwError "source discrepancy: expected exact current38"
    let fixed := x[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) x
    let rawR ← bodyAt (current ++ `R) x
    unless rawR.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
      throwError "source discrepancy: native residual spine changed"
    let rargs := rawR.getAppArgs
    let hW := rargs[3]!
    let W := (← inferType hW).appArg!
    let hWopen ← closed (← mkAppM `IsOpen #[W]) `Metric.isOpen_ball
    let χ₃ := stat `χ₃
    let hSupport := mkAppN (mkConst (uncut ++ `source_support)) x
    let hInv := mkAppN (mkConst (uncut ++ `inverse_mem)) x
    let sourceRealization ← mkAppM (uncut ++ `exists_uncut_source_realization)
      #[hWopen,χ₃,hSupport,cur `Inv,hInv]
    let (z,zspec) ← chooseRealization `z `z_spec x sourceRealization

    -- This is exactly the source packet in SourceInterval657–681, not an
    -- existential assertion about an independently initialized realization.
    let packet := .proj ``And 1 (.proj ``And 0 (cur `fact5))
    let (_,p₁) ← chooseRealization `nativeS `afterS x packet
    let (_,p₂) ← chooseRealization `nativeA `afterA x p₁
    let (_,p₃) ← chooseRealization `nativeSR `afterSR x p₂
    let (AR,packet4) ← chooseRealization `nativeAR `nativeAR_spec x p₃
    let arSpec := part packet4 3
    let arSmooth ← forallBoundedTelescope (← inferType arSpec) (some 1) fun u _ => do
      let hu := u[0]!
      let spec := mkApp arSpec hu
      mkLambdaFVars u (.proj ``And 0 spec)
    let arAE ← forallBoundedTelescope (← inferType arSpec) (some 1) fun u _ => do
      let hu := u[0]!
      let spec := mkApp arSpec hu
      mkLambdaFVars u (.proj ``And 0 (.proj ``And 1 spec))
    let arSmooth ← storeDoc `nativeAR_smooth x arSmooth
    let arAE ← storeDoc `nativeAR_source_ae x arAE

    let nativeResidual := rargs[5]!
    unless nativeResidual.isAppOf `JanetCartan.RegularSector.NormalizedSolver.pairedResidual do
      throwError "source discrepancy: lost original native paired residual"
    let args := nativeResidual.getAppArgs
    let a := args[args.size-10:].toArray
    let Aop ← mkAppM `JanetCartan.RegularSector.NormalizedSolver.realSource
      #[a[0]!,a[1]!,a[2]!,a[5]!,a[6]!,a[7]!]
    let D ← mkAppM (ns ++ `sourceDiscrepancy)
      #[χ₃,cur `Inv,z,zspec,AR]
    let namedD ← storeDoc `discrepancy x D true
    let foldD (e : Expr) := e.replace fun q => if q == D then some namedD else none
    let Dspec ← forallBoundedTelescope (← inferType zspec) (some 1) fun h _ => do
      let hh := h[0]!
      let hd ← mkAppM (ns ++ `sourceDiscrepancy_contDiff)
        #[χ₃,cur `Inv,z,zspec,AR,arSmooth,hh]
      mkLambdaFVars h hd
    discard <| storeDoc `discrepancy_smooth x Dspec false (some (foldD (← inferType Dspec)))
    let Dae ← forallBoundedTelescope (← inferType zspec) (some 1) fun h _ => do
      let hh := h[0]!
      let hd ← mkAppM (ns ++ `sourceDiscrepancy_ae)
        #[hW,χ₃,cur `Inv,z,zspec,Aop,AR,arAE,hh]
      mkLambdaFVars h hd
    discard <| storeDoc `discrepancy_ae x Dae false (some (foldD (← inferType Dae)))
    logInfo "actual source discrepancy: native AR minus the same chi3*Inv smooth realization; exact AE source-minus-identity retained, no second chi2 or global zero-extension smoothness premise"

private def domainMeasure (x : Array Expr) : MetaM Expr := do
  let r ← bodyAt (current ++ `R) x
  unless r.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
    throwError "original tensor forcing: not the original local inverse domain"
  return r.getAppArgs[3]!

/-- The one canonical tensor-to-smooth-source map appearing in the actual
uncut ambient completion.  Only original masks, coefficients, and domain. -/
elab "retain_original_tensor_forcing" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun x _ => do
    unless x.size == 38 do throwError "original tensor forcing: expected the identical weak38"
    let fixed := x[:23].toArray
    let cur (field : Name) := mkAppN (mkConst (current ++ field)) x
    let mask (field : Name) := mkAppN (mkConst (`JanetCartan.PhysicalPrimary.OriginalSourceMasks ++ field)) fixed
    let hW ← domainMeasure x
    let W := (← inferType hW).appArg!
    let hη := mask `χsrc_smooth
    let η := (← inferType hη).appArg!
    let S ← mkAppM `tsupport #[(← inferType (mask `χ₂_smooth)).appArg!]
    let forcing ← mkAppM (ns ++ `compact_tensor_forcing_spec) #[W,S,cur `Q,η,cur `hQ,hη]
    let .letE _ _ input body _ ← inferType forcing
      | throwError "original tensor forcing: lost the literal tensor-to-source map"
    unless input.isAppOf `JanetCartan.CorrectedAtoms.cutoffStressSmoothSource do
      throwError "original tensor forcing: expected the original compact stress admission"
    let named ← storeDoc `tensor_input x input true
    let spec ← storeDoc `tensor_input_spec x forcing false (some (body.instantiate1 named))
    forallBoundedTelescope (← inferType spec) (some 1) fun tensors _ => do
      let both := mkAppN spec tensors
      discard <| storeDoc `tensor_forcing_smooth (x ++ tensors) (.proj ``And 0 both)
      discard <| storeDoc `tensor_input_ae (x ++ tensors) (.proj ``And 1 both)
      let plateau := mkAppN (mkConst (regular ++ `χsrc_plateau)) fixed
      let stress ← mkAppM (ns ++ `compact_tensor_forcing_eq_stress)
        #[cur `Q,η,plateau,tensors[0]!]
      discard <| storeDoc `tensor_forcing_eq_stress (x ++ tensors) stress

/-- Feed the actual parent weak equation the same compact tensor as the
ambient response, then close the smooth classical equation on its own core. -/
elab "derive_original_tensor_core_equation" : command => liftTermElabM do
  let eqn := `JanetCartan.PhysicalPrimary.OriginalUncutEquation
  forallBoundedTelescope (← getConstInfo (ns ++ `tensor_input)).type (some 38) fun x _ => do
    unless x.size == 38 do throwError "original core: expected the identical weak38"
    let cur (field : Name) := mkAppN (mkConst (current ++ field)) x
    let e (field : Name) := mkAppN (mkConst (eqn ++ field)) x
    let D (field : Name) := mkAppN (mkConst (ns ++ field)) x
    let hW ← domainMeasure x
    forallBoundedTelescope (← inferType (D `tensor_input_ae)) (some 1) fun tensors _ => do
      let h := mkAppN (← mkAppM `DFunLike.coe #[D `tensor_input]) tensors
      let smooth := mkAppN (mkConst (uncut ++ `uncut_solver_smooth)) (x.push h)
      let proof ← mkAppM (ns ++ `pointwise_core_of_ae_discrepancy)
        #[hW,e `core_open,e `core_subset_domain,cur `hQ,cur `hB,smooth,
          mkAppN (D `tensor_forcing_smooth) tensors,mkApp (D `discrepancy_smooth) h,
          mkAppN (D `tensor_input_ae) tensors,mkApp (D `discrepancy_ae) h,mkApp (e `physical_ae) h]
      let t ← inferType proof
      unless t.isAppOf `Set.EqOn do throwError "original core: expected pointwise EqOn"
      unless ← isDefEq t.appArg! (e `core) do throwError "original core: changed original chi2-core"
      discard <| storeDoc `physical_eqOn_tensor (x ++ tensors) proof false
        (some (mkApp t.appFn! (e `core)))

end JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancyTemplate
end
