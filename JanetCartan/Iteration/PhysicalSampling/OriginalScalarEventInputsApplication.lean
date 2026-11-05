module

public meta import Lean

/-!
# The original scalar kernel family at a common finite ceiling

Abstract the already checked current-row kernels over the SAME original finite
index and independently supplied positive color rates. This names only a
function on the original index; it makes no additional geometric choice and
retains every row's original mask and full finite-rate phase
(`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalScalarEventInputsApplication
open Lean Meta Elab Command

private def ns : Name := `JanetCartan.PhysicalSampling.OriginalScalarFamily
private def row : Name := ns ++ `Row

private def store (name : Name) (params : Array Expr) (value : Expr)
    (expected : Option Expr := none) : MetaM Expr := do
  let type ← match expected with
    | some type => pure type
    | none => inferType value
  let type ← mkForallFVars params (← instantiateMVars type)
  let value ← mkLambdaFVars params (← instantiateMVars value)
  if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry ||
      type.hasFVar || value.hasFVar then
    throwError "actual scalar event inputs: open or recovered declaration {name}"
  if ← isProp type then
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  else
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  logInfo m!"checked SAME original scalar family field {name}"
  return mkAppN (mkConst name) params

/-- Obtain the actual current43, original row and J/rate/positivity binders from
an existing kernel, rather than reconstructing any selected geometric object. -/
private def withFamily
    (k : Array Expr → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (row ++ `kernel)).type (some 43) fun current tail => do
    unless current.size == 43 do throwError "actual scalar event inputs: expected current43"
    let tail ← whnf tail
    unless tail.isForall do throwError "actual scalar event inputs: original row missing"
    withLocalDeclD `i tail.bindingDomain! fun i => do
      withLocalDeclD `J (mkConst ``Nat) fun J => do
        let rowHead := mkAppN (mkConst (row ++ `kernel)) (current ++ #[i, J])
        let rateType := (← whnf (← inferType rowHead)).bindingDomain!
        withLocalDeclD `rate (← mkForallFVars #[i] rateType) fun rate => do
          let rowWithRate := mkApp rowHead (mkApp rate i)
          let positiveType := (← whnf (← inferType rowWithRate)).bindingDomain!
          withLocalDeclD `hpositive (← mkForallFVars #[i] positiveType) fun hpositive => do
            k (current ++ #[J, rate, hpositive]) i J rate hpositive

/-- The raw and cut families contain exactly the retained kernels, not newly
selected kernels with merely matching norm estimates. -/
elab "cache_original_scalar_kernel_family_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  let names : Array Name := #[`kernel, `cut_kernel]
  unless index < names.size do throwError "actual scalar event inputs: invalid kernel field"
  withFamily fun params i J rate hpositive => do
    let current := params[:43].toArray
    let value := mkAppN (mkConst (row ++ names[index]!))
      (current ++ #[i, J, mkApp rate i, mkApp hpositive i])
    discard <| store (ns ++ names[index]!) params (← mkLambdaFVars #[i] value)

private def withAdmittedFamily
    (k : Array Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withFamily fun params i J rate hpositive => do
    let rowArgs := params[:43].toArray ++ #[i, J, mkApp rate i, mkApp hpositive i]
    let proof := mkAppN (mkConst (row ++ `sharp_bound)) rowArgs
    let admissionType := (← whnf (← inferType proof)).bindingDomain!
    let common := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalMargins.ε)
      params[:22].toArray
    let commonAdmission ← forallBoundedTelescope admissionType (some 2) fun labels bound => do
      unless labels.size == 2 && bound.isAppOfArity ``LE.le 4 do
        throwError "actual scalar event inputs: expected color/band rate admission"
      mkForallFVars labels (mkAppN bound.getAppFn (bound.getAppArgs.set! 3 common))
    withLocalDeclD `hrate (← mkForallFVars #[i] commonAdmission) fun hrate => do
      let rowAdmission ← forallBoundedTelescope admissionType (some 2) fun labels _ => do
        let caps := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalMargins.ε_caps)
          (params[:22].toArray.push i)
        let hcommon := mkAppN hrate (#[i] ++ labels)
        mkLambdaFVars labels (← mkAppM `le_trans #[hcommon, Expr.proj ``And 0 caps])
      k (params.push hrate) i (rowArgs.push rowAdmission)

/-- Use the finite prehistory sum as the sharp constant for every original row. -/
elab "cache_original_scalar_family_cut_sharp" : command =>
    liftTermElabM <| withTransparency .reducible do
  withAdmittedFamily fun params i rowArgs => do
    let current := params[:43].toArray
    let budget := current[:26].toArray ++ current[27:37].toArray
    let sharp := mkAppN (mkConst (row ++ `sharp_bound)) rowArgs
    forallBoundedTelescope (← inferType sharp) (some 3) fun labels _ => do
      unless labels.size == 3 do throwError "actual scalar event inputs: missing refined/color/carrier labels"
      let hrow := mkAppN sharp labels
      let hconstant := mkAppN (mkConst (ns ++ `Csharp_le)) (budget.push i)
      let hrad ← mkAppM `le_of_lt
        #[← mkAppM `JanetCartan.RawInputPartition.refinedRadius_pos #[labels[0]!]]
      let hmul ← mkAppM `mul_le_mul_of_nonneg_right #[hconstant, hrad]
      let result ← mkAppM `le_trans #[hrow, hmul]
      let type ← inferType result
      let some oldCut := type.find? (·.isAppOfArity `JanetCartan.PhysicalSampling.scalarCarrierCutKernel 7)
        | throwError "actual scalar event inputs: sharp bound lost literal carrier cut"
      let cut := mkAppN (mkConst (ns ++ `cut_kernel)) (params[:46].toArray.push i)
      let type := type.replace fun e => if e == oldCut then some cut else none
      discard <| store (ns ++ `cut_sharp_bound) params (← mkLambdaFVars (#[i] ++ labels) result)
        (some (← mkForallFVars (#[i] ++ labels) type))

/-- The actual original weights and window give the summed cut-mean bound. -/
elab "cache_original_scalar_family_cut_mean" : command =>
    liftTermElabM <| withTransparency .reducible do
  withAdmittedFamily fun params i rowArgs => do
    let current := params[:43].toArray
    let fixed := current[:22].toArray
    let budget := current[:26].toArray ++ current[27:37].toArray
    let p := current[2]!
    withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0, p]) fun hp => do
      withLocalDeclD `h (mkConst `Real) fun h => do
        let realZero ← mkNumeral (mkConst `Real) 0
        withLocalDeclD `hh (← mkAppM ``Ne #[h, realZero]) fun hh => do
          let B := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.B) fixed
          let w := mkApp (mkConst `JanetCartan.PhysicalSampling.OriginalWindow.window) p
          let hpatch := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.patchBounds)
            (fixed.push i)
          let hwindow ← mkAppM `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[hp]
          let hwc := mkApp (mkConst `JanetCartan.PhysicalSampling.OriginalWindow.window_continuous) p
          let proof := mkAppN (mkConst (row ++ `mean_bound))
            (rowArgs ++ #[B, h, w, hpatch, hwindow, hwc, hh])
          let type ← inferType proof
          unless type.isAppOfArity ``LE.le 4 do
            throwError "actual scalar event inputs: expected actual patch-mean inequality"
          let some oldCut := type.find? (·.isAppOfArity `JanetCartan.PhysicalSampling.scalarCarrierCutKernel 7)
            | throwError "actual scalar event inputs: mean bound lost literal carrier cut"
          let cut := mkAppN (mkConst (ns ++ `cut_kernel)) (params[:46].toArray.push i)
          let type := type.replace fun e => if e == oldCut then some cut else none
          let proof := mkApp2 (mkConst ``id [.zero]) type proof
          let means ← mkLambdaFVars #[i] type.getAppArgs[2]!.appArg!
          let univ ← mkAppOptM `Finset.univ #[some (← inferType i), none]
          let member ← mkAppM `Finset.mem_univ #[i]
          let sumBound ← withLocalDeclD `hi (← inferType member) fun hi => do
            mkAppM `Finset.sum_le_sum #[← mkLambdaFVars #[i, hi] proof]
          let normBound ← mkAppM `norm_sum_le #[univ, means]
          let result ← mkAppM `le_trans #[normBound, sumBound]
          let resultType ← inferType result
          let total := mkAppN (mkConst (ns ++ `Cmean)) budget
          let resultType := mkAppN resultType.getAppFn (resultType.getAppArgs.set! 3 total)
          discard <| store (ns ++ `cut_mean_bound) (params ++ #[hp, h, hh]) result (some resultType)

/-- Remove only the existing carrier cutoff on the exact original weight
plateau. Both event inputs still concern the named literal raw scalar family. -/
elab "cache_original_scalar_family_raw_inputs" : command =>
    liftTermElabM <| withTransparency .reducible do
  withAdmittedFamily fun params i rowArgs => do
    let current := params[:43].toArray
    let fixed := current[:22].toArray
    let budget := current[:26].toArray ++ current[27:37].toArray
    let familyParams := params[:46].toArray
    let p := current[2]!
    withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0, p]) fun hp => do
      withLocalDeclD `h (mkConst `Real) fun h => do
        let realZero ← mkNumeral (mkConst `Real) 0
        withLocalDeclD `hh (← mkAppM ``Ne #[h, realZero]) fun hh => do
          let cutInfo ← getConstInfo (row ++ `cut_kernel)
          let some cutBody := cutInfo.value?
            | throwError "actual scalar event inputs: cut-kernel body missing"
          let cut := cutBody.beta rowArgs[:47].toArray
          unless cut.isAppOfArity `JanetCartan.PhysicalSampling.scalarCarrierCutKernel 7 do
            throwError "actual scalar event inputs: not the literal existing carrier cut"
          let cutArgs := cut.getAppArgs
          let β ← mkLambdaFVars #[i] cutArgs[4]!
          let hβ ← mkLambdaFVars #[i] cutArgs[5]!
          let hβone ← mkLambdaFVars #[i] cutArgs[6]!
          let plateau ← mkLambdaFVars #[i]
            (mkAppN (mkConst (row ++ `carrier_plateau)) rowArgs)
          let indexType ← inferType i
          let fintype ← synthInstance (mkApp (mkConst `Fintype [.zero]) indexType)
          let D := mkAppN (mkConst (ns ++ `kernel)) familyParams
          let φ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.φ) fixed
          let B := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.B) fixed
          let w := mkApp (mkConst `JanetCartan.PhysicalSampling.OriginalWindow.window) p
          let Csharp := mkAppN (mkConst (ns ++ `Csharp)) budget
          let Cmean := mkAppN (mkConst (ns ++ `Cmean)) budget
          let sharp := mkAppN (mkConst (ns ++ `cut_sharp_bound)) params
          let mean := mkAppN (mkConst (ns ++ `cut_mean_bound)) (params ++ #[hp, h, hh])
          let result := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.scalar_original_inputs_of_carrier_cut [.zero])
            #[indexType, fintype, cutArgs[0]!, cutArgs[1]!, cutArgs[2]!, D,
              β, hβ, hβone, φ, plateau, B, h, w, Csharp, Cmean, sharp, mean]
          discard <| store (ns ++ `original_inputs) (params ++ #[hp, h, hh]) result

/-- Project the existing exact-kernel support, Fourier coefficient and mask
bounds for every row. No bound is extracted by dividing a measured amplitude. -/
elab "cache_original_scalar_family_amplitude_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  let names : Array Name := #[`amplitude_support, `amplitude_bound, `mask_bound]
  unless index < names.size do throwError "actual scalar event inputs: invalid amplitude field"
  withFamily fun params i J rate hpositive => do
    let rowArgs := params[:43].toArray ++ #[i, J, mkApp rate i, mkApp hpositive i]
    let rawInfo ← getConstInfo (row ++ `kernel)
    let some rawBody := rawInfo.value?
      | throwError "actual scalar event inputs: raw-kernel body missing"
    let raw := rawBody.beta rowArgs
    unless raw.isAppOfArity `JanetCartan.PhysicalSampling.originalScalarKernelData 22 do
      throwError "actual scalar event inputs: raw scalar kernel was changed"
    let bounds := mkAppN
      (mkConst `JanetCartan.PhysicalSampling.originalScalarKernelData_uniform_bounds) raw.getAppArgs
    let proof := match index with
      | 0 => Expr.proj ``And 0 bounds
      | 1 => Expr.proj ``And 0 (Expr.proj ``And 1 bounds)
      | _ => Expr.proj ``And 1 (Expr.proj ``And 1 bounds)
    let type ← inferType proof
    let named := mkAppN (mkConst (ns ++ `kernel)) (params.push i)
    let type := type.replace fun e => if e == raw then some named else none
    discard <| store (ns ++ names[index]!) params (← mkLambdaFVars #[i] proof)
      (some (← mkForallFVars #[i] type))

/-- Reuse the shared native-coordinate identity at the actual original
kernels. In particular the half-frequency weight and full finite-rate phase
are retained; this is not the distinct bare scalar tester. -/
elab "cache_original_scalar_family_native_kernel" : command =>
    liftTermElabM <| withTransparency .reducible do
  withFamily fun params i J rate hpositive => do
    let rowArgs := params[:43].toArray ++ #[i, J, mkApp rate i, mkApp hpositive i]
    let info ← getConstInfo (row ++ `kernel)
    let some body := info.value?
      | throwError "actual scalar native identity: raw-kernel body missing"
    let raw := body.beta rowArgs
    unless raw.isAppOfArity `JanetCartan.PhysicalSampling.originalScalarKernelData 22 do
      throwError "actual scalar native identity: original kernel changed"
    let proof := mkAppN
      (mkConst `JanetCartan.PhysicalForwardMean.originalScalarKernelData_scalarBandKernel_eq)
      raw.getAppArgs
    let type ← inferType proof
    let named := mkAppN (mkConst (ns ++ `kernel)) (params.push i)
    let type := type.replace fun e => if e == raw then some named else none
    discard <| store (ns ++ `scalar_band_kernel_eq) params (← mkLambdaFVars #[i] proof)
      (some (← mkForallFVars #[i] type))

end JanetCartan.PhysicalSampling.OriginalScalarEventInputsApplication
