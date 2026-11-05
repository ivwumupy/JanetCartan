module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawAngularRealization
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawForwardSlice
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawAngularRealization
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-! # Exact raw full-angular forward formula on the actual node spine

Consumer: the BEFORE-B source factorization in main:eq:primary-strain. The
independently proved raw angular Jacobian is specialized to the original
native50/row/color/node. The fixed prefix is moved only from its original
refined input to the original scalar mask. No periodic corrected G identity
or altered input operator is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
open RawInputPartition RawInputRealization PhysicalForwardMean PhysicalSamplingShells
open PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def forwardSum {n N J : ℕ}
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ)
    (A : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (w : RefinedInput n J) (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  ∑ j, (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ (j,η))
    (fun η ↦ m (j,η)*Real.sqrt ‖η‖) (A a c j) x η*w j η) :
      Matrix (Fin N) (Fin n) ℂ) ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ)
private theorem forwardSum_prefix {n N J : ℕ}
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ)
    (A : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (cut : ℕ) (w : RefinedInput n J) (x : Euclidean n) :
    forwardSum φ m A (refinedPrefix n J cut w) x =
      forwardSum φ (prefixMask cut m) A w x := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.1.val < cut
  · simp only [refinedPrefix_apply, hj, ite_true, prefixMask, prefixGate, one_mul]
  · refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (annularMeasure n (refinedRadius j))] with η hη
    ext a c
    simp only [refinedPrefix_apply, hj, ite_false, hη, Pi.zero_apply, mul_zero,
      prefixMask, prefixGate, zero_mul, physicalForwardKernel,
      PhysicalMean.sampledMomentKernel, Complex.ofReal_zero, star_star]
private theorem wide_prefix_eq {n J : ℕ} (cut : ℕ) (w : RefinedInput n J) :
    widePrefix n J cut ((wideRefinement n J).symm w) =
      (wideRefinement n J).symm (refinedPrefix n J cut w) := by
  apply (wideRefinement n J).injective
  rw [wideRefinement_prefix, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]
end JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
end
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
open OriginalRawPrimaryRealizationApplication
private def native := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native
private def actual := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
private def old := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def actualG := `JanetCartan.PhysicalMean.OriginalCanonicalActual.G
private def wideInput (n J w : Expr) := app
  ``PhysicalMean.OriginalMeanQuadraticProfilesTemplate.original_refined_input #[n,J,w]
private def publish (key : Name) (params : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw angular: unresolved field {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual raw angular: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := actual ++ key
  IO.println s!"checking actual raw angular {key}/{params.size}"
  (← IO.getStdout).flush
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Literal BEFORE-B full-angular raw wave and exact original forward annuli on the SAME actual node/source chart; original fixed prefix only, including zero angular labels. The original G body supplies only its input parameter spine, never a derivative value or identity (main:eq:primary-strain)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual raw angular: nonstandard axioms {name}: {axioms}"
  logInfo m!"checked actual raw angular {key}/{params.size}: {axioms}"
private def namedLhs (lhs field : Expr) : MetaM Expr := do
  unless lhs.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw angular: observation changed"
  let a := lhs.getAppArgs
  let phase := a[5]!
  unless phase.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw angular: carrier demodulation changed"
  let b := phase.getAppArgs
  let matrix := b[5]!
  unless (matrix.find? (·.isAppOfArity
      `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix 2)).isSome do
    throwError "actual raw angular: original raw matrix conversion changed"
  let some derivative := matrix.find? (·.isAppOf ``fderiv) |
    throwError "actual raw angular: not the raw differential"
  let d := derivative.getAppArgs
  unless d[d.size-2]!.isAppOf
      `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Whole.full_angular.raw do
    throwError "actual raw angular: derivative is not the same complete raw angular field"
  let namedDerivative := mkAppN derivative.getAppFn (d.set! (d.size-2) field)
  let matrix := matrix.replace fun e => if e == derivative then some namedDerivative else none
  let phase := mkAppN phase.getAppFn (b.set! 5 matrix)
  return mkAppN lhs.getAppFn (a.set! 5 phase)
private def sumData (p : Array Expr) : MetaM (Expr × Expr × Expr × Expr × Expr × Expr) := do
  let ph := app (old ++ `rawPhase) p
  let packed ← bodyAt ph
  unless packed.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12 do
    throwError "actual raw angular: original relative phase changed"
  let J := packed.getAppArgs[1]!
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let N := app `JanetCartan.embeddingDimension #[n]
  let amplitude := app `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardAmplitude p
  let A ← forallBoundedTelescope (← inferType amplitude) (some 2) fun ac _ => do
    withLocalDeclD `j (app `JanetCartan.RawInputPartition.RefinedIndex #[J]) fun j =>
      mkLambdaFVars (ac.push j) (mkAppN amplitude ac)
  return (n,N,J,ph,app (old ++ `rawMask) p,A)
/-- Preserve the original telescope verbatim while substituting only each current
binder domain. This avoids repeatedly expanding the whole remaining native type. -/
private def actualTelescope (type : Expr)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop 53 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE key domain body bi := type.consumeMData |
        throwError "actual raw angular: original53 telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl key bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate key bi domain fun x => loop k body (p.push x)

elab "check_actual_raw_angular " mode:num : command => liftTermElabM do
  actualTelescope (← getConstInfo actualG).type fun p _ => do
    let original ← bodyAt (app actualG p)
    unless original.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G 65 do
      throwError "actual raw angular: original native parameter spine changed"
    let parameter := original.getAppArgs
    let (n,N,J,φ,m,A) ← sumData p
    if mode.getNat == 0 then
      withLocalDeclD `v (app `JanetCartan.RawInputPartition.WideInput #[n,J]) fun v => do
        let value := app `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Whole.full_angular.raw (parameter.push v)
        publish `raw_angular (p.push v) value (← inferType value) true
    else if mode.getNat == 1 || mode.getNat == 4 then
      let producer := app (native ++ `raw_full_forward_on_source) parameter
      forallBoundedTelescope (← inferType producer) (some 3) fun tail _ => do
        unless tail.size == 3 do throwError "actual raw angular: expected input/point/source membership"
        let w := tail[0]!
        let x := tail[1]!
        let proof := mkAppN producer tail
        let target ← inferType proof
        unless target.isAppOfArity ``Eq 3 do throwError "actual raw angular: raw equality changed"
        let lhs ← namedLhs target.getAppArgs[1]! (app (actual ++ `raw_angular) (p.push (wideInput n J w)))
        let rhs := app ``forwardSum #[n,N,J,φ,m,A,w,x]
        let target ← mkEq lhs rhs
        let all := p ++ tail
        if mode.getNat == 1 then
          publish `unprefixed_forward_statement all target (mkSort .zero) true
        else
          publish `unprefixed_forward all proof (app (actual ++ `unprefixed_forward_statement) all)
    else if mode.getNat == 3 then
      withLocalDeclD `v (app `JanetCartan.RawInputPartition.WideInput #[n,J]) fun v => do
        let restricted ← bodyAt (app `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Whole.full_angular_smooth.raw (parameter.push v))
        unless restricted.isAppOfArity ``ContDiffOn.mono 14 do
          throwError "actual raw angular: original source-to-cutoff restriction changed"
        let proof := restricted.getAppArgs[11]!
        let target ← inferType proof
        unless target.isAppOfArity ``ContDiffOn 11 do throwError "actual raw angular: source smoothness changed"
        let target := mkAppN target.getAppFn (target.getAppArgs.set! 9 (app (actual ++ `raw_angular) (p.push v)))
        publish `raw_angular_smooth_on_source (p.push v) proof target
    else if mode.getNat == 2 || mode.getNat == 5 then
      let base := app (actual ++ `unprefixed_forward) p
      withLocalDeclD `cut (mkConst ``Nat) fun cut => do
        forallBoundedTelescope (← inferType base) (some 3) fun tail _ => do
          let w := tail[0]!
          let x := tail[1]!
          let rw := app `JanetCartan.RawInputPartition.refinedPrefix #[n,J,cut,w]
          let initial := mkAppN base (tail.set! 0 rw)
          let hp := app ``forwardSum_prefix #[n,N,J,φ,m,A,cut,w,x]
          let initialType ← bodyAt
            (app (actual ++ `unprefixed_forward_statement) (p ++ tail.set! 0 rw))
          let hpType ← inferType hp
          unless initialType.isAppOfArity ``Eq 3 && hpType.isAppOfArity ``Eq 3 do
            throwError "actual raw angular: original prefix equality changed"
          let ia := initialType.getAppArgs
          let both := mkAppN (mkConst ``Eq.trans initialType.getAppFn.constLevels!)
            #[ia[0]!,ia[1]!,ia[2]!,hpType.getAppArgs[2]!,initial,hp]
          let oldwide := wideInput n J rw
          let goal ← inferType both
          let eq := goal.getAppArgs
          let hwide := app ``wide_prefix_eq #[n,J,cut,w]
          let hwideType ← inferType hwide
          let hwa := hwideType.getAppArgs
          let context ← withLocalDeclD `v (← inferType oldwide) fun v =>
            mkLambdaFVars #[v] (eq[1]!.replace fun e => if e == oldwide then some v else none)
          let transfer ← mkAppM ``congrArg #[context,hwide]
          let proof ← mkAppM ``Eq.trans #[transfer,both]
          unless (← inferType proof).getAppArgs[1]!.find? (· == hwa[1]!) |>.isSome do
            throwError "actual raw angular: original wide prefix was not retained"
          let all := p ++ #[cut] ++ tail
          if mode.getNat == 2 then
            publish `prefixed_forward_statement all (← inferType proof) (mkSort .zero) true
          else
            publish `prefixed_forward all proof (app (actual ++ `prefixed_forward_statement) all)
    else throwError "actual raw angular: unknown stage"
end JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
end
