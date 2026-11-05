module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesApplication
public import JanetCartan.Iteration.PhysicalPrimary.WeightedSynthesis
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalWeights
/-!
# Physical synthesis of the actual original sampled source

Exact conditional deduction for the actual source primary. The sole new
quantitative input is literal mass_i ≤ M*mesh, with M fixed before R/history.
Producer: task14 Cmass44*D_N(n+1), with the genuine full-forcing r_N profile.
This implication does not discharge that producer (`main:eq:primary-fixed-scales`). -/
namespace JanetCartan.PhysicalPrimary.OriginalSourcePhysicalSynthesisApplication
private theorem original_cutoff_closedBall_mem_chart (n : ℕ) (D : LocalDomain)
    (x : Euclidean n)
    (hx : x ∈ Metric.closedBall (0 : Euclidean n) (UniformStep.physicalCutoff (n := n) D).rOut) :
    x ∈ D.chart n := by
  apply (UniformStep.physicalCutoff_properties (n := n) D).2.1
  simpa only [(UniformStep.physicalCutoff (n := n) D).tsupport_eq] using hx
private theorem source_mass_absorption (a c t m M h : ℝ)
    (ha : a ≤ c * t * (1 + m)) (hc : 0 ≤ c * t)
    (hm : m ≤ M * h) (hM : 0 ≤ M) (hh : h ≤ 1) :
    a ≤ (c * (1 + M)) * t := by
  calc
    a ≤ c * t * (1 + m) := ha
    _ ≤ c * t * (1 + M) := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (1 : ℝ)) (hm.trans (mul_le_of_le_one_right hM hh))) hc
    _ = (c * (1 + M)) * t := by ring
end JanetCartan.PhysicalPrimary.OriginalSourcePhysicalSynthesisApplication

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalSourcePhysicalSynthesisApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)
private partial def head (e : Expr) : Expr :=
  match e.headBeta with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | .mdata _ b => head b
  | e => e
private def exactType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := head type | throwError "actual synthesis producer signature changed"
    type := rest.instantiate1 arg
  if type.isAppOf (ns ++ `selectedSourceCombinedWave_mass_statement) ||
      type.isAppOf (ns ++ `selectedSourceCombinedWave_uniform_mass_statement) then
    let info ← getConstInfo type.getAppFn.constName!
    let some body := info.value? (allowOpaque := true) | throwError "missing exact source proposition"
    return head (body.beta type.getAppArgs)
  return head type
private def termWith (vars : List (Name × Expr)) (code : String) (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def applyNext (value type arg : Expr) : MetaM (Expr × Expr) := do
  let .forallE _ _ body _ := head type | throwError "actual synthesis expected next unchanged argument"
  return (mkApp value arg,head (body.instantiate1 arg))
private def instantiateBudget (params s : Array Expr) (D n N M hM : Expr) : MetaM Expr := do
  let rows := s[0]!
  unless rows.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
    throwError "not the original row22"
  let cube ← getConstInfo `JanetCartan.PhysicalSampling.OriginalWeights.exists_cube
  let some body := cube.value? (allowOpaque := true) | throwError "missing original cube"
  let cube := head (body.beta rows.getAppArgs)
  unless cube.isAppOfArity `JanetCartan.PhysicalSampling.exists_finite_original_carrier_weight_bounds 5 do
    throwError "changed original cube signature"
  let finite := cube.getAppArgs[1]!
  unless cube.getAppArgs[0]! == rows do throwError "original finite row type changed"
  let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
  unless s[2]!.isAppOfArity (outer ++ `B) 22 && s[3]!.isAppOfArity (outer ++ `ψ) 22 do
    throwError "actual synthesis lost the outer cube and squared cutoff"
  let p := s[2]!.getAppArgs
  unless p == s[3]!.getAppArgs && p == rows.getAppArgs do throwError "static original sampler changed"
  let hB ← termWith [(`hB,app (outer ++ `hB) p)] "(le_of_lt hB)"
  let hweights := app (outer ++ `patchBounds) p
  let mut positiveOrder : Option Expr := none
  for x in params[:44].toArray do
    let t ← inferType x
    if t.isAppOfArity ``LT.lt 4 && t.getAppArgs[0]! == mkConst ``Nat && t.getAppArgs[3]! == s[1]! then
      if ← isDefEq t.getAppArgs[2]! (mkNatLit 0) then positiveOrder := some x
  let some hp := positiveOrder | throwError "missing original pOrder positivity"
  let hw := app `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[s[1]!,hp]
  let one ← mkNumeral (mkConst ``Real) 1
  let P ← withLocalDeclNoLocalInstanceUpdate `row .default rows fun row => mkLambdaFVars #[row] one
  let C := app (ns ++ `uniformPhysicalCost) params[:44].toArray
  let hC := app (ns ++ `uniformPhysicalCost_nonneg) params[:44].toArray
  let factor ← mkAppM ``HAdd.hAdd #[one,M]
  let Cphys ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
    mkLambdaFVars #[q] (← mkAppM ``HMul.hMul #[mkApp C q,factor])
  let hCphys ← termWith [(`hC,hC),(`hM,hM)] "(fun q => mul_nonneg (hC q) (add_nonneg zero_le_one hM))"
  let result := mkAppN (mkConst
    `JanetCartan.PhysicalPrimary.exists_cutSampledPrimary_physical_profiles_on_original_sample [.zero])
    #[n,N,rows,finite,D,s[1]!,s[2]!,one,hB,P,s[3]!,s[4]!,hw,hweights,Cphys,hCphys]
  let closed ← mkLambdaFVars (params[:44].toArray ++ #[M,hM]) result
  if closed.hasFVar || closed.hasMVar then throwError "physical cost depends on R/history/prefix/source/δ"
  return result

elab "publish_actual_source_physical_synthesis" mode:num : command => liftTermElabM do
  let mode := mode.getNat
  unless mode < 2 do throwError "unknown source synthesis publication mode"
  OriginalSampledPhysicalProfilesQuantitativeTemplate.withActualSelectedSourceWave
    fun params _ _ _ _ _ _ => do
      liftM <| IO.eprintln "actual synthesis: source callback"
      let source := params[:52].toArray
      let index ← inferType params[52]!
      unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
        throwError "source synthesis original sample7 changed"
      let s := index.getAppArgs
      let smooth := app (ns ++ `selectedSourceCombinedWave_smooth) params
      let smType ← exactType smooth
      unless smType.isAppOfArity ``ContDiffOn 11 do throwError "source smoothness changed"
      let chart := smType.getAppArgs[10]!
      unless chart.isAppOfArity `JanetCartan.LocalDomain.chart 2 do throwError "source synthesis lost Dsmooth"
      let D := chart.getAppArgs[0]!
      let n := chart.getAppArgs[1]!
      let V := smType.getAppArgs[5]!
      unless V.isAppOfArity ``EuclideanSpace 2 && V.getAppArgs[1]!.isAppOfArity ``Fin 1 do
        throwError "source synthesis target changed"
      let N := V.getAppArgs[1]!.appArg!
      let Z ← mkLambdaFVars #[params[52]!] (app (ns ++ `selectedSourceCombinedWave) params)
      liftM <| IO.eprintln "actual synthesis: source shape"
      let rates := app `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.stage_rates params[:50].toArray
      let R := (← inferType (part rates 0)).appArg!
      let hLam := part rates 2
      let one ← mkNumeral (mkConst ``Real) 1
      let zero ← mkNumeral (mkConst ``Real) 0
      liftM <| IO.eprintln "actual synthesis: rates read"
      let hS := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS params[:44].toArray
      liftM <| IO.eprintln "actual synthesis: native S read"
      let hR ← termWith [(`R0,params[44]!),(`j,params[46]!),(`hS,hS),(`hR,params[45]!)]
        "(by have h : (1 : ℝ) ≤ R0 := le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_trans hS hR); exact h.trans (JanetCartan.le_historyScale h j))"
        (some (← mkAppM ``LE.le #[one,R]))
      liftM <| IO.eprintln "actual synthesis: current R proved"
      let hh ← termWith [(`hR,hR)]
        "(by exact Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num [JanetCartan.separationExponent]))"
        (some (← mkAppM ``LE.le #[s[5]!,one]))
      liftM <| IO.eprintln "actual synthesis: mesh proved"
      let base := app (ns ++ `selectedSourceCombinedWave_mass_jets) params
      let mass ← forallBoundedTelescope (← exactType base) (some 3) fun point _ => do
        let bound ← exactType (mkAppN base point)
        unless bound.isAppOfArity ``LE.le 4 do throwError "actual source mass bound changed"
        let rhs := bound.getAppArgs[3]!
        unless rhs.isAppOfArity ``HMul.hMul 6 do throwError "actual source mass product changed"
        let total := rhs.getAppArgs[5]!
        unless total.isAppOfArity ``HAdd.hAdd 6 do throwError "actual baseline lost its unscaled one"
        let value := total.getAppArgs[5]!
        let family ← mkLambdaFVars #[params[52]!] value
        let closed ← mkLambdaFVars source family
        if closed.hasFVar then throwError "literal mass depends on physical derivative/point"
        return value
      liftM <| IO.eprintln "actual synthesis: literal mass extracted"
      withLocalDeclNoLocalInstanceUpdate `massCost .default (mkConst ``Real) fun M => do
        withLocalDeclNoLocalInstanceUpdate `massCost_nonneg .default (← mkAppM ``LE.le #[zero,M]) fun hM => do
          liftM <| IO.eprintln "actual synthesis: mass scalar admitted"
          let budget ← instantiateBudget params s D n N M hM
          liftM <| IO.eprintln "actual synthesis: static budget produced"
          let budgetType ← exactType budget
          unless budgetType.isAppOfArity ``Exists 2 do throwError "unchanged synthesis lost prehistory constant"
          let Ctype := budgetType.getAppArgs[0]!
          let predicate := budgetType.getAppArgs[1]!
          let .sort level ← whnf (← inferType Ctype) | throwError "physical coefficient type is not a sort"
          let C := mkAppN (mkConst ``Classical.choose [level]) #[Ctype,predicate,budget]
          let spec := mkAppN (mkConst ``Classical.choose_spec [level]) #[Ctype,predicate,budget]
          let specType := head (predicate.beta #[C])
          unless specType.isAppOfArity ``And 2 do throwError "unchanged synthesis lost positivity/bound pair"
          let hC := Expr.proj ``And 0 spec
          let allBound := Expr.proj ``And 1 spec
          let allBoundType := specType.getAppArgs[1]!
          let massBound ← mkForallFVars #[params[52]!] (← mkAppM ``LE.le #[mass,← mkAppM ``HMul.hMul #[M,s[5]!]])
          liftM <| IO.eprintln "actual synthesis: static cost chosen"
          withLocalDeclNoLocalInstanceUpdate `actualSourceMass .default massBound fun hMass => do
            withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
              withLocalDeclNoLocalInstanceUpdate `δ_nonneg .default (← mkAppM ``LE.le #[zero,δ]) fun hδ => do
                let mut currentValue := allBound
                let mut currentType := allBoundType
                for argument in #[R,δ,hR,hδ,s[6]!,Z] do
                  let result ← applyNext currentValue currentType argument
                  currentValue := result.1
                  currentType := result.2
                let .forallE _ smoothGoal _ _ := head currentType | throwError "missing weighted smoothness input"
                liftM <| IO.eprintln "actual synthesis: actual Z supplied"
                let hZ ← forallBoundedTelescope smoothGoal (some 2) fun i _ => do
                  unless i.size == 2 do throwError "weighted smoothness domain changed"
                  mkLambdaFVars i (app (ns ++ `selectedSourceCombinedWave_smooth) (source.push i[0]!))
                let result ← applyNext currentValue currentType hZ
                currentValue := result.1
                currentType := result.2
                let .forallE _ jetsGoal _ _ := head currentType | throwError "missing physical jet input"
                liftM <| IO.eprintln "actual synthesis: weighted smoothness supplied"
                let jets ← forallBoundedTelescope jetsGoal (some 5) fun point _ => do
                  unless point.size == 5 do throwError "unchanged weighted spatial jet ABI changed"
                  let actual := app (ns ++ `selectedSourceCombinedWave_uniform_mass_jets)
                    (source ++ #[point[0]!,point[2]!,point[3]!])
                  let .forallE _ chartGoal _ _ := head (← exactType actual) |
                    throwError "actual source uniform jet lost chart membership"
                  liftM <| IO.eprintln "actual synthesis: physical jet domain"
                  let hx := app ``original_cutoff_closedBall_mem_chart #[n,D,point[3]!,point[4]!]
                  let hxType ← exactType hx
                  liftM <| IO.eprintln s!"actual synthesis: chart type structural equality {hxType == chartGoal}; heads {hxType.getAppFn.constName?} / {chartGoal.getAppFn.constName?}"
                  if hxType.isAppOfArity ``Membership.mem 5 && chartGoal.isAppOfArity ``Membership.mem 5 then
                    let a := hxType.getAppArgs[4]!
                    let b := chartGoal.getAppArgs[4]!
                    liftM <| IO.eprintln s!"actual synthesis: chart heads {a.getAppFn.constName?} / {b.getAppFn.constName?}; structural equality {a == b}"
                  liftM <| IO.eprintln "actual synthesis: closed ball mapped to source chart"
                  let actual := mkApp actual hx
                  let actualType ← exactType actual
                  let atom := actualType.getAppArgs[3]!.getAppArgs[4]!
                  let hU := app (ns ++ `uniformPhysicalCost_nonneg) (params[:44].toArray.push point[2]!)
                  let hcoeff ← termWith [(`hU,hU),(`hLam,hLam)]
                    "(by exact mul_nonneg hU (Real.rpow_nonneg (le_of_lt hLam) _))"
                    (some (← mkAppM ``LE.le #[zero,atom]))
                  liftM <| IO.eprintln "actual synthesis: uniform coefficient nonnegative"
                  let rhs := actualType.getAppArgs[3]!
                  let total := rhs.getAppArgs[5]!
                  unless atom.isAppOfArity ``HMul.hMul 6 && total.isAppOfArity ``HAdd.hAdd 6 do
                    throwError "literal physical coefficient or one-plus-mass changed"
                  let proof := app ``source_mass_absorption
                    #[actualType.getAppArgs[2]!,atom.getAppArgs[4]!,atom.getAppArgs[5]!,
                      total.getAppArgs[5]!,M,s[5]!,actual,hcoeff,mkApp hMass point[0]!,hM,hh]
                  mkLambdaFVars point proof
                liftM <| IO.eprintln "actual synthesis: actual weighted jets proved"
                let result ← applyNext currentValue currentType jets
                let value := result.1
                let type := result.2
                let some rawP := type.find? (·.isAppOfArity `JanetCartan.PhysicalPrimary.cutSchwartz 5) |
                  throwError "unchanged synthesis lost genuine compact primary"
                let namedP := app (ns ++ `selectedSourcePrimary) (source.push δ)
                let type := type.replace fun e => if e == rawP then some namedP else none
                let tail := params[44:52].toArray ++ #[hMass,δ,hδ]
                let allProof ← mkLambdaFVars tail value
                let allType ← mkForallFVars tail type
                let positiveType := specType.getAppArgs[0]!
                let pair := mkAppN (mkConst ``And.intro) #[positiveType,allType,hC,allProof]
                let pairType := mkApp2 (mkConst ``And) positiveType allType
                let predicate ← withLocalDeclNoLocalInstanceUpdate `C .default Ctype fun c => do
                  mkLambdaFVars #[c] (pairType.replace fun e => if e == C then some c else none)
                let existsType := mkApp2 (mkConst ``Exists [level]) Ctype predicate
                let existsProof := mkAppN (mkConst ``Exists.intro [level]) #[Ctype,predicate,C,pair]
                let fixed := params[:44].toArray ++ #[M,hM]
                let statement := ns ++ `selectedSourcePrimary_physicalProfiles_statement
                let type ← instantiateMVars (← mkForallFVars fixed (if mode == 0 then mkSort .zero else app statement fixed))
                let value ← instantiateMVars (← mkLambdaFVars fixed (if mode == 0 then existsType else existsProof))
                for e in #[type,value] do
                  if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
                    throwError "source synthesis leaked a sample, current stage, or unresolved analytic datum"
                let (type,value) := Lean.ShareCommon.shareCommon (type,value)
                let name := if mode == 0 then statement else ns ++ `selectedSourcePrimary_physicalProfiles_of_mass_bound
                liftM <| IO.eprintln s!"checking actual source physical synthesis mode {mode} / {fixed.size}"
                if mode == 0 then
                  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
                else
                  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
                addDocStringCore name "The genuine selectedSourcePrimary satisfies the unchanged weighted physical Sobolev profiles with a constant chosen before R/history/source/δ, conditional only on literal mass_i ≤ M*mesh. The identified producer is Cmass44*D_N(n+1) from the actual full-forcing Picard profile; this implication does not close that producer (main:eq:primary-fixed-scales)."
                logInfo "Actual source physical synthesis: C before R/history/source/δ; explicit literal mass≤M*mesh premise awaits14 genuine full-source D_N."
end JanetCartan.PhysicalPrimary.OriginalSourcePhysicalSynthesisApplication
end
publish_actual_source_physical_synthesis 0
publish_actual_source_physical_synthesis 1
