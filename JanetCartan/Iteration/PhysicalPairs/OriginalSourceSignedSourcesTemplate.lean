module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitude
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedData
/-! # The original measured complete signed sources are unchanged

Retain both original cutoffs: the broad χsrc in the uncut tensor and the
single inner χ₂ of the native measured inverse. Actual amplitude germs on the
whole source chart preserve every χ₂-measured plus and minus tensor, including
all plus diagonals (doubled carriers) and all off-diagonal minus carriers. No
claim is made that the uncut tensors agree outside that chart. Consumers are
the SAME `OriginalSignedData.measured` and measured native correction in
`app:ch_pairs:eq:pairs-exact-offself`, not a new signed ledger or weight.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set
namespace JanetCartan.PhysicalPairs.OriginalSourceSignedSources
/-- Pointwise multiplication by the ORIGINAL inner measurement erases only
values outside its proved source chart; all full signed terms remain. -/
theorem measured_signed_sources_of_eq_on {n N : ℕ} {ι : Type*}
    (χ η : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A B : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (U : Set (Euclidean n)) (hχ : tsupport χ ⊆ U)
    (hAB : ∀ i x, x ∈ U → A i x = B i x) (j k : ι) :
    (fun x ↦ χ x • (η x • ProductSum.plusSource θ A j k x)) =
      (fun x ↦ χ x • (η x • ProductSum.plusSource θ B j k x)) ∧
    (fun x ↦ χ x • (η x • ProductSum.minusSource θ A j k x)) =
      (fun x ↦ χ x • (η x • ProductSum.minusSource θ B j k x)) := by
  constructor <;> funext x
  · by_cases hx : χ x = 0
    · simp only [hx,zero_smul]
    · have hu := hχ (subset_tsupport χ hx)
      simp only [ProductSum.plusSource,hAB j x hu,hAB k x hu]
  · by_cases hx : χ x = 0
    · simp only [hx,zero_smul]
    · have hu := hχ (subset_tsupport χ hx)
      simp only [ProductSum.minusSource,hAB j x hu,hAB k x hu]
end JanetCartan.PhysicalPairs.OriginalSourceSignedSources
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceSignedSourcesTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSourceSignedSources
private def amp := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def remainingType (key : Name) (args : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for v in args do
    unless type.isForall do throwError "actual measured signed source: changed actual source telescope"
    type := type.bindingBody!.instantiate1 v
  return type
private def save (key : Name) (p : Array Expr) (value type : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual measured signed source: unresolved field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual measured signed source: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"actual measured signed source: kernel passed {name}"

elab "publish_original_measured_signed_sources " which:num : command => liftTermElabM do
  unless which.getNat < 3 do throwError "actual measured signed source: unknown publication mode"
  withActualSelectedSourceWave fun p _ _ _ _ _ _ => do
    let i := p[52]!
    let index ← inferType i
    let θ ← mkLambdaFVars #[i] (app (amp ++ `phase) p)
    let A ← mkLambdaFVars #[i] (app (amp ++ `amplitude) p)
    let B ← mkLambdaFVars #[i] (app (amp ++ `rawAmplitude) p)
    let gt ← remainingType `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.germ_statement p
    forallBoundedTelescope gt (some 2) fun point _ => do
      unless point.size == 2 do throwError "actual measured signed source: changed original chart germ"
      let ht ← inferType point[1]!
      unless ht.isAppOfArity ``Membership.mem 5 do throwError "actual measured signed source: lost original source-chart membership"
      let chart := ht.getAppArgs[3]!
      unless chart.isAppOfArity (mask ++ `chart) 23 do throwError "actual measured signed source: original chart23 changed"
      let source := chart.getAppArgs
      let support := app (mask ++ `χ₂_support_chart) source
      let a := (← inferType support).getAppArgs
      let closed := a[a.size-2]!
      unless closed.isAppOf ``tsupport do throwError "actual measured signed source: lost actual inner measurement support"
      let χ := closed.appArg!
      let η := (← inferType (app (mask ++ `χsrc_smooth) source)).appArg!
      for e in #[chart,χ,η] do
        if (e.find? (· == i)).isSome then
          throwError "actual measured signed source: node-dependent cutoff/chart substituted for original common source"
      let actualN ← inferType (app (amp ++ `amplitude) p)
      unless actualN.isForall do throwError "actual measured signed source: changed actual matrix field"
      let matrix := actualN.bindingBody!
      unless matrix.isAppOfArity ``Matrix 3 do throwError "actual measured signed source: changed complete matrix amplitude"
      let N := matrix.getAppArgs[0]!.appArg!
      let dim := matrix.getAppArgs[1]!.appArg!
      let germ := app (amp ++ `germ_on_original_chart) (p ++ point)
      let equality ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[germ]
      let equalOn ← mkLambdaFVars #[i,point[0]!,point[1]!] equality
      withLocalDeclD `k index fun k => do
        let proof := mkAppN (mkConst ``JanetCartan.PhysicalPairs.OriginalSourceSignedSources.measured_signed_sources_of_eq_on [.zero])
          #[dim,N,index,χ,η,θ,A,B,chart,support,equalOn,i,k]
        let type ← inferType proof
        unless type.isAppOfArity ``And 2 do throwError "actual measured signed source: lost both complete signs"
        let plus := type.getAppArgs[0]!.getAppArgs
        let minus := type.getAppArgs[1]!.getAppArgs
        let all := p.push k
        if which.getNat == 0 then save `measuredPlus all plus[1]! plus[0]! true
        else if which.getNat == 1 then save `measuredMinus all minus[1]! minus[0]! true
        else
          let target := app ``And #[← mkEq (app (ns ++ `measuredPlus) all) plus[2]!,
            ← mkEq (app (ns ++ `measuredMinus) all) minus[2]!]
          save `measured_sources_eq all proof target
end JanetCartan.PhysicalPairs.OriginalSourceSignedSourcesTemplate
end
