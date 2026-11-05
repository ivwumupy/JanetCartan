module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingProfile
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMass
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourcePicardPrecision
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Genuine all-order Picard profile for the original complete forcing

The actual full g, SAME high E, and SAME balanced Q estimates instantiate the
finite Picard induction at ONE J=cutoffCount K, selected staticPrefix N. Original101
supplies both gamma and R90 guards. Only the numerical initial auxiliary reach
remains explicit. No source, Picard, quadratic, linear or mass success premise
is quantified. The genuine unweighted mass is Cmass44*D_N(n+1)*h, with the
COMMON D_N=Σj≤N P_j fixed staticPrefix history. There is no K-to-R substitution.
Consumer: physical synthesis, true-R full-self bounds and finite precision
(`new:eq:source-bound`, `app:ch_mean_pairs:prop:mean-iteration`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
private theorem common_profile_bound (v A D h R : ℝ) (s r : ℕ)
    (hh : 0 ≤ h) (hR : 0 ≤ R) (hAD : A ≤ D)
    (hv : v ≤ A*h*R^(s-r)) : v ≤ D*h*R^(s-r) :=
  hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAD hh) (pow_nonneg hR _))
private theorem mass_from_low_profile (n : ℕ) (mass v CM DN h R : ℝ)
    (hCM : 0 ≤ CM) (hmass : mass ≤ CM*v)
    (hprofile : v ≤ DN*h*R^((n+1)-RevisedScales.sourceOrder n)) : mass ≤ (CM*DN)*h := by
  have hq : n+1 ≤ RevisedScales.sourceOrder n := by
    unfold RevisedScales.sourceOrder RevisedScales.baselineOrder
    omega
  rw [Nat.sub_eq_zero_of_le hq, pow_zero, mul_one] at hprofile
  exact (hmass.trans (mul_le_mul_of_nonneg_left hprofile hCM)).trans_eq (by ring)
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
open Lean Meta Elab Command
open OriginalCanonicalMomentAdmissionTemplate (withSelectedAtPoint)
open OriginalCanonicalPicardApplication (applyKnownUntil)
private def root := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual full-source Picard: unavailable {key}"
  return (value.beta p).headBeta
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def tail (e : Expr) (k : Nat) : Expr := Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k
private def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0 (tail e k)
private def save (key : Name) (p : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual full-source Picard: missing {missing.toList}"
    for old in #[source ++ `iterate,source ++ `selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then throwError "actual full-source Picard: background-only run escaped"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full-source Picard: source/estimate/numeric guard escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Genuine all-q bound on the SAME actual complete-forcing Picard source at ONE fixed J=cutoffCount K. Actual fullg/E/Q producers and original101 numeric admission; only initial auxiliary reach is numeric. Common D_N=Σj≤N P_j and M_N=Cmass44*D_N(n+1) precede history; no source/iteration success premise (new:eq:source-bound)."
  logInfo m!"actual full-source Picard {key}/{p.size}: all analytic primitives supplied, SAME fixed J and full g"

/-- Retain selected39 plus exactly the existing target13 DATA, and the SAME
high E's literal fixed prefix. No second sample, inverse or target is chosen. -/
private def withFullData
    (next : Array Expr → Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withSelectedAtPoint fun all chosen point => do
    unless all.size == 53 && chosen.size == 42 && point.size == 47 do
      throwError "actual full-source Picard: original selected admission changed"
    let native := all[:50].toArray
    let high := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.high_error
      (native ++ #[point[27]!,point[39]!])
    let some linear := (← inferType high).find? (·.isAppOfArity (source ++ `linear) 52)
      | throwError "actual full-source Picard: actual high E lost its fixed prefix"
    let L := linear.getAppArgs[51]!
    unless L.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 && !L.hasLooseBVars do
      throwError "actual full-source Picard: not the SAME pre-iteration full cutoff"
    let target := app (forcing ++ `scaled_measured_target) native
    forallBoundedTelescope (← inferType target) (some 13) fun data _ => do
      unless data.size == 13 do throwError "actual full-source Picard: target DATA boundary changed"
      let selected := chosen[:39].toArray ++ data
      next native selected point high L

elab "prove_actual_full_source_picard " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "actual full-source Picard: unknown publication mode"
  withFullData fun native selected point high L => do
    withTransparency .default do
      forallBoundedTelescope (← inferType high) (some 1) fun numeric _ => do
        unless numeric.size == 1 do throwError "actual full-source Picard: initial auxiliary reach boundary changed"
        let hAux := numeric[0]!
        let fixed := native[:44].toArray
        let staticPrefix := selected[:33].toArray
        let Cg := app (forcing ++ `selectedFullSourceBudget) staticPrefix
        let CE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh fixed
        let CQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ fixed
        let hCg := app (forcing ++ `selectedFullSourceBudget_nonneg) staticPrefix
        let hCE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh_nonneg fixed
        let hCQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ_nonneg fixed
        let full := app (forcing ++ `selectedFullSource) selected
        let hInitial ← mkAppM ``le_trans
          #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,native[45]!]
        let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,native[46]!]
        let n := app ``Nat.succ #[native[0]!]
        let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
        let T := app `JanetCartan.currentCoefficientScale #[native[44]!,native[46]!]
        let hh := part facts 3
        let h := (← inferType hh).getAppArgs[3]!
        let hRzero ← termWith [(`hR,part facts 0)] "le_trans (show (0 : ℝ) ≤ 1 by norm_num) hR"
        withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
          let stage := selected ++ #[hAux,N]
          let P := app `JanetCartan.PhysicalMean.sourceIterateProfile #[Cg,CE,CQ,N]
          let D := app (root ++ `D) (staticPrefix.push N)
          if mode.getNat == 0 then
            let run := app (source ++ `selected_iterateWithForcing) (native ++ #[L,full,N])
            let raw ← bodyAt (source ++ `selected_iterateWithForcing) (native ++ #[L,full,N])
            unless raw.isAppOfArity `JanetCartan.PhysicalMean.sourceIterate 7 do
              throwError "actual full-source Picard: literal full-source run changed"
            let a := raw.getAppArgs
            let quadraticUniversal := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.source_profile
              (native ++ #[point[27]!,point[39]!,L])
            let quadratic ← forallBoundedTelescope (← inferType quadraticUniversal) (some 2) fun A _ => do
              unless A.size == 2 do throwError "actual full-source Picard: balanced quadratic budget boundary changed"
              mkLambdaFVars A (mkAppN quadraticUniversal
                (A ++ #[R,h,part facts 0,part facts 2,hh]))
            let known := #[(`Y,a[0]!),(`originalAddCommGroup,a[1]!),(`originalModule,a[2]!),
              (`p,app `JanetCartan.PhysicalMean.residualSobolevSeminorm #[n]),
              (`Cg,Cg),(`CE,CE),(`CQ,CQ),(`hCg,hCg),(`hCE,hCE),(`hCQ,hCQ),
              (`E,a[3]!),(`Q,a[4]!),(`g,full),(`s₀,app `JanetCartan.RevisedScales.sourceOrder #[n]),
              (`T,T),(`R,R),(`h,h),(`hT,part facts 1),(`hR,part facts 0),(`hTR,part facts 2),
              (`hh,hh),(`hh1,part facts 4),(`hg,app (forcing ++ `selected_full_source_profile) selected),
              (`hlinear,mkApp high hAux),(`hquadratic,quadratic)]
            let name := `JanetCartan.PhysicalMean.sourceIterate_seminorm_profile
            let stem := mkConst name [.zero]
            applyKnownUntil `hquadratic stem (← inferType stem) known #[] fun proof extras => do
              unless extras.isEmpty do throwError "actual full-source Picard: an analytic primitive remained"
              withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
                let value := mkAppN proof #[N,q]
                let rawP := app `JanetCartan.PhysicalMean.sourceIterateProfile #[Cg,CE,CQ,N]
                let target := (← inferType value).replace fun e => if e == raw then some run else if e == rawP then some P else none
                unless (target.find? (· == run)).isSome && (target.find? (· == P)).isSome do
                  throwError "actual full-source Picard: SAME named run or static P_N disappeared"
                save `actual_iterate_profile (stage.push q) value target
          else if mode.getNat == 1 then
            withLocalDeclNoLocalInstanceUpdate `j .default (mkConst ``Nat) fun j => do
              let gate ← mkAppM ``LE.le #[j,N]
              withLocalDeclNoLocalInstanceUpdate `hj .default gate fun hj => do
                withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
                  let profile := app (root ++ `iterate_profile) (selected ++ #[hAux,j,q])
                  let bound ← inferType profile
                  let v := bound.getAppArgs[2]!
                  let A := mkApp (app (root ++ `P) (staticPrefix.push j)) q
                  let hAD := app (root ++ `P_le_D) (staticPrefix ++ #[N,j,hj,q])
                  let proof := app ``common_profile_bound
                    #[v,A,mkApp D q,h,R,q,app `JanetCartan.RevisedScales.sourceOrder #[n],hh,hRzero,hAD,profile]
                  save `iterate_profile_uniform (stage ++ #[j,hj,q]) proof (← inferType proof)
          else
            let run := app (source ++ `selected_iterateWithForcing) (native ++ #[L,full,N])
            let massArgs := native ++ #[point[27]!,point[39]!,L,run]
            let stem := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.fourierMass_le massArgs
            forallBoundedTelescope (← inferType stem) (some 1) fun index _ => do
              unless index.size == 1 do throwError "actual full-source Picard: original mass sample boundary changed"
              let hmass := mkAppN stem index
              let actualMass ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.fourierMass_statement (massArgs ++ index)
              unless actualMass.isAppOfArity ``LE.le 4 do throwError "actual full-source Picard: unweighted input mass inequality changed"
              let cm := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.Cmass fixed
              let hcm := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.Cmass_nonneg fixed
              let q := app ``Nat.succ #[n]
              let profile := app (root ++ `iterate_profile_uniform)
                (selected ++ #[hAux,N,N,← mkAppM ``le_refl #[N],q])
              let v := (← inferType profile).getAppArgs[2]!
              let proof := app ``mass_from_low_profile
                #[n,actualMass.getAppArgs[2]!,v,cm,mkApp D q,h,R,hcm,hmass,profile]
              let cost ← termWith [(`CM,cm),(`D,D),(`q,q)] "CM * D q"
              let target := (← inferType proof).replace fun e => if e == cost then some (app (root ++ `M) (staticPrefix.push N)) else none
              unless (target.find? (·.isAppOf (root ++ `M))).isSome do
                throwError "actual full-source Picard: common prehistory M_N disappeared"
              save `input_fourierMass_le (stage ++ index) proof target
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

prove_actual_full_source_picard 0

public meta section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
open Lean Meta Elab Command
run_elab do
  let actual := root ++ `actual_iterate_profile
  forallBoundedTelescope (← getConstInfo actual).type (some 55) fun p target => do
    unless p.size == 55 do throwError "actual full-source Picard: accepted all-q profile55 changed"
    let some rawP := target.find? (·.isAppOfArity `JanetCartan.PhysicalMean.sourceIterateProfile 4)
      | throwError "actual full-source Picard: actual P_N budget not retained"
    let P := app (root ++ `P) (p[:33].toArray.push p[53]!)
    let expected := target.replace fun e => if e == rawP then some P else none
    save `iterate_profile p (app actual p) expected
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

prove_actual_full_source_picard 1
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.actual_iterate_profile
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.iterate_profile
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.iterate_profile_uniform
