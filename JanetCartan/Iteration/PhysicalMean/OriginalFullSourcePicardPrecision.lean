module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecisionBudgets
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingProfile
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles
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
# Actual finite Picard precision for the original complete source

The SAME full g, original E and balanced Q instantiate the already-proved
fixed-cutoff recurrence and interpolation. Both source tails are retained.
The common D_N is the finite SUM of individual P_j, and Cρ^N is never dropped.
As and At are the actual static coefficients; rho=omega=3/512 is an honest
weaker transport rate, not a coefficient-one contraction or a new sampler.
N and the proof-tail order depend only on dimension/accuracy. J=cutoffCount K
is fixed for the entire run and does not change with N. The source auxiliary
reach concerns INITIAL R0; Sprecision is reached at the CURRENT stage R.
The two public guards are numerical, never a successful-source hypothesis.
Consumer: Step5 of app:ch_mean_pairs:prop:mean-iteration, new:eq:source-bound.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
private theorem exact_omega_rate :
    (1+samplingSlack-fineExponent)/4 = (3/512 : ℝ) := by
  norm_num [samplingSlack, fineExponent, meanSlack]

private theorem rewrite_low_linear (v u tail C As At R : ℝ)
    (hC : C = As+At)
    (h : v ≤ (C*R^(-(3/512 : ℝ)))*u+tail) :
    v ≤ (As*R^(-((1+samplingSlack-fineExponent)/4))+
      At*R^(-((1+samplingSlack-fineExponent)/4)))*u+tail := by
  rw [exact_omega_rate, ← add_mul, ← hC]
  exact h

private theorem residual_low_coefficient (v a c Dm h C R ω Cg tail : ℝ) (N : ℕ)
    (hR : 0 < R) (ha : 0 ≤ a) (hc : 0 ≤ c) (hD : 0 ≤ Dm)
    (hh : 0 ≤ h) (hCg : 0 ≤ Cg)
    (hscaled : a+2*c*Dm*h ≤ C*R^(-ω))
    (hlow : v ≤ (a+2*c*Dm*h)^N*Cg*h+tail) :
    v ≤ C^N*R^(-ω*(N : ℝ))*Cg*h+tail := by
  have hbase : 0 ≤ a+2*c*Dm*h := add_nonneg ha
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) hD) hh)
  have hpow : (R^(-ω))^N = R^(-ω*(N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  have hp : (a+2*c*Dm*h)^N ≤ C^N*R^(-ω*(N : ℝ)) :=
    (pow_le_pow_left₀ hbase hscaled N).trans_eq (by rw [mul_pow,hpow])
  exact hlow.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hCg) hh) le_rfl)

private theorem numerical_associate (A C h d ε : ℝ)
    (hnumeric : (A*C)*h*d ≤ ε) : A*(C*h*d) ≤ ε := by
  simpa only [mul_assoc] using hnumeric
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
private def linear := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual full-source precision: unavailable {key}"
  return (value.beta p).headBeta
private def typeAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for x in p do
    let .forallE _ _ body _ := type.consumeMData
      | throwError "actual full-source precision: telescope changed at {key}"
    type := body.instantiate1 x
  return type
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def tail (e : Expr) (k : Nat) : Expr :=
  Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k
private def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0 (tail e k)
private def save (key : Name) (p : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual full-source precision: missing {missing.toList}"
    for old in #[source ++ `iterate,source ++ `selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then throwError "actual full-source precision: background-only source escaped"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full-source precision: unresolved analytic/numeric field in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  addDecl (.thmDecl {name := root ++ key,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore (root ++ key)
    "Actual complete-forcing finite Picard precision for the SAME original E/Q/global inverse/ONE sample and full cutoff J, all analytic primitives applied. Accuracy and static coefficient budgets precede history; only initial auxiliary and current-stage precision reaches remain numerical. Cρ^N and both low tails are retained (app:ch_mean_pairs:prop:mean-iteration)."
  logInfo m!"actual full-source precision {key}/{p.size}: FULLg52, SAME fixed J, original LOW/HIGH applied; no analytic premise"

/-- Open only the existing selected source DATA and actual88 high interface. -/
private def withFullData
    (next : Array Expr → Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withSelectedAtPoint fun all chosen point => do
    unless all.size == 53 && chosen.size == 42 && point.size == 47 do
      throwError "actual full-source precision: selected admission boundary changed"
    let native := all[:50].toArray
    let high := app (linear ++ `high_error) (native ++ #[point[27]!,point[39]!])
    let some E := (← inferType high).find? (·.isAppOfArity (source ++ `linear) 52)
      | throwError "actual full-source precision: high E lost its original full prefix"
    let J := E.getAppArgs[51]!
    unless J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 && !J.hasLooseBVars do
      throwError "actual full-source precision: cutoff is not fixed before Picard N"
    let target := app (forcing ++ `scaled_measured_target) native
    forallBoundedTelescope (← inferType target) (some 13) fun data _ => do
      unless data.size == 13 do throwError "actual full-source precision: target DATA boundary changed"
      next native (chosen[:39].toArray ++ data) point high J

elab "prove_original_full_picard_precision " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "actual full-source precision: unknown mode"
  withFullData fun native selected point high J => do
    withTransparency .default do
      let fixed := native[:44].toArray
      let staticPrefix := selected[:33].toArray
      let n := app ``Nat.succ #[native[0]!]
      let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
      let T := app `JanetCartan.currentCoefficientScale #[native[44]!,native[46]!]
      let K := J.getAppArgs[0]!
      let full := app (forcing ++ `selectedFullSource) selected
      withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Real) fun accuracy => do
        let staticPrecision := staticPrefix.push accuracy
        let N := app (root ++ `precisionSteps) #[n,accuracy]
        let q := app (root ++ `precisionTailOrder) #[n,accuracy]
        let Crho := app (root ++ `Cρ) staticPrecision
        let spec := app (root ++ `Sprecision_spec) staticPrecision
        let numerical := mkApp (Expr.proj ``And 1 spec) R
        forallBoundedTelescope (← inferType high) (some 1) fun aux _ => do
          unless aux.size == 1 do throwError "actual full-source precision: initial auxiliary guard changed"
          let hAux := aux[0]!
          forallBoundedTelescope (← inferType numerical) (some 1) fun reach _ => do
            unless reach.size == 1 do throwError "actual full-source precision: stage precision reach changed"
            let numeric := mkApp numerical reach[0]!
            let hscaled := part numeric 0
            let hsmall := part numeric 1
            let hprecision := tail numeric 2
            let params := staticPrecision ++ selected[33:].toArray ++ #[hAux,reach[0]!]
            let residual := app (source ++ `selected_residualWithForcing) (native ++ #[J,full,N])
            if mode.getNat == 2 then
              let middle := app (root ++ `residual_middle) params
              let middleType ← inferType middle
              unless middleType.isAppOfArity ``LE.le 4 do
                throwError "actual full-source precision: actual middle bound disappeared"
              let M := middleType.getAppArgs[3]!
              let eps := (← inferType hprecision).getAppArgs[3]!
              let args := #[n,residual,M,eps,middle]
              let helperType ← typeAt ``originalFixedForcing_cNorm_of_middle args
              let .forallE _ domain result _ := helperType.consumeMData
                | throwError "actual full-source precision: C1 numeric boundary changed"
              let product := domain.getAppArgs[2]!
              let A := product.getAppArgs[4]!
              unless M.isAppOfArity ``HMul.hMul 6 && M.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 do
                throwError "actual full-source precision: middle coefficient/envelope/root shape changed"
              let hnumeric := app ``numerical_associate
                #[A,M.getAppArgs[4]!.getAppArgs[4]!,M.getAppArgs[4]!.getAppArgs[5]!,M.getAppArgs[5]!,eps,hprecision]
              let proof := mkApp (app ``originalFixedForcing_cNorm_of_middle args) hnumeric
              save `residual_cNorm params proof (result.instantiate1 hnumeric)
            else
              let Cg := app (forcing ++ `selectedFullSourceBudget) staticPrefix
              let CE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh fixed
              let CQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ fixed
              let hCg := app (forcing ++ `selectedFullSourceBudget_nonneg) staticPrefix
              let hCE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh_nonneg fixed
              let hCQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ_nonneg fixed
              let D := app (root ++ `D) (staticPrefix.push N)
              let c0 := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant fixed
              let hc0 := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant_nonneg fixed
              let b := mkApp (app (linear ++ `Ctail) fixed) q
              let hb := mkApp (app (linear ++ `Ctail_nonneg) fixed) q
              let As := app (root ++ `As) staticPrefix
              let At := app (root ++ `At) staticPrefix
              let omega ← termWith [] "(1+JanetCartan.samplingSlack-JanetCartan.fineExponent)/4"
              let a ← termWith [(`As,As),(`At,At),(`R,R),(`w,omega)] "As*R^(-w)+At*R^(-w)"
              let hInitial ← mkAppM ``le_trans
                #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,native[45]!]
              let facts ← mkAppM ``fixedPicard_history_scale_facts #[hInitial,native[46]!]
              let hh := part facts 3
              let h := (← inferType hh).getAppArgs[3]!
              let hRzero ← termWith [(`hR,part facts 0)] "le_trans (show (0 : ℝ) ≤ 1 by norm_num) hR"
              let hRpos ← termWith [(`hR,part facts 0)] "lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hR"
              let ha ← termWith [(`hR,hRzero),(`w,omega),
                  (`hAs,app (root ++ `As_nonneg) staticPrefix),(`hAt,app (root ++ `At_nonneg) staticPrefix)]
                "add_nonneg (mul_nonneg hAs (Real.rpow_nonneg hR (-w))) (mul_nonneg hAt (Real.rpow_nonneg hR (-w)))"
              let m := app `JanetCartan.RevisedScales.baselineOrder #[n]
              let s0 := app `JanetCartan.RevisedScales.sourceOrder #[n]
              let hm ← if mode.getNat == 0 then
                  termWith [(`n,n)] "((by change n/2+2 ≤ 2*(n/2+2); omega) : JanetCartan.RevisedScales.baselineOrder n ≤ JanetCartan.RevisedScales.sourceOrder n)"
                else pure (app ``Nat.succ_pos #[app ``Nat.succ #[app ``Nat.div #[n,mkNatLit 2]]])
              let raw ← bodyAt (source ++ `selected_iterateWithForcing) (native ++ #[J,full,N])
              unless raw.isAppOfArity ``sourceIterate 7 do throwError "actual full-source precision: SAME run body changed"
              let runArgs := raw.getAppArgs
              let qbody ← bodyAt (source ++ `quadratic) runArgs[4]!.getAppArgs
              unless qbody.isAppOf ``fixedSourceQuadratic do throwError "actual full-source precision: original Q changed"
              let commInfo ← getConstInfo ``fixedSourceQuadratic_comm
              let hQ := mkAppN (mkConst ``fixedSourceQuadratic_comm (commInfo.levelParams.map (fun _ => .zero))) qbody.getAppArgs
              let quadraticUniversal := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.source_profile
                (native ++ #[point[27]!,point[39]!,J])
              let quadratic ← forallBoundedTelescope (← inferType quadraticUniversal) (some 2) fun A _ => do
                unless A.size == 2 do throwError "actual full-source precision: balanced Q profile boundary changed"
                mkLambdaFVars A (mkAppN quadraticUniversal (A ++ #[R,h,part facts 0,part facts 2,hh]))
              let low51 := app (linear ++ `low_error) (native.push q)
              let low ← forallBoundedTelescope (← inferType low51) (some 1) fun u _ => do
                unless u.size == 1 do throwError "actual full-source precision: actual low source boundary changed"
                let actualLow := mkApp low51 u[0]!
                let lowType ← inferType actualLow
                let rhs := lowType.getAppArgs[3]!
                unless rhs.isAppOfArity ``HAdd.hAdd 6 && rhs.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 do
                  throwError "actual full-source precision: BOTH exact low terms changed"
                let proof := app ``rewrite_low_linear #[lowType.getAppArgs[2]!,rhs.getAppArgs[4]!.getAppArgs[5]!,
                  rhs.getAppArgs[5]!,app (linear ++ `Cnormal) fixed,As,At,R,
                  app (root ++ `Cnormal_eq_As_add_At) staticPrefix,actualLow]
                mkLambdaFVars u proof
              let known := #[(`n,n),(`Y,runArgs[0]!),(`originalAddCommGroup,runArgs[1]!),(`originalModule,runArgs[2]!),
                (`p,app ``residualSobolevSeminorm #[n]),(`Cg,Cg),(`CE,CE),(`CQ,CQ),(`hCg,hCg),(`hCE,hCE),(`hCQ,hCQ),
                (`E,runArgs[3]!),(`Q,runArgs[4]!),(`hQ,hQ),(`g,full),(`s₀,s0),(`m₀,m),(`hm₀,hm),(`q,q),(`N,N),(`J,N),
                (`T,T),(`R,R),(`K,K),(`h,h),(`a,a),(`b,b),(`c₀,c0),(`ω,omega),(`Cρ,Crho),
                (`hT,part facts 1),(`hR,part facts 0),(`hTR,part facts 2),(`hK,tail facts 5),(`hh,hh),(`hh1,part facts 4),
                (`ha,ha),(`hb,hb),(`hc₀,hc0),(`hCρ,app (root ++ `Cρ_nonneg) staticPrecision),
                (`hg,app (forcing ++ `selected_full_source_profile) selected),(`hlinear,mkApp high hAux),(`hquadratic,quadratic),
                (`hlowLinear,low),(`hlowQuadratic,app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.low_bound
                  (native ++ #[point[27]!,point[39]!,J]))]
              let producer := if mode.getNat == 0 then ``sourceResidual_fixedCutoff_seminorm_le
                else ``sourceResidual_fixedCutoff_middle_le_with_coefficient
              let info ← getConstInfo producer
              let start := mkConst producer (info.levelParams.map (fun _ => .zero))
              applyKnownUntil `hlowQuadratic start (← inferType start) known #[] fun primitive extras => do
                unless extras.isEmpty do
                  throwError "actual full-source precision: unfilled primitive {← extras.mapM fun x => return (← getFVarLocalDecl x).userName}"
                let proof ← if mode.getNat == 0 then do
                    let hContract ← termWith [(`hs,hscaled),(`hsmall,hsmall)] "le_trans hs hsmall"
                    let low := mkApp primitive hContract
                    let lowType ← inferType low
                    let rhs := lowType.getAppArgs[3]!
                    let hDm := mkApp (app (root ++ `D_nonneg) (staticPrefix.push N)) m
                    pure (app ``residual_low_coefficient #[lowType.getAppArgs[2]!,a,c0,mkApp D m,h,Crho,R,omega,
                      mkApp Cg (mkNatLit 0),rhs.getAppArgs[5]!,N,hRpos,ha,hc0,hDm,hh,mkApp hCg (mkNatLit 0),hscaled,low])
                  else pure (mkAppN primitive #[hscaled,hsmall])
                let proofType ← inferType proof
                let target ← if mode.getNat == 0 then do
                    let v := proofType.getAppArgs[2]!.replace fun e =>
                      if e.isAppOfArity ``sourceResidual 7 then some residual else none
                    termWith [(`v,v),(`C,Crho),(`N,N),(`R,R),(`w,omega),(`Cg,Cg),(`h,h),(`b,b),(`D,D),(`q,q),(`K,K)]
                      "v ≤ C^N*R^(-w*(N : ℝ))*Cg 0*h+2*(N : ℝ)*b*(D q+D 0)*h*(R/K)^q"
                  else pure (proofType.replace fun e =>
                    if e.isAppOfArity ``sourceResidual 7 then some residual else none)
                unless target.getUsedConstants.contains (source ++ `selected_residualWithForcing) &&
                    target.getUsedConstants.contains (root ++ `Cρ) do
                  throwError "actual full-source precision: actual residual or full coefficient lost"
                save (if mode.getNat == 0 then `residual_low else `residual_middle) params proof target
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

prove_original_full_picard_precision 0
prove_original_full_picard_precision 1
prove_original_full_picard_precision 2

#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.residual_low
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.residual_middle
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.residual_cNorm
