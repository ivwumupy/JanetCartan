module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSamplingBounds
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
public import JanetCartan.Iteration.PhysicalMean.FixedPicardCoefficientSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Metadata for the exact original Picard precision budgets

The actual low linear coefficient splits as Cnormal=As+At, with As=Cs/gamma
and At=Ct/gamma. We use its genuine weaker omega rate; the sharper upstream
31/640 transport bound is unchanged. The coefficient is EXACTLY
As+At+2*c0*COMMOND_N(m0), and is never replaced by one or hidden in a source
hypothesis. This template chooses only dimension/accuracy numerical orders and defines
publication commands. The coefficient and threshold leaves invoke them in
distinct modules, retaining the SAME names and mathematics.
Consumer: actual full-source finite precision
(`app:ch_mean_pairs:prop:mean-iteration`, `new:eq:source-bound`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped BigOperators
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
/-- Dimension/accuracy-only step count, before every profile coefficient. -/
def precisionSteps (n : ℕ) (accuracy : ℝ) : ℕ :=
  (exists_fixedPicard_coefficient_threshold n accuracy).choose
/-- Dimension/accuracy-only proof-tail order, not an input cutoff change. -/
def precisionTailOrder (n : ℕ) (accuracy : ℝ) : ℕ :=
  (exists_fixedPicard_coefficient_threshold n accuracy).choose_spec.choose
private theorem split_coefficient (Ct Cs gi : ℝ) : (Ct+Cs)*gi = Cs*gi+Ct*gi := by ring
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
open Lean Meta Elab Command
open OriginalCanonicalMomentAdmissionTemplate (withSelectedBefore)
private def root := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def linear := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "exact Picard coefficient: unavailable {key}"
  return (value.beta p).headBeta
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def progress (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "JANET_PICARD_PRECISION_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  progress s!"kernel start {key}/{p.size}"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "exact Picard coefficient: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "exact Picard coefficient: later history/target/sample escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual full-source fixed Picard coefficient: SAME Cnormal=As+At, EXACT Cρ=As+At+2*c0*COMMOND_N(m0), genuine weaker omega rate and retained Cρ^N. All choices precede R0/history/target/sample; no coefficient absorption or analytic success premise (app:ch_mean_pairs:prop:mean-iteration)."
  progress s!"kernel PASS {key}/{p.size}"
  logInfo m!"actual full-source exact precision budget {key}/{p.size}: common D_N and full contraction coefficient retained"

elab "define_original_full_picard_coefficient " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "exact Picard coefficient: unknown split mode"
  withSelectedBefore 44 fun native selected _ => do
    unless selected.size == 33 do throwError "exact Picard coefficient: static33 changed"
    let actual := app (linear ++ `Cnormal) native
    let cost ← bodyAt (linear ++ `Cnormal) native
    unless cost.isAppOfArity ``HMul.hMul 6 do throwError "exact Picard coefficient: Cnormal not original product"
    let sum := cost.getAppArgs[4]!
    let gi := cost.getAppArgs[5]!
    unless sum.isAppOfArity ``HAdd.hAdd 6 && gi.isAppOfArity ``Inv.inv 3 do
      throwError "exact Picard coefficient: original Ct+Cs or reciprocal gamma changed"
    let Ct := sum.getAppArgs[4]!
    let Cs := sum.getAppArgs[5]!
    let gamma := gi.getAppArgs[2]!
    unless gamma.isAppOfArity `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.gamma 21 do
      throwError "exact Picard coefficient: actual current gamma21 changed"
    let hgamma := app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.gamma_pos gamma.getAppArgs
    let As := app (root ++ `As) selected
    let At := app (root ++ `At) selected
    let rawAs ← termWith [(`Cs,Cs),(`gi,gi)] "Cs*gi"
    let rawAt ← termWith [(`Ct,Ct),(`gi,gi)] "Ct*gi"
    if mode.getNat == 0 then save `As selected rawAs (mkConst ``Real) true
    else if mode.getNat == 1 then
      let hCs := app (linear ++ `Csample_nonneg) native
      let proof ← termWith [(`hCs,hCs),(`hg,hgamma)] "mul_nonneg hCs (inv_nonneg.mpr hg.le)"
      let target ← termWith [(`A,As)] "(0 : ℝ) ≤ A"
      save `As_nonneg selected proof target
    else if mode.getNat == 2 then save `At selected rawAt (mkConst ``Real) true
    else if mode.getNat == 3 then
      let hCt := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ctransport_nonneg native
      let proof ← termWith [(`hCt,hCt),(`hg,hgamma)] "mul_nonneg hCt (inv_nonneg.mpr hg.le)"
      let target ← termWith [(`A,At)] "(0 : ℝ) ≤ A"
      save `At_nonneg selected proof target
    else
      let proof := app ``split_coefficient #[Ct,Cs,gi]
      let target ← termWith [(`C,actual),(`As,As),(`At,At)] "C = As+At"
      save `Cnormal_eq_As_add_At selected proof target

elab "define_original_full_picard_precision " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "exact Picard coefficient: unknown precision mode"
  withSelectedBefore 44 fun native selected _ => do
    unless selected.size == 33 do throwError "exact Picard coefficient: static33 changed"
    let n := app ``Nat.succ #[native[0]!]
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Real) fun accuracy => do
      let params := selected.push accuracy
      let N := app ``precisionSteps #[n,accuracy]
      let q := app ``precisionTailOrder #[n,accuracy]
      let DN := app (root ++ `D) (selected.push N)
      let m ← termWith [(`n,n)] "n/2+2"
      let c0 := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant native
      let hc0 := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant_nonneg native
      let As := app (root ++ `As) selected
      let At := app (root ++ `At) selected
      let Crho := app (root ++ `Cρ) params
      let rawCrho ← termWith [(`As,As),(`At,At),(`c0,c0),(`D,DN),(`m,m)] "As+At+2*c0*D m"
      if mode.getNat == 0 then
        save `Cρ params rawCrho (mkConst ``Real) true
      else if mode.getNat == 1 then
        let hAs := app (root ++ `As_nonneg) selected
        let hAt := app (root ++ `At_nonneg) selected
        let hD := mkApp (app (root ++ `D_nonneg) (selected.push N)) m
        let proof ← termWith [(`hAs,hAs),(`hAt,hAt),(`hc,hc0),(`hD,hD)]
          "add_nonneg (add_nonneg hAs hAt) (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) hD)"
        let target ← termWith [(`C,Crho)] "(0 : ℝ) ≤ C"
        save `Cρ_nonneg params proof target
      else if mode.getNat == 2 then
        let Cg := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSourceBudget selected
        let CE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh native
        let CQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ native
        let hCg := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSourceBudget_nonneg selected
        let hCE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh_nonneg native
        let hCQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ_nonneg native
        let b := mkApp (app (linear ++ `Ctail) native) q
        let hb := mkApp (app (linear ++ `Ctail_nonneg) native) q
        let hAs := app (root ++ `As_nonneg) selected
        let hAt := app (root ++ `At_nonneg) selected
        let omega ← termWith [] "(1+JanetCartan.samplingSlack-JanetCartan.fineExponent)/4"
        let choice := app `JanetCartan.PhysicalMean.exists_fixedPicard_coefficient_threshold #[n,accuracy]
        let spec ← mkAppM ``Classical.choose_spec #[choice]
        let spec ← mkAppM ``Classical.choose_spec #[spec]
        let numerical := Expr.proj ``And 1 (Expr.proj ``And 1 spec)
        let proof := mkAppN numerical #[Cg,CE,CQ,hCg,hCE,hCQ,b,c0,As,At,omega,hb,hc0,hAs,hAt,
          ← termWith [(`w,omega)] "le_refl w"]
        let threshold := Expr.proj ``And 1 proof
        let target ← termWith [(`n,n),(`accuracy,accuracy),(`Cg,Cg),(`CE,CE),(`CQ,CQ),
            (`b,b),(`c0,c0),(`As,As),(`At,At),(`w,omega),(`D,DN),(`m,m),(`C,Crho),(`N,N),(`q,q)]
          ("∃ S : ℝ, 2 ≤ S ∧ ∀ R : ℝ, S ≤ R → " ++
            "((As*R^(-w)+At*R^(-w))+2*c0*D m*R^(-JanetCartan.separationExponent) ≤ C*R^(-w)) ∧ " ++
            "C*R^(-w) ≤ 1 ∧ " ++
            "(2*JanetCartan.fourierInterpolationConstant n 1 m*" ++
            "JanetCartan.PhysicalMean.finiteSourceResidualConstantWithCoefficient Cg CE CQ b C m q N)*" ++
            "R^(-JanetCartan.separationExponent)*Real.sqrt (R^(-w*(N : ℝ))+(R/R^JanetCartan.fineExponent)^q) ≤ R^(-accuracy)")
        save `exists_precision_threshold params threshold target
      else
        let ex := app (root ++ `exists_precision_threshold) params
        let rawS ← mkAppM ``Classical.choose #[ex]
        let S := app (root ++ `Sprecision) params
        if mode.getNat == 3 then
          save `Sprecision params rawS (mkConst ``Real) true
        else
          let proof ← mkAppM ``Classical.choose_spec #[ex]
          let target := (← inferType proof).replace fun e => if e == rawS then some S else none
          save `Sprecision_spec params proof target
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

