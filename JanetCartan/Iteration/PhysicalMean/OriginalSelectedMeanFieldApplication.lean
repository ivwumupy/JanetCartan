module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldCurrentTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
public meta import Lean

/-! # Actual full initialized mean application

Every analytic input is read from its named original-data producer. The public
application adds only the genuine auxiliary and initial full-field reach gates;
its source is the same complete-forcing Picard iterate at the same fixed J
(`main:prop:mean`, `new:eq:source-bound`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanFieldApplication
open Lean Meta Elab Command
open OriginalSelectedMeanFieldCurrentTemplate (root app termWith save)
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
private def mean := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def common := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def canonical := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def base := `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles
private def inverse := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
private def bodyAt (name : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "full initialized mean: unavailable producer body {name}"
  return (value.beta p).headBeta
private def tail (e : Expr) (k : Nat) : Expr :=
  Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k
private def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0 (tail e k)

/-- This is metadata, not a new term-level assumption package. -/
structure Actual where
  selected : Array Expr
  native : Array Expr
  native39 : Array Expr
  stage : Array Expr
  early : Array Expr
  N : Expr
  J : Expr
  hAux : Expr
  W : Expr
  raw : Expr
  fields : Expr
  source : Expr
  facts : Expr
  R : Expr
  T : Expr
  h : Expr
  w : Array Expr
  e : Array Expr

private def withActual (next : Actual → MetaM Unit) : MetaM Unit :=
  withActualSelectedFields fun p _ native native39 _ => withTransparency .default do
    let selected := p[:52].toArray
    let N := p[53]!
    let allq := app (common ++ `iterate_profile) selected
    let allqType ← inferType allq
    let some run := allqType.find? (·.isAppOfArity (canonical ++ `selected_iterateWithForcing) 53)
      | throwError "full initialized mean: missing actual full-source run53"
    let J := run.getAppArgs[50]!
    unless !J.hasLooseBVars && J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 do
      throwError "full initialized mean: fixed complete prefix changed"
    forallBoundedTelescope allqType (some 1) fun aux _ => do
      unless aux.size == 1 do throwError "full initialized mean: changed initial auxiliary gate"
      let stage := selected ++ #[J,N]
      let W := app (mean ++ `initializedField) stage
      let Wraw ← bodyAt (mean ++ `initializedField) stage
      unless Wraw.isAppOfArity `JanetCartan.PhysicalBackground.baseVariation 8 do
        throwError "full initialized mean: actual initialized field is not baseVariation8"
      let w := Wraw.getAppArgs
      let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift native
      let E ← bodyAt (canonical ++ `linear) (native ++ #[shift,J])
      unless E.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
        throwError "full initialized mean: same original E28 changed"
      let full := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource selected
      let source := app (canonical ++ `selected_iterateWithForcing) (native ++ #[J,full,N])
      let hInitial ← mkAppM ``le_trans
        #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS native[:44].toArray,native[45]!]
      let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,native[46]!]
      let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
      let T := app `JanetCartan.currentCoefficientScale #[native[44]!,native[46]!]
      let hhType ← inferType (part facts 3)
      let h := hhType.getAppArgs[3]!
      next {
        selected := selected, native := native, native39 := native39, stage := stage
        early := selected[:33].toArray.push N, N := N, J := J, hAux := aux[0]!, W := W
        raw := w[5]!, fields := Wraw, source := source, facts := facts
        R := R, T := T, h := h, w := w, e := E.getAppArgs }

/-- Supply all raw analytic fields from the actual original initializer,
paired global inverse and common all-order Picard profile. -/
def publishRaw : MetaM Unit := withActual fun d => do
  let fixed := d.native[:44].toArray
  let Dinit := app (base ++ `Craw) fixed
  let Cinv := app (inverse ++ `Cinv) fixed
  let M := app (common ++ `D) d.early
  let hDinit := app (base ++ `Craw_nonneg) fixed
  let hCinv := app (inverse ++ `Cinv_nonneg) fixed
  let hM := app (common ++ `D_nonneg) d.early
  let hpair := app (inverse ++ `paired_profile) d.native
  unless d.e[20]!.isAppOfArity `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
    throwError "full initialized mean: changed same positive global inverse39"
  let image := app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.image d.e[20]!.getAppArgs
  let initial := app `JanetCartan.PhysicalBackground.NativeAdmission.raw d.native39
  let hinitial := app (base ++ `raw_mem) d.native
  let hinitialBound := app (base ++ `raw_grade_profile) d.native
  let hreg ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
    mkLambdaFVars #[q] (mkAppN d.e[21]! #[d.source,q])
  let hsource ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
    let hNN := app ``Nat.le_refl #[d.N]
    mkLambdaFVars #[q] (app (common ++ `iterate_profile_uniform)
      (d.selected ++ #[d.hAux,d.N,d.N,hNN,q]))
  let proof := mkAppN (mkConst (root ++ `initialized_raw_profile) [.zero])
    #[d.w[0]!,d.w[2]!,d.w[3]!,Dinit,Cinv,M,hDinit,hCinv,hM,image,d.e[19]!,d.e[15]!,
      d.T,d.R,d.h,part d.facts 1,part d.facts 2,part d.facts 3,part d.facts 4,hpair,
      initial,hinitial,hinitialBound,d.source,hreg,hsource]
  let expected ← termWith [(`n,d.w[0]!),(`iota,d.w[2]!),(`raw,d.raw),
      (`C,app (root ++ `Craw) d.early),(`R,d.R)]
    ("∀ s : ℕ, raw ∈ JanetCartan.CarrierSobolev.augmentedInputLevel n iota s ∧ " ++
     "(JanetCartan.CarrierSobolev.augmentedInputSobolevScale n iota).gradeNorm s raw ≤ C s*R^(s-(1+n))")
  save `initializedRaw_profile (d.selected ++ #[d.hAux,d.N]) (.proj ``And 1 proof) false (some expected)

/-- Apply the already fixed geometric continuation to the actual full raw
field, retaining BOTH the field and its full linearized strain. -/
def publishField : MetaM Unit := withActual fun d => do
  let S := app (root ++ `SfullW) d.native[:44].toArray
  let gate ← termWith [(`S,S),(`R0,d.native[44]!)] "S ≤ R0"
  withLocalDeclNoLocalInstanceUpdate `hFullW .default gate fun hFullW => do
    let hraw := app (root ++ `initializedRaw_profile) (d.selected ++ #[d.hAux,d.N])
    let hreg ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
      mkLambdaFVars #[q] (.proj ``And 0 (mkApp hraw q))
    let hbound ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
      mkLambdaFVars #[q] (.proj ``And 1 (mkApp hraw q))
    let packet := app (root ++ `CW_continuation)
      (d.early ++ #[d.native[44]!,hFullW,d.native[46]!,d.native[47]!,d.native[48]!,d.native[49]!,
        d.raw,hreg,d.R,part d.facts 2,hbound])
    let bound := Expr.proj ``And 1 packet
    let radius := app `JanetCartan.PhysicalSeed.OriginalBoundary.b d.native39[:2].toArray
    let expected ← termWith [(`n,d.w[0]!),(`b,radius),(`W,d.W),(`F,d.w[6]!),
        (`C,app (root ++ `CW) d.early),(`R,d.R)]
      ("∀ s : ℕ, JanetCartan.cNorm (Metric.closedBall (0 : JanetCartan.Euclidean n) b) s W + " ++
       "JanetCartan.cNorm (Metric.closedBall (0 : JanetCartan.Euclidean n) b) s " ++
       "(JanetCartan.linearizedMetric F W) ≤ C s*R^s")
    save `initializedField_strain_profile (d.selected ++ #[d.hAux,d.N,hFullW]) bound false (some expected)
end JanetCartan.PhysicalMean.OriginalSelectedMeanFieldApplication
end
