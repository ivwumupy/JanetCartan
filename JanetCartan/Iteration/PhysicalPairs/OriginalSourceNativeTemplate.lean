module
public import JanetCartan.Iteration.PhysicalMean.CanonicalPhysicalIdentity
public import JanetCartan.Iteration.PhysicalMean.IndividualPhysicalProfile
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
/-! # Consume the single actual primitive tuple for the physical source field

The identity uses real A, whole Gprefix and their exact An/hArep/hG bridge.
The physical profile uses complex An, the full matrix amplitude, and the SAME
already-prefixed mask. No factory, sample, detector normalization or inverse is
reconstructed. Only the supplied source's genuine profile remains an input;
its selected complete-forcing producer is the source iteration, not a mass or
Fourier-support bound (`main:eq:mean-final-amplitude`, `main:prop:current-waves`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate
open RawInputPartition
/-- The literal row restriction of the same joint raw phase. -/
theorem curried_original_phase {n J : ℕ} {ν : Type} [MetricSpace ν]
    (φ : ((ν × RefinedIndex J) × Euclidean (n-1)) → Euclidean n → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (i : ν) :
    Continuous (Function.uncurry (fun z : RefinedIndex J × Euclidean (n-1) => φ ((i,z.1),z.2))) :=
  hφ.comp (((continuous_const.prodMk continuous_fst.fst).prodMk continuous_fst.snd).prodMk continuous_snd)

/-- Restrict the already-prefixed full mask, without adding another prefix. -/
theorem curried_original_mask {n J : ℕ} {ν : Type} [MetricSpace ν]
    (m : ((ν × RefinedIndex J) × Euclidean (n-1)) → ℝ)
    (hm : Continuous m) (i : ν) :
    Continuous (fun z : RefinedIndex J × Euclidean (n-1) => m ((i,z.1),z.2)) :=
  hm.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)

/-- Compactness of the same mask row follows by the original projection. -/
theorem curried_original_mask_compact {n J : ℕ} {ν : Type} [MetricSpace ν]
    (m : ((ν × RefinedIndex J) × Euclidean (n-1)) → ℝ)
    (hms : HasCompactSupport m) (i : ν) :
    HasCompactSupport (fun z : RefinedIndex J × Euclidean (n-1) => m ((i,z.1),z.2)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hms.image (continuous_fst.snd.prodMk continuous_snd))
  intro z hz
  exact ⟨((i,z.1),z.2), subset_tsupport m hz, rfl⟩

/-- Whole forward-amplitude continuity for a fixed original sample, with no
sample weight or detector normalization. -/
theorem curried_original_amplitude {n N J : ℕ} {ν : Type}
    (amp : Fin N → Fin n → ν × RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (hamp : ∀ a c j, ContDiff ℝ ∞ (Function.uncurry (amp a c j))) (i : ν) :
    ∀ a c, Continuous (fun z : (RefinedIndex J × Euclidean (n-1)) × Euclidean n =>
      amp a c (i,z.1.1) z.1.2 z.2) := by
  intro a c
  have hc : Continuous (fun z : RefinedIndex J × (Euclidean (n-1) × Euclidean n) =>
      amp a c (i,z.1) z.2.1 z.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun j => (hamp a c (i,j)).continuous)
  exact hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
end JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate
open Lean Meta Elab Command
open PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSourceNative
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def put (fields : Array (Name × Expr)) (key : Name) (value : Expr) :=
  (fields.filter (fun p => p.1 != key)).push (key,value)
private def save (key : Name) (params : Array Expr) (value : Expr) (data : Bool)
    (target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual native source: unresolved {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual native source: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"actual native source: kernel passed {name}"

/-- Only currying/restriction of the actual joint tuple, exactly as in
`CanonicalQuadraticProfile`; the whole forward and operator identities are
passed unchanged. Stop before the legitimate source/point/sample DATA. -/
def identityPrefix (original : Array (Name × Expr)) : MetaM (Expr × Array (Name × Expr)) := do
  let key := `JanetCartan.PhysicalMean.fixedSourceDerivative_eq_individualNativeField
  let info ← getConstInfo key
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut proof := mkConst key levels
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  let mut fields := original
  let conversions : Array (Name × String) := #[
    (`φ,"(fun i z => φ ((i,z.1),z.2))"),
    (`m,"(fun i z => m ((i,z.1),z.2))"),
    (`amp,"(fun i a c j => amp a c (i,j))"),
    (`hampK,"(fun i a c j η => hampK a c (i,j) η)")]
  let helpers : Array (Name × Name) := #[
    (`hφ,``curried_original_phase), (`hm,``curried_original_mask),
    (`hms,``curried_original_mask_compact), (`hamp,``curried_original_amplitude)]
  while type.isForall do
    let .forallE binder domain body bi := type | throwError "actual native source: malformed identity telescope"
    let field := binderKey binder domain bi
    if field == `u then return (proof,fields)
    let value ← match helpers.find? (fun p => p.1 == field) with
      | some (_,helper) => applyFields helper original (some `i)
      | none => match conversions.find? (fun p => p.1 == field) with
        | some (_,code) => termWith original.toList code (some domain)
        | none => getField original field
    proof := mkApp proof value
    type := body.instantiate1 value
    fields := put fields field value
  throwError "actual native source: missing source DATA in original identity consumer"

/-- Parameters are the frozen89 native50 + moment guard + reach guard + prefix,
not86's source53. The source/torus/sample binders remain inside the exact Prop. -/
def publishIdentity (params : Array Expr) (fields : Array (Name × Expr)) (mode : Nat) : MetaM Unit := do
  unless params.size == 53 && mode < 2 do throwError "actual native source: changed identity ABI"
  let (proof,_) ← identityPrefix fields
  let target ← inferType proof
  if mode == 0 then save `identity_statement params target true (mkSort .zero)
  else save `canonical_derivative_eq_native params proof false (app (ns ++ `identity_statement) params)

/-- Consume the literal individual Cnorm theorem at the actual row. Its
`A=An i`, `G=amp_i`, `hG=hamp_i`; these keys are intentionally DIFFERENT from
the canonical/native identity dictionary. The only analytic input is the
supplied source's true Sobolev profile through s+n+2. -/
partial def publishSourceProfile (params : Array Expr)
    (original : Array (Name × Expr)) (mode : Nat) : MetaM Unit := do
  unless params.size == 53 && mode < 2 do throwError "actual native source: changed source-profile ABI"
  let common ← withInverseBudget params original
  let fixed ← budgetPrefix params common
  let (_,curried) ← identityPrefix common
  let n ← getField common `n
  let ν ← getField common `ν
  let residualType ← mkAppM ``CoeSort.coe #[app `JanetCartan.CurrentMean.SmoothResidual #[n]]
  withLocalDeclD `u residualType fun u => do
    withLocalDeclD `i ν fun i => do
      let e ← mkAppM ``DFunLike.coe #[app `JanetCartan.CurrentMean.smoothResidualToL2 #[n],u]
      let mut known := common ++ #[(`u,u),(`e,e)]
      for (key,source) in #[(`φ,`φ),(`m,`m),(`G,`amp),(`hφ,`hφ),(`hm,`hm),(`hms,`hms),(`hGK,`hampK)] do
        known := put known key (mkApp (← getField curried source) i)
      for (key,source) in #[(`A,`An),(`hA,`hAn),(`Tbare,`Tbare),(`hTbare,`hTbare),(`hTbareBound,`hTbareBound)] do
        known := put known key (mkApp (← getField common source) i)
      let conversions : Array (Name × String) := #[
        (`Φ,"(fun j => Φ (i,j))"), (`a,"(fun a j => ameas a (i,j))"), (`L,"(fun j => L (i,j))"),
        (`hφs,"(fun z => hφs ((i,z.1),z.2))"), (`hΦ,"(fun j => hΦ (i,j))"),
        (`hG,"(fun a c j => hamp a c (i,j))"), (`ha,"(fun a j => ha a (i,j))"),
        (`hL,"(fun j v => hL (i,j) v)"), (`hhigh,"(fun z => hhigh ((i,z.1),z.2))"),
        (`haK,"(fun a j η => haK a (i,j) η)"), (`hagree,"(fun z => hagree ((i,z.1),z.2))"),
        (`hphase,"(fun z => hphase ((i,z.1),z.2))"), (`hGj,"(fun a c j η => hGj a c (i,j) η)"),
        (`hΦj,"(fun j η => hΦj (i,j) η)"), (`haj,"(fun a j η => haj a (i,j) η)"),
        (`hLj,"(fun j η => hLj (i,j) η)")]
      let allowed := #[`s,`M,`hM,`R,`h,`hR,`hTR,`hh,`hsource]
      let consumer := `JanetCartan.PhysicalMean.individualNativeInverseField_cNorm_source_profile
      let info ← getConstInfo consumer
      let levels := info.levelParams.map (fun _ => Level.zero)
      let literal := mkConst consumer levels
      let rec go (type : Expr) (args : Array Expr) (known : Array (Name × Expr))
          (bound : Array Expr) : MetaM Unit := do
        match type with
        | .forallE binder domain body bi =>
          let field := binderKey binder domain bi
          if field == `hreg || field == `hinverse then
            let all ← sourceTail params known (field == `hreg)
            let proof ← if field == `hreg then pure all else
              forallBoundedTelescope domain (some 2) fun xs _ => do
                unless xs.size == 2 do throwError "actual native source: changed finite inverse-order boundary"
                mkLambdaFVars xs (mkApp all xs[0]!)
            go (body.instantiate1 proof) (args.push proof) (put known field proof) bound
          else if allowed.contains field then
            if known.any (fun p => p.1 == field) then
              throwError "actual native source: producer improperly supplies source input {field}"
            withLocalDeclNoLocalInstanceUpdate binder bi domain fun x =>
              go (body.instantiate1 x) (args.push x) (known.push (field,x)) (bound.push x)
          else
            let value ← match conversions.find? (fun p => p.1 == field) with
              | some (_,code) => termWith ((`i,i) :: common.toList) code (some domain)
              | none => getField known field
            go (body.instantiate1 value) (args.push value) (put known field value) bound
        | target =>
          let some cost := target.find? (·.isAppOf `JanetCartan.PhysicalMean.nativeIndividualPhysicalProfileConstant) |
            throwError "actual native source: lost true R-scale individual profile constant"
          let M ← getField known `M
          let s ← getField known `s
          let closed ← mkLambdaFVars (fixed ++ #[M,s]) cost
          if closed.hasFVar || closed.hasLooseBVars then
            throwError "actual native source: R/history/prefix/sample/source data entered the supposedly static profile constant"
          let all := params ++ #[u,i] ++ bound
          if mode == 0 then save `profile_statement all target true (mkSort .zero)
          else save `source_cNorm_profile all (mkAppN literal args) false (app (ns ++ `profile_statement) all)
      go (info.type.instantiateLevelParams info.levelParams levels) #[] known #[]
end JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate
end
