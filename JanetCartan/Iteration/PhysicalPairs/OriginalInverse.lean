module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedCorrectedExpansion
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# The measured signed-product inverse of the original physical history

Use the EXISTING original38 real corrected source, smooth solver, order-zero
retarded operator, and all-order tame bound. Its raw correction is proved equal
to the measured inverse composed with the original χ₂. The one smooth corrector
is drawn from the original inverse's own `fact17`, before any tensor source,
shift, signed pair, or output order. It represents that same operator, not a
second choice of inverse. These are the `htame`/`hZcorr`/`hsolverAe` fields of
`exists_original_physical_directOffSelf_size_constants` and the input of the
same-source strain transfer (`app:ch_regular:thm:exact-correction`,
`app:ch_pairs:eq:pairs-lag-sum-size`, `main:prop:pairs`).
-/

public meta section
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalInverse
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def here := `JanetCartan.PhysicalPairs.OriginalInverse
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def cur := reg ++ `Current
private def fdi := `JanetCartan.FixedDomainInverse
private def part (v : Expr) : Nat → Expr
  | 0 => .proj ``And 0 v
  | k+1 => part (.proj ``And 1 v) k
private partial def eraseLets (e : Expr) : Expr :=
  match e.headBeta with
  | .letE _ _ v b _ => eraseLets (b.instantiate1 v)
  | body => body
private def keep (name : Name) (p : Array Expr) (v : Expr) (isDef := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let v ← store (here ++ name) p v isDef expected
  addDocStringCore (here ++ name) "The actual same-current measured correction, normalized smooth representation and all-order paired-solver bounds used by the original signed Schwartz product (main:prop:pairs; app:ch_regular:thm:exact-correction)."
  return v

/-- Rewrite the specific native lemma through the proved OPERATOR equality,
without replacing a solution, choosing a new datum or weakening its estimate. -/
private def transportCorrection (p : Array Expr) (name : Name) (proof corr equality : Expr) : MetaM Unit := do
  let nativeType ← inferType proof
  let chosen := (nativeType.find? fun e => e.isAppOfArity (cur ++ `Corr) 38).orElse fun _ =>
    nativeType.find? fun e => e.isAppOf (fdi ++ `correctedSource) && e.getAppNumArgs ≥ 12
  let some old := chosen | throwError "actual product inverse: missing literal corrected source in {name}"
  let motive ← withLocalDeclD `correction (← inferType corr) fun op =>
    mkLambdaFVars #[op] (nativeType.replace fun e => if e == old then some op else none)
  let cast ← mkAppM ``congrArg #[motive,equality]
  let target := nativeType.replace fun e => if e == old then some corr else none
  discard <| keep name p (← mkAppM ``Eq.mp #[cast,proof]) false (some target)

run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (cur ++ `normalized_solver)).type (some 38) fun p _ => do
    unless p.size == 38 do throwError "actual product inverse: original38 required"
    let fixed := p[:23].toArray
    let now (k : Name) := mkAppN (mkConst (cur ++ k)) p
    let stat (k : Name) := mkAppN (mkConst (reg ++ k)) fixed
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let fix := #[n] ++ p[1:21].toArray
    let hK := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.fact14) fix
    let fin2 := mkApp (mkConst ``Fin) (mkNatLit 2)
    let one ← mkNumeral fin2 1
    let some rv := (← getConstInfo (cur ++ `R)).value? (allowOpaque := true)
      | throwError "original product inverse: missing raw physical residual"
    let raw := rv.beta p
    unless raw.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
      throwError "original product inverse: wrong native residual compression"
    let hW := raw.getAppArgs[3]!
    let eq ← mkAppM `JanetCartan.SignedProductEstimates.normalized_correctedSource_eq_measured_inverse
      #[stat `f,hK,stat `L,now `Q,now `B,stat `output,now `ho,now `hob,
        now `W₁,mkApp (now `retarded) one,hW,stat `hrU,stat `hUW,now `hmem,
        stat `hbudget,now `hbound,stat `χ₂,stat `χ₃,stat `fact42]
    let t := eraseLets (← inferType eq)
    unless t.isAppOfArity ``Eq 3 do throwError "original product inverse: lost measured-correction equality"
    let corr ← keep `Corr p t.getAppArgs[2]! true
    let same ← keep `correction_eq p eq false (some (← mkEq (now `Corr) corr))
    transportCorrection p `response_tame (now `fact15) corr same
    let ex := now `fact17
    let hEx ← inferType ex
    unless hEx.isAppOfArity ``Exists 2 do throwError "original product inverse: missing actual smooth corrector witness"
    let z ← keep `Zcorr p (← mkAppM ``Classical.choose #[ex]) true
    let zspec ← keep `corrector_spec p (← mkAppM ``Classical.choose_spec #[ex]) false (some (hEx.getAppArgs[1]!.beta #[z]))
    let zAE ← forallBoundedTelescope (← inferType zspec) (some 1) fun u _ => do
      mkLambdaFVars u (part (mkAppN zspec u) 4)
    transportCorrection p `corrector_ae zAE corr same
    let original := now `fact20
    let smooth ← forallBoundedTelescope (← inferType original) (some 1) fun u _ =>
      mkLambdaFVars u (.proj ``And 0 (mkAppN original u))
    discard <| keep `solver_smooth p smooth
    let ae ← forallBoundedTelescope (← inferType original) (some 1) fun u _ =>
      mkLambdaFVars u (.proj ``And 1 (mkAppN original u))
    let physName := `JanetCartan.RegularSector.NormalizedSolver.realSolver
    let some phys := (← inferType ae).find? (fun e => e.isAppOf physName && e.getAppNumArgs ≥ 12)
      | throwError "original product inverse: missing actual retarded zero solver"
    discard <| keep `Pphys p phys true
    transportCorrection p `solver_ae ae corr same
  logInfo "original38 measured signed correction: same real inverse/χ₂, native smooth corrector and solver on all admitted smooth tensors, all-order true paired-solver tame estimate before samples"
end JanetCartan.PhysicalPairs.OriginalInverse
end
