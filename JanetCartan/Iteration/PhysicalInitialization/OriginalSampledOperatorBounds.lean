module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalWordOrdinary
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.LowBounds
public meta import Lean

/-!
# Uniform low bounds for the original measured signed residual

The original algebraic box and normal bound are fixed before the history.
For the literal order-one phase, endpoint and retarded operator of each actual
current, bound both the paired and separately reflected residual letters
(including the elliptic letter), with the outer χ₂ and inner χ₃ unchanged.
These are the whole-factor bounds in the finite-power observed-chain estimate
`app:ch_regular:lem:finite-chain`, not singleton-history operator norms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
namespace JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds
private theorem open_physical (n : ℕ) (r : ℝ) : IsOpen (ball (0 : Euclidean n) r) := isOpen_ball
private theorem nonneg_of_ge_one {I : Type} (D : I → ℕ → ℝ) (h : ∀ p k, 1 ≤ D p k) :
    ∀ p k, 0 ≤ D p k := fun p k ↦ zero_le_one.trans (h p k)
end JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def self := `JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def pdo := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
private def sym := `JanetCartan.PhysicalPrimary.OriginalRetardedSymbols
private def app (k : Name) (a : Array Expr) := mkAppN (mkConst k) a
private def first (h : Expr) (i : Nat) : Expr := match i with
  | 0 => .proj ``And 0 h
  | i+1 => first (.proj ``And 1 h) i
private def byName (k : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec opts : Expr → Array (Option Expr)
    | .forallE n _ body _ => #[((known.find? (·.1 == n)).map (·.2))] ++ opts body
    | .mdata _ e => opts e
    | _ => #[]
  let options := opts (← getConstInfo k).type
  unless (options.filter Option.isSome).size == known.size do throwError "changed binder names for {k}"
  mkAppOptM k options

run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `f)).type (some 23) fun s _ => do
    let get (k : Name) := app (reg ++ k) s
    let d := s[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let hn := s[1]!
    let ordinary := #[n] ++ s[1:21].toArray
    let protectedAt (k : Name) := app (`JanetCartan.PhysicalInitialization.OriginalProtected ++ k) ordinary
    let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,ordinary[20]!]
    let seed := ordinary.set! 20 cap
    let μ := app `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure seed
    let hμ := app `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure seed
    let screened := app (reg ++ `screenedRadius) #[n,hn,protectedAt `r,μ]
    let hp := app (reg ++ `screened_pos) #[n,hn,protectedAt `r,μ,protectedAt `fact2,hμ]
    let core := app (reg ++ `core_spec) #[n,hn,screened,hp]
    let hΩ := app ``open_physical #[n,app `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,hn]]
    let f := get `f
    let fa := (← inferType f).getAppArgs
    let a (k : Name) := app (pdo ++ `Algebraic ++ k) s
    let Mpos := a `fact2
    let hMalg ← forallBoundedTelescope (← inferType Mpos) (some 1) fun p _ => do mkLambdaFVars p (← mkAppM ``le_of_lt #[mkAppN Mpos p])
    let I := (← inferType (get `Dpdo)).bindingDomain!
    let hD := app ``nonneg_of_ge_one #[I,get `Dpdo,get `fact30]
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
    let src := `JanetCartan.RegularSector.FiniteResidual.FiniteIdentity.exists_selectedFullPairedResidualTerm_uniform_low_constants_with_signed
    let info ← getConstInfo src
    let domains : Array (Name × Expr) := #[(`d,d),(`Ω,fa[1]!),(`x,fa[2]!),(`RQ,fa[3]!),(`A₀,fa[4]!),(`K,fa[5]!),(`M,fa[6]!)]
    let args ← forallBoundedTelescope info.type (some 7) fun p _ => p.mapM fun v => do
      let name := (← v.fvarId!.getDecl).userName
      let some (_,arg) := domains.find? (·.1 == name) | throwError "unexpected fixed physical parameter {name}"
      return arg
    let raw := app src (args ++ #[f,protectedAt `fact14,hΩ,first core 2,← mkAppM ``le_of_lt #[get `fact0],
      get `Rbox,a `Rbox,a `Mbound,mkApp (get `base) one,get `Dpdo,hMalg,hD])
    let data ← store (self ++ `exists_fixed_bounds) s raw
    select (self ++ `Low) s data

run_cmd liftTermElabM <| withTransparency .reducible do
  let current := reg ++ `Current
  forallBoundedTelescope (← getConstInfo (current ++ `projected)).type (some 38) fun w _ => do
    let fixed := w[:23].toArray
    let stat (k : Name) := app (reg ++ k) fixed
    let cur (k : Name) := app (current ++ k) w
    let mask (k : Name) := app (`JanetCartan.PhysicalPrimary.OriginalSourceMasks ++ k) fixed
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let Ω := fa[1]!
    let KQ ← mkAppM `Metric.closedBall #[fa[2]!,fa[3]!]
    let hKQ ← mkAppM `ProperSpace.isCompact_closedBall #[fa[2]!,fa[3]!]
    let low := mkAppN (cur `fact2) #[KQ,hKQ]
    let hl ← mkAppM `JanetCartan.PhysicalPrimary.OriginalWordOrdinary.algebraic_low_bounds
      #[KQ,cur `Q,cur `B,first low 0,first low 1]
    let hQ ← byName `ContDiff.contDiffOn #[(`s,Ω),(`h,cur `hQ)]
    let hB ← byName `ContDiff.contDiffOn #[(`s,Ω),(`h,cur `hB)]
    let hmap ← mkAppM `Set.MapsTo.mono_left #[cur `fact0,← mkAppM `Set.subset_univ #[Ω]]
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
    let endpoint := app (sym ++ `endpoint_native) w
    let retarded := app (sym ++ `physical_residual_retarded_bounds) w
    forallBoundedTelescope (← inferType endpoint) (some 1) fun p _ => do
      let Ψ ← mkLambdaFVars p (← inferType (mkAppN retarded p)).getAppArgs[7]!
      let alg := app (pdo ++ `algebraic_bounds) (w ++ p ++ #[one])
      let hnormal ← mkLambdaFVars p (.proj ``And 0 alg)
      let hs₂ := mask `χ₂_smooth
      let hs₃ := mask `χ₃_smooth
      let χ₂ := (← inferType hs₂).appArg!
      let χ₃ := (← inferType hs₃).appArg!
      let h := app (self ++ `Low.continuation) (fixed ++ #[stat `L,stat `hL,stat `output,cur `ho,cur `hob,
        stat `fact20,cur `hib,cur `Q,cur `B,hQ,hB,hmap,.proj ``And 0 hl,.proj ``And 1 hl,
        cur `W₁,mkApp (cur `Op) one,Ψ,stat `χout,stat `χsource,stat `hs,stat `Dgain,stat `Gain,
        mkApp (stat `cost) one,endpoint,retarded,hnormal,χ₂,χ₃,← mkAppM `ContDiff.continuous #[hs₂],
        ← mkAppM `ContDiff.continuous #[hs₃],← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[stat `χ₂],
        ← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[stat `χ₃]])
      discard <| store (self ++ `actual_low_bounds) w h
end JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds
end
