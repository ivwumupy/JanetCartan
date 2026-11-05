module

public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeights
public import JanetCartan.Iteration.PhysicalSampling.OriginalWindow
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Geometry
public meta import Lean

/-!
# Deterministic quadrature of the actual exterior weights

The unscaled positive baseline uses the original protected exterior cutoff,
not the smaller incidence/carrier weight. Apply the existing deterministic
quadrature theorem to that actual cutoff and the ONE original window. This
holds at every admissible shift, including the scalar/measured event's shift;
no transfer by a vanishing inner mask is made. A concrete background integrand
must still supply its own regularity and derivative bounds
(`app:ch_waves:eq:background-quadrature`, `app:ch_background:eq:bg-affine-mean`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalOuterQuadratureApplication
open Lean Meta Elab Command

elab "apply_original_outer_background_quadrature" : command => liftTermElabM <| withTransparency .default do
  let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
  forallBoundedTelescope (← getConstInfo (outer ++ `B)).type (some 22) fun x _ => do
    unless x.size == 22 do throwError "outer quadrature: expected original22 geometry"
    let B := mkAppN (mkConst (outer ++ `B)) x
    let ψ := mkAppN (mkConst (outer ++ `ψ)) x
    let hψ := mkAppN (mkConst (outer ++ `patchBounds)) x
    let I := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.Index) x
    let fi ← synthInstance (← mkAppM ``Fintype #[I])
    let one ← mkNumeral (mkConst ``Real) 1
    let P ← withLocalDeclD `i I fun i => mkLambdaFVars #[i] one
    withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0,x[2]!]) fun hp => do
      let win (q : Name) := mkConst (`JanetCartan.PhysicalSampling.OriginalWindow ++ q)
      let args : Array (Option Expr) := #[some I,some (mkConst ``Real),some fi,none,none,none,
        some (win `mollifier),some (win `compact),some (win `smooth),some (win `mass),
        some (win `nonneg),some (win `support),some x[2]!,some hp,some ψ,some B,some P,some hψ]
      let result ← mkAppOptM `JanetCartan.Sampling.Realization.norm_familyBackgroundError_le args
      let type ← instantiateMVars (← mkForallFVars (x.push hp) (← inferType result))
      let value ← instantiateMVars (← mkLambdaFVars (x.push hp) result)
      if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
          type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
        throwError "outer quadrature: unresolved sample, profile or geometry input"
      addDecl (.thmDecl {name := outer ++ `quadrature,levelParams := [],type,value}) (forceExpose := true)

end JanetCartan.PhysicalSampling.OriginalOuterQuadratureApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
apply_original_outer_background_quadrature
