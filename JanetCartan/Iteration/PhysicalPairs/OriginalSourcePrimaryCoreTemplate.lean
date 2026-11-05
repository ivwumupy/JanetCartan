module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedCorrection
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageMetric
/-! # The actual aggregate-cutoff primary has the signed primary's core germ

The final P is not replaced by the uncut Schwartz sum. On the ORIGINAL Dsmooth
core only, its already fixed aggregate cutoff is one on a neighborhood. Thus
its metric agrees with the signed-product construction's literal primary. This
closes the pointwise primary join without presupposing a source/profile or
signed response estimate (`main:eq:self-off`, `main:prop:pairs`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore
open UniformStep PhysicalPrimary
/-- Use the existing physical cutoff plateau, not a new cutoff of each wave. -/
theorem aggregate_primary_core_germ {n N : ℕ} {ι : Type*} [Fintype ι]
    (D : LocalDomain) (b : ℝ) (μ : ι → ℝ)
    (W : ι → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (P : Euclidean n → Euclidean N)
    (heq : P = fun x ↦ physicalCutoff D x • sampledPrimary b μ
      (fun i ↦ (W i : Euclidean n → EuclideanSpace ℂ (Fin N))) x)
    (x : Euclidean n) (hx : x ∈ D.core n) :
    P =ᶠ[𝓝 x] (uncutSampledPrimary b μ W : Euclidean n → Euclidean N) := by
  rw [heq,uncutSampledPrimary_coe]
  have hs := (physicalCutoff_properties (n := n) D).2.2.2
  filter_upwards [Metric.isOpen_ball.mem_nhds (hs.1 hx)] with y hy
  rw [hs.2 hy,one_smul]
/-- The pointwise induced metric only sees this already proved core germ. -/
theorem metric_eq_of_germ {n N : ℕ} {P Q : Euclidean n → Euclidean N}
    {x : Euclidean n} (heq : P =ᶠ[𝓝 x] Q) : inducedMetric P x = inducedMetric Q x := by
  have hd : fderiv ℝ P x = fderiv ℝ Q x := heq.fderiv_eq
  change (fun i j ↦ inner ℝ (fderiv ℝ P x (EuclideanSpace.single i 1))
    (fderiv ℝ P x (EuclideanSpace.single j 1))) = _
  rw [hd]
  rfl
end JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore
end
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourcePrimaryCoreTemplate
open Lean Meta Elab Command
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
elab "identify_original_primary_core " which:num : command => liftTermElabM do
  unless which.getNat < 2 do throwError "actual primary core: unknown mode"
  let correction := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
  forallBoundedTelescope (← getConstInfo correction).type (some 55) fun p _ => do
    let original ← body correction p
    unless original.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedSum.correction 47 do
      throwError "actual primary core: SAME signed correction disappeared"
    let sp := original.getAppArgs
    let source := p[:44].toArray ++ p[45:53].toArray ++ #[p[54]!]
    let actual := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary
    let P ← mkAppM ``DFunLike.coe #[app actual source]
    let Q ← mkAppM ``DFunLike.coe #[app `JanetCartan.PhysicalPairs.OriginalStageMetric.primary sp]
    let prim ← body actual source
    unless prim.isAppOfArity `JanetCartan.PhysicalPrimary.cutSampledPrimary 9 do
      throwError "actual primary core: original aggregate cutoff changed"
    let a := prim.getAppArgs
    let domain := app `JanetCartan.LocalDomain.core #[a[4]!,a[0]!]
    withLocalDeclD `x (app `JanetCartan.Euclidean #[a[0]!]) fun x => do
      withLocalDeclD `hx (← mkAppM ``Membership.mem #[domain,x]) fun hx => do
        let all := p ++ #[x,hx]
        let germ := mkAppN (mkConst ``JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore.aggregate_primary_core_germ [.zero])
          #[a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,sp[45]!,P,
            app `JanetCartan.PhysicalPairs.OriginalSourcePrimary.aggregate_primary_eq source,x,hx]
        let gt ← inferType germ
        unless gt.isAppOfArity ``Filter.EventuallyEq 5 do throwError "actual primary core: germ shape changed"
        let target := mkAppN gt.getAppFn (gt.getAppArgs.set! 4 Q)
        let (key,proof,target) ← if which.getNat == 0 then pure (`germ,germ,target) else do
          let same := app `JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore.germ all
          let proof := app ``JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore.metric_eq_of_germ
            #[a[0]!,a[1]!,P,Q,x,same]
          pure (`metric,proof,← inferType proof)
        let type ← instantiateMVars (← mkForallFVars all target)
        let value ← instantiateMVars (← mkLambdaFVars all proof)
        for e in #[type,value] do
          if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
            throwError "actual primary core: unresolved original primary identity"
        let pair := Lean.ShareCommon.shareCommon (type,value)
        let name := `JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore ++ key
        liftM <| IO.eprintln s!"actual primary core: kernel checking {name}"
        addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
        addDocStringCore name "The unchanged final aggregate-cutoff primary and the original signed construction's real Schwartz sum have the SAME germ/metric on the original Dsmooth core, with identical sample and weight (main:eq:self-off, main:prop:pairs)."
        liftM <| IO.eprintln s!"actual primary core: kernel passed {name}"
end JanetCartan.PhysicalPairs.OriginalSourcePrimaryCoreTemplate
end
