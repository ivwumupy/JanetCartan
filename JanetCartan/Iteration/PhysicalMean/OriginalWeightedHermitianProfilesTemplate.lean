module

public import JanetCartan.Iteration.PhysicalMean.HermitianCarrierPullback
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import Lean

/-!
# Actual outer-weighted Hermitian profiles: fixed costs and local geometry

Consumer: the unchanged weighted background quadrature source in
`app:ch_waves:eq:background-quadrature`. The positive baseline is uncut on the
whole original parent, at the genuine reference spatial patch. Only C and the
original outer weight furnish zero germs. No inner κ, angular factor or Fourier
normalization enters this construction. The named budget has no history or
local-domain proof arguments; its actual primitive costs come from97 and98.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalWeightedHermitianProfiles
open SeparatedSampling CurrentMean RawPrimary.SliceBounds HermitianCarrierPullback

/-- The literal fourfold ball of the existing common measurement radius.
This definition does not select another radius or cutoff. -/
def measurementCompact (n : ℕ) (μ : ℝ) : Set (Euclidean n) :=
  closedBall 0 (4 * μ)

/-- Curry the already proved whole-parent graph inclusion; no domain is enlarged. -/
theorem graph_mapsTo_of_forall {n d : ℕ}
    (X : Set (Euclidean n)) (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (K : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (h : ∀ x ∈ X, ∀ z ∈ tsupport φ,
      (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)) ∈ K) :
    MapsTo (fun w : Euclidean n × Point ↦
      (w.1,WithLp.toLp 2 w.2,ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport φ) K :=
  fun w hw ↦ h w.1 hw.1 w.2 hw.2

/-- The original parameter window supplies an open carrier graph neighborhood;
its inverse image is used only to restrict the smoothness proof, not to cut the
amplitude or alter the fixed quantitative budget. The actual producers are95
for the graph/support,97 for B, and98 for C. -/
theorem weighted_profiles_on_parameter_window {n d N : ℕ}
    (X : Set (Euclidean n)) (hX : IsCompact X)
    (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (W : Set (Euclidean 3)) (hW : IsOpen W) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hφW : MapsTo (WithLp.toLp 2) (tsupport φ) W)
    (K Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hgK : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport φ) K)
    (CM CB : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j) (hCB : ∀ j, 0 ≤ CB j) :
    let D := weightedLocalCarrierBudget (N := N) X ζ φ CM CB
    (∀ j, 0 ≤ D j) ∧
      ∀ (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n), ContDiff ℝ ∞ C →
        tsupport C ⊆ X →
      ∀ (B : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ),
        ContDiffOn ℝ ∞ B Ω →
      ∀ (L : ℝ) (r : ℕ), 1 ≤ L →
      HasDerivativeProfile K (fun v ↦ C v.1) r L CM →
      (∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j B v‖ ≤ CB j * L^(j-r)) →
      let H := fun w : Euclidean n × Point ↦ φ w.2 • C w.1
        (hermitianTensor (B (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))))
      ContDiff ℝ ∞ H ∧
        ∀ j w, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L^(j-r) := by
  let g : Euclidean n × Point → Euclidean n × (Euclidean 3 × Euclidean d) :=
    fun w ↦ (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))
  let U : Set (Euclidean n × Point) := univ ×ˢ (WithLp.toLp 2 ⁻¹' W)
  have hnode : ContDiff ℝ ∞ (fun z : Point ↦ WithLp.toLp 2 z) := by fun_prop
  have hz : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ WithLp.toLp 2 w.2) :=
    hnode.comp contDiff_snd
  have hU : IsOpen U := isOpen_univ.prod (hW.preimage hnode.continuous)
  have hg : ContDiffOn ℝ ∞ g U :=
    contDiffOn_fst.prodMk (hz.contDiffOn.prodMk
      (hζ.comp hz.contDiffOn (fun _ hw ↦ hw.2)))
  let O := U ∩ g ⁻¹' Ω
  have hO : IsOpen O := hg.continuousOn.isOpen_inter_preimage hU hΩ
  have hSO : X ×ˢ tsupport φ ⊆ O := by
    intro w hw
    exact ⟨⟨mem_univ _,hφW hw.2⟩,hKΩ (hgK hw)⟩
  exact weighted_local_carrier_profiles X hX ζ φ hφ hφc O hO
    (hg.mono inter_subset_left) hSO K Ω hK hΩ hKΩ (fun _ hw ↦ hw.2)
    hgK CM CB hCM hCB

end JanetCartan.PhysicalMean.OriginalWeightedHermitianProfiles
end

@[expose] public meta section
namespace JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (withActualRow bodyAt)

def ns := `JanetCartan.PhysicalMean.OriginalWeightedHermitianProfiles
def baseline := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
def measurement := `JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfiles
def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
def calculus := `JanetCartan.PhysicalMean.HermitianCarrierPullback
def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args

def save (short : Name) (params : Array Expr) (term : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let env ← getEnv
  let missing := term.getUsedConstants.filter (fun n ↦ (env.find? n).isNone)
  unless missing.isEmpty do
    throwError "actual weighted background: missing imported producers {missing} in {short}"
  let target ← match expected with | some t => pure t | none => inferType term
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let missingType := type.getUsedConstants.filter (fun n ↦ (env.find? n).isNone)
  unless missingType.isEmpty do
    throwError "actual weighted background: missing type producers {missingType} in {short}"
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasLooseBVars || value.hasLooseBVars ||
      type.hasSorry || value.hasSorry then
    throwError "actual weighted background: late data or open proof in {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Original outer-weighted uncut Hermitian baseline on the same saved event, with fixed whole-parent amplitude and common measurement costs (app:ch_waves:eq:background-quadrature). No inner mask, added analytic hypothesis or altered reserve."
  logInfo m!"checked original weighted background {short} at {params.size} inputs"

/-- Register the named costs before R, history and colors. This command reads
existing selected data only and rejects any leaked later variable. -/
elab "publish_original_weighted_background_budget" : command => liftTermElabM <|
    withTransparency .reducible <| withActualRow fun d => do
  let fixed := d.parameters[:44].toArray
  let rowFixed := fixed.push d.row
  let C := d.mean70[37]!
  unless C.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
    throwError "actual weighted background: the original measurement changed"
  let n := d.raw13[0]!
  unless ← isDefEq n C.getAppArgs[0]! do
    throwError "actual weighted background: ambient measurement dimension changed"
  let X := app (ns ++ `measurementCompact) #[n,C.getAppArgs[2]!]
  let ζ ← bodyAt (baseline ++ `ζ) d.parameters
  let φ ← bodyAt (baseline ++ `ψ) d.parameters
  let CM := app (measurement ++ `CM) fixed
  let CB := app (parent ++ `A) rowFixed
  let dims := #[n,mkApp2 (mkConst ``Nat.sub) n (mkNatLit 1),d.raw13[1]!]
  let inputs := dims ++ #[X,ζ,φ,CM,CB]
  save `D rowFixed (app (calculus ++ `weightedLocalCarrierBudget) inputs) true
  save `D_nonneg rowFixed (app (calculus ++ `weightedLocalCarrierBudget_nonneg)
    (inputs ++ #[app (measurement ++ `CM_nonneg) fixed,app (parent ++ `A_nonneg) rowFixed]))

/-- Peel only the root lets of an inferred theorem type. Native proof arguments
are never recursively beta- or zeta-reduced. -/
partial def rootLets (e : Expr) : Expr :=
  let e := e.headBeta.consumeMData
  match e with
  | .letE _ _ value body _ => rootLets (body.instantiate1 value)
  | _ => e

/-- Combine the actual95 support, actual97 uncut matrix and actual98 measurement.
Every analytic input is a named checked producer on the SAME native event. -/
elab "publish_original_weighted_background_profiles" : command => liftTermElabM <|
    withTransparency .reducible <| withActualRow fun d => do
  let p := d.parameters
  let fixed := p[:44].toArray
  let rowFixed := fixed.push d.row
  let n := d.raw13[0]!
  let dim := mkApp2 (mkConst ``Nat.sub) n (mkNatLit 1)
  let dims := #[n,dim,d.raw13[1]!]
  let bg (key : Name) := app (baseline ++ key) p
  let par (key : Name) := app (parent ++ key) rowFixed
  let X := bg `X
  let ζ := bg `ζ
  let φ := bg `ψ
  let outer := d.native64[:22].toArray.push d.row
  let hφ := app `JanetCartan.PhysicalSampling.OriginalOuterWeights.smooth outer
  let hφc := app `JanetCartan.PhysicalSampling.OriginalOuterWeights.compact outer
  let hζ := bg `ζ_smooth
  let tζ ← inferType hζ
  unless tζ.isAppOfArity `ContDiffOn 11 do
    throwError "actual weighted background: changed genuine carrier smoothness"
  let W := tζ.getAppArgs[10]!
  unless W.isAppOfArity `JanetCartan.FrozenMenu.parameterInterior 1 do
    throwError "actual weighted background: not the original parameter interior"
  let hW := app `JanetCartan.FrozenMenu.isOpen_parameterInterior W.getAppArgs
  let K := par `J
  let Ω := par `Ω
  let hgraph := app (ns ++ `graph_mapsTo_of_forall)
    #[n,dim,X,ζ,φ,K,bg `graph_in_parent]
  let CM := app (measurement ++ `CM) fixed
  let CB := par `A
  let geometric := app (ns ++ `weighted_profiles_on_parameter_window)
    (dims ++ #[X,bg `X_compact,ζ,φ,hφ,hφc,W,hW,hζ,bg `outer_parameter_interior,
      K,Ω,par `J_compact,par `Ω_open,par `J_in_Ω,hgraph,
      CM,CB,app (measurement ++ `CM_nonneg) fixed,par `A_nonneg])
  let C := bg `C
  let hC := app (measurement ++ `smooth) p
  let hMC := mkApp (app (measurement ++ `joint_profile) p) K
  let tMC ← inferType hMC
  unless tMC.isAppOfArity `JanetCartan.HasDerivativeProfile 11 &&
      tMC.getAppArgs[6]! == K && tMC.getAppArgs[8]! == d.mean70[61]! &&
      tMC.getAppArgs[9]! == d.mean70[60]! && tMC.getAppArgs[10]! == CM do
    throwError "actual weighted background: changed measurement set, reserve, scale or cost"
  let hTwo := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed
  let tTwo ← inferType hTwo
  let tReached ← inferType p[45]!
  unless tTwo.isAppOfArity ``LE.le 4 && tReached.isAppOfArity ``LE.le 4 do
    throwError "actual weighted background: changed numerical stage threshold"
  unless tTwo.getAppArgs[3]! == tReached.getAppArgs[2]! &&
      tReached.getAppArgs[3]! == p[44]! do
    throwError "actual weighted background: reached threshold no longer matches original hS/R"
  let inst ← synthInstance (mkApp (mkConst `Preorder [.zero]) (mkConst ``Real))
  let hR := mkAppN (mkConst `le_trans [.zero])
    #[mkConst ``Real,inst,tTwo.getAppArgs[2]!,tTwo.getAppArgs[3]!,p[44]!,hTwo,p[45]!]
  let hL := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
    #[p[44]!,hR,p[46]!]
  let rate := bg `rate
  let colorType := (← inferType rate).bindingDomain!
  withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color => do
    let pc := p.push color
    let B := app (parent ++ `amplitude) pc
    let hB := app (parent ++ `smooth) pc
    let hBC := app (parent ++ `jets) pc
    let proof := mkAppN (.proj ``And 1 geometric)
      #[C,hC,bg `C_support_X,B,hB,d.mean70[60]!,d.mean70[61]!,hL,hMC,hBC]
    let smoothType := rootLets (← inferType (.proj ``And 0 proof))
    unless smoothType.isAppOf `ContDiff do
      throwError "actual weighted background: lost global weighted smoothness"
    let rawField := smoothType.appArg!
    let physical := (← inferType C).bindingDomain!
    let point := mkConst `JanetCartan.SeparatedSampling.Point
    let product := mkApp2 (mkConst ``Prod [.zero,.zero]) physical point
    let H := bg `H
    let field ← withLocalDeclNoLocalInstanceUpdate `w .default product fun w => do
      let x := .proj ``Prod 0 w
      let z := .proj ``Prod 1 w
      let value ← mkAppM ``HSMul.hSMul #[mkApp φ z,mkAppN H #[color,x,z]]
      mkLambdaFVars #[w] value
    let rawBudget := app (calculus ++ `weightedLocalCarrierBudget) (dims ++ #[X,ζ,φ,CM,CB])
    let D := app (ns ++ `D) rowFixed
    let target := (rootLets (← inferType proof)).replace fun e =>
      if e == rawField then some field else if e == rawBudget then some D else none
    unless (target.find? (·.isAppOf (baseline ++ `H))).isSome &&
        (target.find? (·.isAppOf (ns ++ `D))).isSome do
      throwError "actual weighted background: target must retain exact95 H and static45 D"
    if (target.find? (· == rawField)).isSome ||
        (target.find? (·.isAppOf (calculus ++ `weightedLocalCarrierBudget))).isSome then
      throwError "actual weighted background: raw field or unnamed budget survived target replacement"
    unless target.isAppOfArity ``And 2 do
      throwError "actual weighted background: expected the smoothness/jet conjunction"
    save `weighted_profile pc proof false (some target)
    let named := app (ns ++ `weighted_profile) pc
    let smooth := target.getAppArgs[0]!
    let jets := target.getAppArgs[1]!
    save `weighted_smooth pc (app ``And.left #[smooth,jets,named]) false (some smooth)
    save `weighted_jets pc (app ``And.right #[smooth,jets,named]) false (some jets)

end JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate
end
