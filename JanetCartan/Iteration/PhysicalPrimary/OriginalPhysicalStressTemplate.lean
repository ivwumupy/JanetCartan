module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutObservation
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalPhaseTemplate

/-! # Exact observed primary stress at the physical carrier
The local source is the native full tensor's two admitted quadratures. Its
parameter comparison neighborhood contains every original closed source cell,
while the full inverse itself stays on the original doubled window. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalStress
open ResponseTransfer

/-- Positive modulation of the literal native smooth source preserves the
small spatial support and gives joint smoothness everywhere. The physical
source class below uses exactly this function and its native `MemLp` proof. -/
theorem raw_forcing_regular {n d : ℕ}
    (ρ : ℝ) (φ : (Euclidean 3 × Euclidean d) → Euclidean n → ℝ)
    (a : (Euclidean 3 × Euclidean d) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (X : Set (Euclidean n)) (hp : ContDiff ℝ ∞ (Function.uncurry φ))
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hs : ∀ c, tsupport (a c) ⊆ X) :
    let g := fun c x ↦ carrier ρ (φ c) x • a c x
    ContDiff ℝ ∞ (fun w : Euclidean n × (Euclidean 3 × Euclidean d) ↦ g w.2 w.1) ∧
      ∀ c, tsupport (g c) ⊆ X := by
  intro g
  have hφ := hp.comp (contDiff_snd.prodMk contDiff_fst)
  have hA := ha.comp (contDiff_snd.prodMk contDiff_fst)
  constructor
  · exact (((contDiff_const (c := Complex.I)).mul
      (Complex.ofRealCLM.contDiff.comp ((contDiff_const (c := ρ)).mul hφ))).cexp).smul hA
  · intro c
    exact (tsupport_smul_subset_right _ _).trans (hs c)

end JanetCartan.PhysicalPrimary.OriginalPhysicalStress
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalStressTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalPhysicalPhaseTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalStress
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def phase := `JanetCartan.PhysicalPrimary.OriginalUncutSource.Physical
private def source := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def obs := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def comparison := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def stress := `JanetCartan.PhysicalPrimary.OriginalStressClass
private def appl (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def emit (name : Name) (xs : Array Expr) (v : Expr) (data := false)
    (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ name) xs v data t
  addDocStringCore (ns ++ name) "Actual uncut primary stress at the physical reciprocal carrier and original scalar, with both quadratures on the original plateau; no source identification premise (app:ch_response:eq:response-actual-solver-formula)."
  return h

elab "instantiate_original_physical_stress_part " step:num : command => liftTermElabM do
  let step := step.getNat
  unless step ≤ 4 do throwError "unknown physical stress part"
  withPhysicalPhaseInputs fun xs _ s ph => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let φ := appl (ind ++ `phase) xs
    let native := appl (ind ++ `source) xs
    let v := (← OriginalLocalWaveGeometryTemplate.bodyAt (geo ++ `parameter_window) s).getAppArgs
    let cut := #[n,s[1]!,v[23]!,v[24]!]
    let W := appl (comparison ++ `parameterComparisonWindow) cut
    let ws := appl (comparison ++ `parameterComparisonWindow_spec) cut
    let hV := Expr.proj ``And 0 (.proj ``And 1 ws)
    let hθ := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 ws))
    let hPhase := appl (phase ++ `phase_on_source) xs
    let joint := appl (obs ++ `joint_smooth) ph
    let ρ ← mkAppM ``Inv.inv #[s[47]!]
    if step == 0 then
      let g ← forallBoundedTelescope (← inferType φ) (some 1) fun cs _ => do
        let c := cs[0]!
        mkLambdaFVars cs (appl (source ++ `rawForcing) (s ++ #[c,mkApp φ c,ρ]))
      let raw ← emit `forcing xs g true
      let ha := appl (source ++ `smooth) s
      let hs := appl (source ++ `support) s
      let pre := (← inferType ha).appArg!
      unless pre.isAppOf `Function.uncurry do throwError "physical stress: native parameter-first source changed"
      let X ← forallBoundedTelescope (← inferType hs) (some 1) fun _ sub => pure sub.appArg!
      let bundle := appl (ns ++ `raw_forcing_regular) #[n,s[0]!,ρ,φ,pre.appArg!,X,joint,ha,hs]
      discard <| emit `forcing_smooth xs (.proj ``And 0 bundle)
      discard <| emit `forcing_support xs (.proj ``And 1 bundle)
      forallBoundedTelescope (← inferType φ) (some 1) fun cs _ => do
        let c := cs[0]!
        let hcont ← mkAppM `Continuous.uncurry_left #[c,← mkAppM `ContDiff.continuous #[joint]]
        let hm := appl (source ++ `forcing_memLp) (s ++ #[c,mkApp φ c,hcont,ρ])
        let mt := (← inferType hm).getAppArgs
        let mt := mkAppN (← inferType hm).getAppFn (mt.set! (mt.size-3) (mkApp raw c))
        discard <| emit `forcing_memLp (xs.push c) hm false (some mt)
      logInfo "physical forcing: global joint smoothness, native L2 membership and compact spatial support"
      return
    forallBoundedTelescope (← inferType φ) (some 1) fun cs _ => do
      let c := cs[0]!
      withLocalDeclD `hc (← mkAppM `Membership.mem #[W,c]) fun hc => do
        let nativeWindow := mkAppN hV #[c,hc]
        let args := xs ++ #[c,hc]
        if step == 1 then
          let raw := appl `JanetCartan.PhysicalPrimary.OriginalLocalWaves.source_quadratures
            (s ++ #[c,nativeWindow])
          discard <| emit `real_admission args (.proj ``And 0 raw)
          discard <| emit `imag_admission args (.proj ``And 1 raw)
          logInfo "physical forcing: both original raw tensor admissions retained on the fixed comparison window"
          return
        let hcont ← mkAppM `Continuous.uncurry_left #[c,← mkAppM `ContDiff.continuous #[joint]]
        let src := s ++ #[c,mkApp φ c,hcont,ρ]
        let u := appl (source ++ `realization) src
        if step == 2 then
          let t := (← inferType u)
          let eq := mkAppN (mkConst ``Eq [.succ .zero]) #[t,u,mkApp native c]
          discard <| emit `same_inverse_source (xs.push c) (← mkEqRefl u) false (some eq)
          logInfo "original physical index's full inverse source is literally the same Source53 realization"
          return
        if step == 3 then
          let p := s ++ #[c,mkApp φ c,hcont,mkAppN hPhase #[c,nativeWindow],nativeWindow,mkAppN hθ #[c,hc]]
          let eq := appl (stress ++ `source53_class) p
          discard <| emit `raw_uncut_class args eq
          logInfo "physical forcing: both native geometric hypotheses discharged on the open source plateau"
          return
        let raw := appl (ns ++ `raw_uncut_class) args
        let sides := (← inferType raw).getAppArgs
        let trans := mkConst ``Eq.trans [.succ .zero]
        let same := appl (ns ++ `same_inverse_source) (xs.push c)
        discard <| emit `uncut_class args (mkAppN trans #[sides[0]!,sides[1]!,u,mkApp native c,raw,same])
        let neutral := appl (source ++ `realization_eq) src
        let rhs := (← inferType neutral).getAppArgs[2]!
        discard <| emit `chi3_neutral_class args (mkAppN trans #[sides[0]!,sides[1]!,u,rhs,raw,neutral])
        logInfo "physical forcing: native admitted sum identified with both canonical classes"

end JanetCartan.PhysicalPrimary.OriginalPhysicalStressTemplate
end
