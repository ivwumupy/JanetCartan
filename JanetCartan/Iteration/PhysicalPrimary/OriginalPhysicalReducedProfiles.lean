module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalInverseEnvelopes
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalJetTransfer

/-! # Actual physical complete inverse: classical joint reserved profiles
The all-history complete inverse theorem is queried at the same physical
frequency tau^-1. Its literal vector Fourier classes are identified with the
classical reduced solution, and precisely n+1 reserved spatial derivatives pay
for the Fourier-to-classical diagonal. All costs precede the physical history. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfiles
open Pseudodifferential FixedDomainInverse CanonicalAtomRealization

/-- The final classical transfer consumes the native complete-inverse norm,
not a residual power or a fresh solution, at the exact source reserve. -/
theorem classical_of_native_classes {n d N : ℕ}
    {V Vbig : Set (Euclidean 3 × Euclidean d)} (hV : IsOpen V) (hsub : V ⊆ Vbig)
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ V))
    {u v : (Euclidean 3 × Euclidean d) → Lp (EuclideanSpace ℂ (Fin N)) 2 (volume : Measure (Euclidean n))}
    (he : ∀ c ∈ V, ∀ k, iteratedFDeriv ℝ k u c = iteratedFDeriv ℝ k v c)
    (hclass : ∀ c ∈ V, ∀ k (w : Fin k → (Euclidean 3 × Euclidean d)),
      ∃ ug : PiLp 2 (fun _ : Fin N ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
        (∀ i, ug i =ᵐ[volume] fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i) ∧
        ug = finiteL2CoordinateIsometry volume (iteratedFDeriv ℝ k u c w) ∧
        (∀ s : ℝ, MemMatrixFourierSobolev s ug ↔ MemVectorFourierSobolev s (iteratedFDeriv ℝ k u c w)) ∧
        (∀ s : ℝ, matrixFourierSobolevNorm s ug = vectorFourierSobolevNorm s (iteratedFDeriv ℝ k u c w)))
    (S : ℕ → ℕ → ℝ) (hS : ∀ k p, 0 ≤ S k p)
    {τ size K : ℝ} (hτ : 0 < τ) (hsize : 0 ≤ size) (hK : 1 ≤ K)
    (reserve rSource : ℕ) (hr : reserve+n+1 = rSource)
    (hv : ∀ k p : ℕ, ∀ c ∈ Vbig, ∀ w : Fin k → (Euclidean 3 × Euclidean d),
      (∀ l, ‖w l‖ ≤ 1) →
      MemVectorFourierSobolev (p : ℝ) (iteratedFDeriv ℝ k v c w) ∧
      vectorFourierSobolevNorm (p : ℝ) (iteratedFDeriv ℝ k v c w) ≤
        S k p * (τ^3*size) * K^(p+k-rSource)) :
    ∀ m q, q ∈ univ ×ˢ V →
      ‖iteratedFDeriv ℝ m f q‖ ≤ reducedProfileClassicalBudget n d N S m * (τ^3*size) * K^(m-reserve) ∧
      ∀ i, ‖iteratedFDeriv ℝ m (fun b ↦ f b i) q‖ ≤
        reducedProfileClassicalBudget n d N S m * (τ^3*size) * K^(m-reserve) := by
  apply OriginalReducedReserve.reserved_joint_of_ordered_classes hV hf S hS hτ hsize hK reserve
  intro c hc k p w hw
  obtain ⟨ug,hug,_,hm,hn⟩ := hclass c hc k w
  have hv := hv k p c (hsub hc) w hw
  rw [← he c hc k,← hr] at hv
  exact ⟨ug,hug,(hm p).2 hv.1,(hn p).trans_le hv.2⟩

end JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfiles
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfiles
private def inv := `JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def fam := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def phy := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def jets := `JanetCartan.PhysicalPrimary.OriginalPhysicalJetTransfer
private def word := `JanetCartan.PhysicalPrimary.OriginalReservedWords
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def app (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  logInfo m!"physical reduced: checked {k}"
  addDocStringCore (ns ++ k) "Actual original complete-inverse Fourier bound transferred to its physical classical joint reduced solution at the literal reciprocal carrier; prehistory cost and exact reserve (app:ch_response:eq:response-graded-reduced)."
  return h
private def conj (hs : List Expr) : MetaM Expr := do
  match hs with
  | [] => throwError "empty native physical family"
  | [h] => return h
  | h::hs => mkAppM ``And.intro #[h,← conj hs]

/-- The same point as the existing 66 query, now reaching the actual complete
inverse threshold. All phase/stress/class identities are reused verbatim. -/
def withNativePhysicalInputs (go : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (inv ++ `S)).type (some 42) fun p _ => do
    unless p.size == 42 do throwError "physical reduced: full inverse static42 changed"
    let base := p[:40].toArray ++ #[p[41]!] ++
      #[`windowExponent,`windowExponent_pos,`windowExponent_lt_one].map (fun k => mkConst (word ++ k))
    let source := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
    let fixed := base[:39].toArray
    let st := base[:41].toArray
    let origType ← inferType (app (source ++ `a) fixed)
    forallBoundedTelescope origType (some 1) fun rr type => do
      let R₀ := rr[0]!
      withLocalDeclD `hReached (← mkAppM ``LE.le #[app (inv ++ `S) p,R₀]) fun hR => do
        let h66 ← mkAppM `le_trans #[app (inv ++ `remainder_threshold) p,hR]
        let hSource ← mkAppM `le_trans #[app (fam ++ `source_threshold) st,h66]
        let .forallE _ _ rest _ := type | throwError "physical reduced: original source threshold lost"
        forallBoundedTelescope (rest.instantiate1 hSource) (some 12) fun tail _ => do
          let s := fixed ++ #[R₀,hSource] ++ tail
          let rawScalar ← mkAppM ``Subtype.val #[s[49]!]
          let i ← mkAppM (ind ++ `carrierIndex) #[R₀,s[41]!,s[42]!,s[43]!,s[45]!,s[47]!,s[50]!,rawScalar]
          let ptType := (← inferType (app (inv ++ `observed_solution) p)).bindingDomain!
          unless ptType.isAppOfArity ``Subtype 2 do throwError "physical reduced: admitted inverse index lost"
          let both := (← whnf (ptType.getAppArgs[1]!.beta #[i])).getAppArgs
          let hist ← whnf both[0]!
          let winType := hist.getAppArgs[1]!.getAppArgs[1]!.getAppArgs[1]!.getAppArgs[1]!.getAppArgs[0]!
          withLocalDeclD `hRateOne (← mkAppM ``LE.le #[s[47]!,← mkNumeral (mkConst `Real) 1]) fun hτ1 => do
            withLocalDeclD `hScaleWindow winType fun hWin => do
              let hρ ← mkAppM (ind ++ `carrier_one_le) #[s[48]!,hτ1]
              let hist ← conj [hR,s[44]!,hρ,s[46]!,hWin,s[51]!]
              let src ← conj [s[48]!,← mkAppM ``Subtype.property #[s[49]!],s[52]!]
              let admitted ← mkAppM ``And.intro #[hist,src]
              let pt := mkAppN (mkConst ``Subtype.mk [.one]) #[ptType.getAppArgs[0]!,ptType.getAppArgs[1]!,i,admitted]
              let old := base ++ #[R₀,h66] ++ tail ++ #[hτ1,hWin]
              go (p ++ #[R₀,hR] ++ tail ++ #[hτ1,hWin]) p old s pt

elab "construct_physical_reduced_native_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (inv ++ `S)).type (some 42) fun p _ => do
    let cost ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      withLocalDeclD `s (mkConst ``Nat) fun s =>
        mkLambdaFVars #[k,s] (app (inv ++ `cost) (p ++ #[s,k]))
    let S ← emit `FourierCost p cost true
    let nn ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      withLocalDeclD `s (mkConst ``Nat) fun s =>
        mkLambdaFVars #[k,s] (app (inv ++ `cost_nonneg) (p ++ #[s,k]))
    discard <| emit `FourierCost_nonneg p nn
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let classical := app `JanetCartan.CanonicalAtomRealization.reducedProfileClassicalBudget #[n,p[0]!,n,S]
    discard <| emit `C p classical true
  withNativePhysicalInputs fun xs p old s pt => do
    let u := app (jets ++ `full_solution) old
    let v := app (inv ++ `observed_solution) (p.push pt)
    discard <| emit `same_complete_solution xs (← mkEqRefl u) false (some (← mkEq u v))
    let he := app (jets ++ `ordered_solution_jets) old
    let he ← emit `ordered_solution_jets xs he false (some ((← inferType he).replace fun e => if e == u then some v else none))
    let smooth := app (phy ++ `solver_joint_smooth) old
    let rawReduced := (← inferType smooth).getAppArgs[(← inferType smooth).getAppArgs.size-2]!
    let f ← emit `reduced xs rawReduced true
    discard <| emit `smooth xs smooth
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let va := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let ws := app (cmp ++ `parameterComparisonWindow_spec) #[n,s[1]!,va[23]!,va[24]!]
    let fourier ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      withLocalDeclD `p (mkConst ``Nat) fun r => do
        mkLambdaFVars #[k,r] (app (inv ++ `on_admitted) (p ++ #[r,k,.proj ``Subtype 0 pt,.proj ``Subtype 1 pt]))
    let fourier ← emit `native_ordered_bound xs fourier
    let oldBase := old[:44].toArray
    let nativePoint := app (ind ++ `point) old
    let hK := app (fam ++ `Point.hK) (oldBase.push nativePoint)
    withLocalDeclD `reserve (mkConst ``Nat) fun reserve => do
      let order := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) reserve n) (mkNatLit 1)
      withLocalDeclD `hSourceReserve (← mkEq order s[37]!) fun hr => do
        let V := (← inferType (.proj ``And 0 ws)).appArg!
        let Vbig := app (fam ++ `Static.V) old[:41].toArray
        let result := app (ns ++ `classical_of_native_classes)
          #[n,s[0]!,n,V,Vbig,.proj ``And 0 ws,.proj ``And 0 (.proj ``And 1 ws),f,smooth,
            app (jets ++ `comparison_solution) old,v,he,app (phy ++ `ordered_classes) old,
            app (ns ++ `FourierCost) p,app (ns ++ `FourierCost_nonneg) p,s[47]!,s[50]!,s[45]!,
            s[48]!,s[51]!,hK,reserve,s[37]!,hr,fourier]
        let t := (← inferType result).replace fun e => if e == rawReduced then some f else none
        discard <| emit `joint_jets (xs ++ #[reserve,hr]) result false (some t)
  logInfo "actual physical complete inverse at tau^-1: SAME uncut source/operator/phase, ordered Fourier bounds transferred to all classical joint vector and coordinate jets with exactly n+1 source reserve"

end JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfilesTemplate
end
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
construct_physical_reduced_native_profiles
