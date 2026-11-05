module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-! # The actual initialized mean's source-dependent budget

The geometric reach is already fixed before every raw budget. Here the original
initializer is combined with the actual positive-current inverse and the COMMON
finite-Picard budget, before the history and target. Only the coefficient may
depend on the finite Picard index (`main:prop:mean`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
open JanetCartan.CurrentMean JanetCartan.ContinuumRow
open JanetCartan.CarrierSobolev JanetCartan.CoerciveInverse
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles

/-- The actual initializer and common Picard source share the raw reserve n+1. -/
def rawBudget (Dinit Cinv M : ℕ → ℝ) (s : ℕ) : ℝ :=
  Dinit s + Cinv s * (M s + M 0)

theorem rawBudget_nonneg (Dinit Cinv M : ℕ → ℝ)
    (hDinit : ∀ s, 0 ≤ Dinit s) (hCinv : ∀ s, 0 ≤ Cinv s)
    (hM : ∀ s, 0 ≤ M s) (s : ℕ) : 0 ≤ rawBudget Dinit Cinv M s :=
  add_nonneg (hDinit s) (mul_nonneg (hCinv s) (add_nonneg (hM s) (hM 0)))

/-- Genuine raw source profile at reserve n+1: retain the original initializer,
use the actual paired inverse bound, and weaken only the natural exponents. -/
theorem initialized_raw_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (Dinit Cinv M : ℕ → ℝ) (hDinit : ∀ s, 0 ≤ Dinit s)
    (hCinv : ∀ s, 0 ≤ Cinv s) (hM : ∀ s, 0 ≤ M s)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {T R h : ℝ} (hT : 1 ≤ T) (hTR : T ≤ R) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hpair : ∀ s w, w ∈ (periodicSobolevScale n (Euclidean n)).level s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s ((augmentedNormal image U ψ).inverse w) +
        (augmentedInputSobolevScale n ι).gradeNorm s (rightInverse (augmentedRow image U ψ) w) ≤
          Cinv s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-2*(n/2+2))*‖w‖))
    (initial : AugmentedInput n ι) (hinitial : ∀ s, initial ∈ augmentedInputLevel n ι s)
    (hinitialBound : ∀ s, (augmentedInputSobolevScale n ι).gradeNorm s initial ≤ Dinit s*T^(s-(1+n)))
    (e : SmoothResidual n)
    (hreg : ∀ s, rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ augmentedInputLevel n ι s)
    (hsource : ∀ s, residualSobolevSeminorm n s e ≤ M s*h*R^(s-2*(n/2+2))) :
    (∀ s, 0 ≤ rawBudget Dinit Cinv M s) ∧
    ∀ s, initial+rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ augmentedInputLevel n ι s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s
        (initial+rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e)) ≤
          rawBudget Dinit Cinv M s*R^(s-(1+n)) := by
  have hreserve : 1+n ≤ 2*(n/2+2) := by omega
  have horder (s : ℕ) : s-2*(n/2+2) ≤ s-(1+n) := by omega
  have hR : 1 ≤ R := hT.trans hTR
  refine PhysicalMean.initializedRaw_source_profile Dinit Cinv M hDinit hCinv hM
    image U ψ hT hTR hh1 ?_ initial hinitial ?_ e hreg ?_
  · intro s w hw
    apply (hpair s w hw).trans
    apply mul_le_mul_of_nonneg_left _ (hCinv s)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hT (horder s)) (norm_nonneg w))
  · intro s
    exact (hinitialBound s).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hT) hTR _) (hDinit s))
  · intro s
    exact (hsource s).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hR (horder s)) (mul_nonneg (hM s) hh))
end JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanFieldCurrentTemplate
open Lean Meta Elab Command
open OriginalCanonicalMomentAdmissionTemplate (withSelectedBefore)
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles
def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p
def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)
def save (key : Name) (p : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "full initialized field: later or unresolved parameter in {key}"
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do throwError "full initialized field: missing constants {missing.toList}"
  let name := root ++ key
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  liftM <| IO.eprintln s!"full initialized field: checking {key}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Original full initialized mean budget/profile, with SAME raw initializer, positive-current inverse and common full-source Picard budget; fixed geometric threshold precedes every budget and history (main:prop:mean)."
  liftM <| IO.eprintln s!"full initialized field: passed {key}/{p.size}"

/-- Construct only the raw coefficient on the fixed selected33 and index N. -/
def publishRawBudget (nonneg : Bool) : MetaM Unit :=
  withSelectedBefore 44 fun native selected _ => do
    let Dinit := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.Craw native
    let Cinv := app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.Cinv native
    withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
      let p := selected.push N
      let M := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.D p
      let value := app (root ++ `rawBudget) #[Dinit,Cinv,M]
      if !nonneg then
        save `Craw p value true (some (← mkArrow (mkConst ``Nat) (mkConst ``Real)))
      else
        let hinit := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.Craw_nonneg native
        let hinv := app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.Cinv_nonneg native
        let hM := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.D_nonneg p
        let proof := app (root ++ `rawBudget_nonneg) #[Dinit,Cinv,M,hinit,hinv,hM]
        let target ← termWith [(`C,app (root ++ `Craw) p)] "∀ s : ℕ, 0 ≤ C s"
        save `Craw_nonneg p proof false (some target)

/-- Apply the fixed-reach continuation to the actual before-history raw budget. -/
def publishFieldExists : MetaM Unit :=
  withSelectedBefore 44 fun native selected _ => do
    withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
      let p := selected.push N
      let D := app (root ++ `Craw) p
      let hD := app (root ++ `Craw_nonneg) p
      save `exists_CW p (app (root ++ `raw_profile_exists) (native ++ #[D,hD]))

def publishFieldChoice (mode : Nat) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (root ++ `exists_CW)).type (some 34) fun p _ => do
    let packet := app (root ++ `exists_CW) p
    let C ← instantiateMVars (← mkAppM ``Classical.choose #[packet])
    let spec ← instantiateMVars (← mkAppM ``Classical.choose_spec #[packet])
    let named := app (root ++ `CW) p
    match mode with
    | 0 => save `CW p C true (some (← mkArrow (mkConst ``Nat) (mkConst ``Real)))
    | 1 =>
      let target ← termWith [(`C,named)] "∀ s : ℕ, 0 ≤ C s"
      save `CW_nonneg p (.proj ``And 0 spec) false (some target)
    | 2 =>
      let value := Expr.proj ``And 1 spec
      let target := (← instantiateMVars (← inferType value)).replace fun e => if e == C then some named else none
      unless target.getUsedConstants.contains (root ++ `CW) do
        throwError "full initialized field: continuation lost the named source budget"
      save `CW_continuation p value false (some target)
    | _ => throwError "full initialized field: unknown coefficient mode"
end JanetCartan.PhysicalMean.OriginalSelectedMeanFieldCurrentTemplate
end

#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.initialized_raw_profile
