module
public import JanetCartan.Iteration.PhysicalMean.CanonicalFieldProfiles
public import JanetCartan.Iteration.PhysicalMean.CanonicalRawProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
public meta import Lean

/-!
# A geometric initial reach uniform in the full raw source budget

The full initialized mean uses the original raw initializer plus the positive
current inverse of the complete-source Picard iterate. Its raw budget depends
on the finite Picard index, but the initial geometric reach must not. Choose
that reach from the existing half-tangent coefficient producer first, and only
then apply the existing base/full-strain estimate to an arbitrary raw budget.
This is the zero-reserve case needed by the actual physical mean
(`main:prop:mean`, `app:ch_mean_pairs:eq:mean-coarse-field-profile`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean
open ContinuumRow CarrierSobolev AuxiliaryRawBand PhysicalBackground GeometricProfile

/-- The geometric initial threshold is chosen before every raw source budget,
so it can enter the dimension-only final reach even when that budget later
depends on the accuracy-dependent finite Picard index. Both the full field and
its full linearized strain are estimated on the same original wide ball. -/
theorem exists_history_fixedSourceBase_zero_profile_uniform_raw
    {n : ℕ} {ι : Type*} [Fintype ι]
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius)
    (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 R))
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ}
    (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent*((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧
      ∀ D : ℕ → ℝ, (∀ s, 0 ≤ D s) →
      ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ (raw : AugmentedInput n ι), (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∀ L : ℝ, currentCoefficientScale R₀ stage ≤ L →
      (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s raw ≤ D s*L^(s-(1+n))) →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ (baseVariation χsrc raw F X₀) (ball 0 R) ∧
      ∀ s, cNorm (closedBall 0 r) s (baseVariation χsrc raw F X₀) +
        cNorm (closedBall 0 r) s (linearizedMetric F (baseVariation χsrc raw F X₀)) ≤
          C s*L^s := by
  obtain ⟨S, hS, C, hC, hraising⟩ := exists_history_halfTangent_profile
    G hr hrR hR hB hStar (show 2+(0+1) ≤ rStar by omega) horder
  obtain ⟨A, hA, hhistory⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (G := G.map) (isCompact_closedBall (0 : Euclidean n) r)
    (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  refine ⟨S, hS, ?_⟩
  intro D hD
  obtain ⟨E, hE, hbase⟩ := exists_baseVariation_strain_profile (ι := ι)
    (isCompact_closedBall (0 : Euclidean n) r) isOpen_ball (closedBall_subset_ball hrR)
    χsrc hs X₀ hX₀ A C D hA hC hD
  refine ⟨E, hE, ?_⟩
  intro R₀ hR₀ stage u ell hu raw hreg L hTL hraw F
  obtain ⟨hi, _, hCp⟩ := hraising R₀ hR₀ stage u ell hu
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hT : 1 ≤ currentCoefficientScale R₀ stage :=
    one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) stage
  have hL : 1 ≤ L := hT.trans hTL
  have hFp : HasDerivativeProfile (closedBall 0 r) F 2 L A := by
    intro s
    apply (hhistory R₀ (hS.trans hR₀) stage u ell hu _ Subset.rfl s).trans
    apply mul_le_mul_of_nonneg_left _ (hA s)
    exact (pow_le_pow_left₀ (zero_le_one.trans hT) hTL _).trans
      (pow_le_pow_right₀ hL (by omega : s-rStar ≤ s-2))
  have hCr : HasDerivativeProfile (closedBall 0 r) (halfTangentCoefficient F) 1 L C := by
    intro s
    exact (hCp s).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hT) hTL _) (hC s))
  refine ⟨contDiffOn_baseVariation χsrc hs raw hreg isOpen_ball hF.contDiffOn hX₀ hi, ?_⟩
  simpa only [Nat.sub_zero] using hbase F hF hi raw hreg 0 L hL hFp hCr hraw

end JanetCartan.PhysicalMean
end
#print axioms JanetCartan.PhysicalMean.exists_history_fixedSourceBase_zero_profile_uniform_raw

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfilesTemplate
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (ActualInverse withActualInverse)
open OriginalBackgroundHermitianTemplate (bodyAt)

private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs

/-- Read the SAME native wide geometry from the existing zero-reserve producer.
Discard only its initializer budget and the redundant zero-reserve proof; the
new threshold is chosen before any replacement raw budget. -/
def uniformPacket (d : ActualInverse) : MetaM Expr := do
  let (base,_,_) ← OriginalCanonicalBaseProfilesTemplate.profileArguments d
  let chosen ← bodyAt `JanetCartan.PhysicalBackground.NativeBaseProfiles.fieldS base
  unless chosen.isAppOfArity ``Classical.choose 3 do
    throwError "full initialized field: changed original geometric choice"
  let packet := chosen.getAppArgs[2]!
  unless packet.isAppOfArity `JanetCartan.PhysicalMean.exists_history_fixedSourceBase_profile 23 do
    throwError "full initialized field: changed original native field producer23"
  let a := packet.getAppArgs
  unless a[18]! == mkNatLit 0 do
    throwError "full initialized field: original base reserve is not zero"
  let args := a[:13].toArray ++ #[a[15]!,a[16]!,a[17]!,a[19]!,a[20]!,a[22]!]
  return mkAppN (mkConst `JanetCartan.PhysicalMean.exists_history_fixedSourceBase_zero_profile_uniform_raw [.zero]) args

private def save (key : Name) (p : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "full initialized field: later or unresolved input in {key}"
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do
      throwError "full initialized field: missing original constants {missing.toList}"
  let name := root ++ key
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  liftM <| IO.eprintln s!"full initialized field: kernel checking {key}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "SAME original wide physical mean geometry and initializer: initial reach chosen before every raw source budget and hence before Picard accuracy/history; no analytic field estimate assumed (main:prop:mean; app:ch_mean_pairs:eq:mean-coarse-field-profile)."
  liftM <| IO.eprintln s!"full initialized field: kernel passed {key}/{p.size}"
  return app name p

/-- Publish the actual geometric predicate once; its small downstream choices
use that checked predicate instead of rebuilding the native inverse telescope. -/
def publishUniformActual : MetaM Unit :=
  withActualInverse fun d => do
    discard <| save `uniform_raw_exists d.parameters[:44].toArray (← uniformPacket d)

def publishUniformChoice (mode : Nat) : MetaM Unit := do
  let info ← getConstInfo (root ++ `uniform_raw_exists)
  forallBoundedTelescope info.type (some 44) fun p _ => do
    let packet := app (root ++ `uniform_raw_exists) p
    let chosen ← instantiateMVars (← mkAppM ``Classical.choose #[packet])
    let spec ← instantiateMVars (← mkAppM ``Classical.choose_spec #[packet])
    let S := app (root ++ `SfullW) p
    match mode with
    | 0 => discard <| save `SfullW p chosen true (some (mkConst ``Real))
    | 1 =>
      let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 2,S]
      discard <| save `two_le_SfullW p (.proj ``And 0 spec) false (some target)
    | 2 =>
      let value := Expr.proj ``And 1 spec
      let target := (← instantiateMVars (← inferType value)).replace fun e =>
        if e == chosen then some S else none
      unless target.getUsedConstants.contains (root ++ `SfullW) do
        throwError "full initialized field: uniform raw predicate lost named fixed reach"
      discard <| save `raw_profile_exists p value false (some target)
    | _ => throwError "full initialized field: unknown fixed reach publication"
end JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfilesTemplate
end
