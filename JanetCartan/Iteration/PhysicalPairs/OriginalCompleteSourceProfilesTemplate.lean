module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNative
/-! # Genuine physical R-jets of the actual complete source summand

The native profile has already been proved from the SAME finite Sobolev source
profile. Transport that estimate to the physical D in the complete amplitude
split, on the unchanged entire source chart. The source bound is not replaced
by a K ceiling or a physical oscillatory derivative bound. Its actual Picard
producer and fixed h-cap remain explicit completion obligations
(`main:eq:mean-final-amplitude`, `main:prop:pairs`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles
/-- No global regularity for the unobserved physical summand is required.
Its whole-chart germ is sufficient to transfer the full native inverse jets. -/
theorem physical_jets_of_native {n N : ℕ} {S D : Euclidean n → Matrix (Fin N) (Fin n) ℂ}
    {U : Set (Euclidean n)} (hU : IsOpen U) (heq : EqOn S D U)
    (hD : ContDiff ℝ ∞ D) (s : ℕ) (price : ℝ)
    (hprofile : ∀ K : Set (Euclidean n), cNorm K s D ≤ price) :
    ContDiffOn ℝ ∞ S U ∧ ∀ x ∈ U, ‖iteratedFDeriv ℝ s S x‖ ≤ price := by
  refine ⟨hD.contDiffOn.congr (fun _ hx ↦ heq hx), ?_⟩
  intro x hx
  have hmem : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hg : S =ᶠ[𝓝 x] D := hmem.mono (fun _ hy ↦ heq hy)
  rw [(hg.iteratedFDeriv ℝ s).eq_of_nhds]
  exact (norm_iteratedFDeriv_le_cNorm isCompact_singleton (hD.of_le (by simp))
    (mem_singleton x) le_rfl).trans (hprofile {x})
end JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles
end
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalCompleteSourceProfilesTemplate
open Lean Meta Elab Command
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "profile_original_complete_source_amplitude" : command => liftTermElabM do
  let native := `JanetCartan.PhysicalPairs.OriginalSourceNative
  let identity := `JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentity
  let ci ← getConstInfo (native ++ `profile_statement)
  forallBoundedTelescope ci.type (some 64) fun p _ => do
    unless p.size == 64 do throwError "physical source profile: native53/source/sample/profile9 changed"
    let h := app (native ++ `source_cNorm_profile) p
    let nativeStatement ← Core.betaReduce (← zetaReduce ((ci.value! (allowOpaque := true)).beta p))
    unless nativeStatement.isAppOfArity ``And 2 do throwError "physical source profile: native regularity/profile conjunction changed"
    let hd := Expr.proj ``And 0 h
    let hp := Expr.proj ``And 1 (.proj ``And 1 h)
    let pre := p[:55].toArray
    let same := app (identity ++ `source_eq_native) pre
    let pointType ← inferType same
    forallBoundedTelescope pointType (some 2) fun point _ => do
      unless point.size == 2 do throwError "physical source profile: original chart tail changed"
      let chart := (← inferType point[1]!).getAppArgs[3]!
      unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
        throwError "physical source profile: not the SAME full source chart"
      let n := (← inferType point[0]!).appArg!
      let S := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.sourceAmplitude
        (p[:50].toArray ++ #[p[52]!,p[53]!,p[54]!])
      let D := app (identity ++ `nativeAmplitude) pre
      let N := (← inferType S).bindingBody!.getAppArgs[0]!.appArg!
      let price ← forallBoundedTelescope (← inferType hp) (some 1) fun sets bound => do
        unless sets.size == 1 && bound.isAppOfArity ``LE.le 4 do
          throwError "physical source profile: native all-set Cnorm profile changed"
        let price := bound.appArg!
        if (price.find? (· == sets[0]!)).isSome then throwError "physical source profile: cost depends on physical set"
        pure price
      let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles.physical_jets_of_native
        #[n,N,S,D,chart,app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open chart.getAppArgs,
          same,hd,p[55]!,price,hp]
      let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
      let value ← instantiateMVars (← mkLambdaFVars p proof)
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "physical source profile: unresolved chart/source profile"
      let pair := Lean.ShareCommon.shareCommon (type,value)
      let name := `JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles.source_jets
      liftM <| IO.eprintln "physical source profile: kernel checking actual source D64"
      addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
      addDocStringCore name "The actual complete-source physical amplitude has all-order chart regularity and genuine C_s(M)*h*R^s spatial jets from its SAME finite source Sobolev profile through s+n+2, using the original global inverse Q0 (main:prop:pairs, main:eq:mean-final-amplitude)."
      liftM <| IO.eprintln "physical source profile: kernel passed actual source D64"
end JanetCartan.PhysicalPairs.OriginalCompleteSourceProfilesTemplate
end
