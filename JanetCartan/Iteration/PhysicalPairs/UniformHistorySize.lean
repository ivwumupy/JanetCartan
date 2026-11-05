module

public import JanetCartan.Iteration.PhysicalPairs.LocalHistorySize
public import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# One genuine physical size threshold before every amplitude price

The unchanged retained coefficient and reconstruction producers choose Tc/Tg
before the complete-node budget C. Their maximum is ONE initial threshold,
independent of later Picard accuracy N and all later histories/targets/smoothing.
Only D is chosen after C. This repeats the exact geometric/response deduction
of LocalHistorySize with its actual witness in the correct quantifier order;
no profile estimate, later-stage reach or new geometry is assumed
(`main:prop:pairs`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric MeasureTheory FourierTransform
open scoped SchwartzMap NNReal ENNReal ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open SignedProductEstimates
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse Pseudodifferential
open ResponseTransfer ResponseTransfer.RetainedFactors JanetCartan.Localization
open GeometricProfile RegularSector.FiniteEvolution CurrentCoefficientProfiles ProtectedFlow
open ArbitraryAccuracy.ResidualLocalization ProjectedStressFrame
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
variable {ι : Type*}

end JanetCartan.PhysicalPairs
end
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory FourierTransform
open scoped SchwartzMap NNReal ENNReal ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open Lean Meta Elab Command
open SignedProductEstimates RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse Pseudodifferential
open ResponseTransfer ResponseTransfer.RetainedFactors JanetCartan.Localization
open GeometricProfile RegularSector.FiniteEvolution CurrentCoefficientProfiles ProtectedFlow
open ArbitraryAccuracy.ResidualLocalization ProjectedStressFrame
run_elab do
  let ci ← getConstInfo ``exists_physical_history_localized_normalized_product_size_constants
  forallTelescope ci.type fun p old => do
    let mut named : List (Name × Expr) := []
    let mut early := #[]
    let mut amplitude := #[]
    for x in p do
      let nm := (← x.fvarId!.getDecl).userName
      if nm == `C || nm == `hC then amplitude := amplitude.push x
      else
        early := early.push x
        named := named ++ [(nm,x)]
    unless amplitude.size == 2 && old.isAppOfArity ``Exists 2 do
      throwError "early size: original amplitude-price/existential interface changed"
    let ea := old.getAppArgs
    let target ← withLocalDeclD `threshold ea[0]! fun T => do
      let body := ea[1]!.beta #[T]
      unless body.isAppOfArity ``And 2 do throwError "early size: threshold lower bound changed"
      let after ← mkForallFVars amplitude body.getAppArgs[1]!
      let spec ← mkAppM ``And #[body.getAppArgs[0]!,after]
      let pred ← mkLambdaFVars #[T] spec
      pure (mkAppN old.getAppFn #[ea[0]!,pred])
    let proof ← PhysicalBackground.NativeReferenceSourceTemplate.termWith named "by\n  obtain ⟨Tc, hTc, AQ, AB, hAQ, hAB, hcoeff⟩ :=\n    PhysicalGeometry.exists_retained_coefficient_profiles Gref hr hrR hR ext\n      hextcenter hextradius hCband hStar hreserve horder\n  obtain ⟨Tg, hTg, Cgeom, hCgeom, hgeom⟩ :=\n    exists_physical_history_reconstruction_entry_profiles Gref hr hrR hR\n      hCband hStar (reserve := 0) (by omega) horder\n  refine ⟨max Tc Tg, hTc.trans (le_max_left _ _), ?_⟩\n  intro C hC\n  let Cg := fun q ↦ 1 + Cgeom q\n  have hCg q : 1 ≤ Cg q := le_add_of_nonneg_right (hCgeom q)\n  obtain ⟨D, hD, hsize⟩ := exists_localized_normalized_product_completedVariation_physicalWeighted_size_constants\n    (N := embeddingDimension (d+1)) (ι := ι) f hK L₀ output ho hob χ₂ χ₃ ψ hψ hψc\n    hnorm hbuffer hS P X Y AQ AB C Cg responseCost hP hX hY hAQ hAB hC hCg\n    hresponseCost hCfreq hlowReserve\n  refine ⟨D, hD, ?_⟩\n  intro R₀ hR₀ j u ell hu F Q B\n  have hcR : Tc ≤ R₀ := (le_max_left _ _).trans hR₀\n  have hgR : Tg ≤ R₀ := (le_max_right _ _).trans hR₀\n  obtain ⟨hQ, hB, hQB⟩ := hcoeff R₀ hcR j u ell hu\n  obtain ⟨hv, hd, hs⟩ := hgeom R₀ hgR j u ell hu\n  have hLc : 1 ≤ currentCoefficientScale R₀ j :=\n    one_le_currentCoefficientScale ((by norm_num : (1 : ℝ) ≤ 2).trans (hTc.trans hcR)) j\n  have hentry {a : Euclidean (d+1) → ℂ} (hasm : ∀ x ∈ closedBall 0 r, ContDiffAt ℝ ∞ a x)\n      (hap : HasDerivativeProfile (closedBall 0 r) a 0 (currentCoefficientScale R₀ j) Cgeom) :\n      ContDiffOn ℝ ∞ a (ball 0 r) ∧\n      ∀ q, ∀ x ∈ ball (0 : Euclidean (d+1)) r,\n        ‖iteratedFDeriv ℝ q a x‖ ≤ Cg q * currentCoefficientScale R₀ j ^ q := by\n    refine ⟨fun x hx ↦ (hasm x (ball_subset_closedBall hx)).contDiffWithinAt, ?_⟩\n    intro q x hx\n    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)\n      (fun y hy ↦ (hasm y hy).of_le (by simp)) (ball_subset_closedBall hx) le_rfl).trans\n    apply (hap q).trans\n    simp only [Nat.sub_zero]\n    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)\n      (pow_nonneg (zero_le_one.trans hLc) q)\n  have hv' l k := hentry (hv l k).1 (hv l k).2\n  have hd' l ik := hentry (hd l ik).1 (hd l ik).2\n  have hs' l ik := hentry (hs l ik).1 (hs l ik).2\n  refine ⟨hQ, hB, ?_⟩\n  intro W uQ uB coeff β W₁ retarded Krecut Corr htame Lpair lam ρ hL hLlam hρ hρlam\n  exact hsize (currentCoefficientScale R₀ j) Lpair lam ρ hLc hL hLlam hρ hρlam\n    Q B hQ hB (hQB (closedBall center profileRadius) (isCompact_closedBall _ _)).1\n    (hQB (closedBall center profileRadius) (isCompact_closedBall _ _)).2\n    W₁ retarded htame F (ball 0 r) isOpen_ball hψr\n    (fun l k ↦ (hv' l k).1) (fun l ik ↦ (hd' l ik).1) (fun l ik ↦ (hs' l ik).1)\n    (fun l k ↦ (hv' l k).2) (fun l ik ↦ (hd' l ik).2) (fun l ik ↦ (hs' l ik).2)\n" (some target)
    let type ← instantiateMVars (← mkForallFVars early target)
    let value ← instantiateMVars (← mkLambdaFVars early proof)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "early size: unresolved actual coefficient/reconstruction proof"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.PhysicalPairs.exists_uniform_threshold_physical_history_localized_product_size_constants
    IO.println "Kernel checking one physical size threshold BEFORE all C/N"
    (← IO.getStdout).flush
    addDecl (.thmDecl {name,levelParams := ci.levelParams,type,value}) (forceExpose := true)
    addDocStringCore name "The actual retained-coefficient/reconstruction threshold is chosen before every later full-amplitude budget C and Picard accuracy N; only the all-order size price depends on C. SAME history, current, cutoffs and response (main:prop:pairs; new:sec:order-of-choices)."
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "early size: nonstandard axioms {axioms}"
    logInfo m!"one physical size threshold BEFORE all C/N: {axioms}"
end JanetCartan.PhysicalPairs
end
