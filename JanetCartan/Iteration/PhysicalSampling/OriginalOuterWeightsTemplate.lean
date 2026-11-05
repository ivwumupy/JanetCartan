module

public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public import JanetCartan.Iteration.PhysicalSampling.OriginalExternalWeights
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Geometry
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# Fixed external-weight consequences for the original finite sampler

Consumer: the original outer-weight physical mean and its unchanged inner
normal comparison (`app:ch_background:eq:bg-affine-mean`,
`app:ch_waves:eq:sampling-prefix-normal`). The supplied external cutoff is the
ONE static original cutoff selected by `PhysicalBackground.OriginalOuterCutoff`;
this file never selects a cutoff. Only the bounding cube may be enlarged, once,
before any current history. The sample mesh, window, global shifts and nodes
are not changed. All actual original-data specializations belong to
`OriginalOuterWeights`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalSampling.OriginalOuterWeightsTemplate
open ContinuumRow CanonicalCarrier CanonicalConic Sampling SeparatedSampling OriginalExternalWeights

/-- The supplied external cutoff squared in the original sampling coordinates.
This data is exposed because the actual original22 weight unfolds to it in the
fixed-source mean (`app:ch_background:eq:bg-affine-mean`). -/
def outerSquare (χ : CarrierParameter → ℝ) : Point → ℝ :=
  fun z ↦ (χ (carrierSamplingEquiv.symm z))^2

private theorem outer_smooth {χ : CarrierParameter → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (outerSquare χ) := by
  exact (hχ.comp carrierSamplingLinearEquiv.symm.toContinuousLinearEquiv.contDiff).pow 2

private theorem outer_compact {χ : CarrierParameter → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (outerSquare χ) := by
  exact (hχ.comp_homeomorph
    carrierSamplingLinearEquiv.symm.toContinuousLinearEquiv.toHomeomorph).comp_left
      (g := fun s : ℝ ↦ s^2) (by norm_num)

/-- The only new choice is one bounding cube, not another cutoff, sample or
inverse. It contains the old inner cube and every actual external support. -/
private theorem common_outer_cube {I : Type} [Fintype I]
    (χ : I → CarrierParameter → ℝ)
    (hχrange : ∀ i z, χ i z ∈ Icc (0 : ℝ) 1)
    (hχcompact : ∀ i, HasCompactSupport (χ i))
    {Binner : ℝ} (hBinner : 0 < Binner) :
    ∃ B > (0 : ℝ), Binner ≤ B ∧ ∀ i, PatchBounds (outerSquare (χ i)) B 1 := by
  classical
  choose b hb hbound using fun i ↦
    (outer_compact (hχcompact i)).isCompact.isBounded.exists_pos_norm_le
  let B := Binner+1+∑ i, b i
  have hsum : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ ↦ (hb i).le
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B, hB, (by dsimp [B]; linarith), ?_⟩
  intro i
  refine ⟨hB.le, fun z ↦ sq_nonneg _, ?_, ?_⟩
  · intro z
    exact (pow_le_pow_left₀ (hχrange i _).1 (hχrange i _).2 2).trans_eq (one_pow 2)
  · intro z hz c
    have hi : b i ≤ ∑ j, b j :=
      Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ i)
    have hbB : b i ≤ B := by dsimp [B]; linarith
    exact (show |z c| ≤ ‖z‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z c).trans
        ((hbound i z (subset_tsupport _ hz)).trans hbB)

private theorem enlarge_inner_cube {φ : Point → ℝ} {Binner B : ℝ}
    (hinner : PatchBounds φ Binner 1) (hB : Binner ≤ B) : PatchBounds φ B 1 :=
  ⟨hinner.radius_nonneg.trans hB, hinner.nonneg, hinner.le_bound,
    fun z hz c ↦ (hinner.support z hz c).trans hB⟩

private theorem inner_samples_eq_common {p : ℕ} {w : ℝ → ℝ}
    {W Binner B h : ℝ} {φ : Point → ℝ}
    (hw : WindowBounds p w W) (hinner : PatchBounds φ Binner 1)
    (hcommon : PatchBounds φ B 1) (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q c, 0 ≤ U q c ∧ U q c < h) :
    samples p Binner φ w h U = samples p B φ w h U := by
  ext a
  rw [mem_samples_iff hw hinner hh hh₁ hU, mem_samples_iff hw hcommon hh hh₁ hU]

/-- Reuse the task72 zero-extension proof at the concrete physical summand:
only enumeration changes, not the inner weight, and zero channels stay zero. -/
private theorem retained_inner_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ z ∈ carrierSupport zRoot (r := r), χ z = 1)
    {p : ℕ} {w : ℝ → ℝ} {W Binner Bouter h : ℝ}
    (hw : WindowBounds p w W)
    (hinner : PatchBounds (originalConicCarrierWeight zRoot hr) Binner 1)
    (houter : PatchBounds (outerSquare χ) Bouter 1)
    (hh : 0 < h) (hh₁ : h ≤ 1) (U : Lattice → Point)
    (hU : ∀ q c, 0 ≤ U q c ∧ U q c < h) (H : Sample → V) :
    (∑ a ∈ samples p Binner (originalConicCarrierWeight zRoot hr) w h U,
      weight (originalConicCarrierWeight zRoot hr) w h U a • H a) =
    ∑ a ∈ samples p Bouter (outerSquare χ) w h U,
      weight (outerSquare χ) w h U a •
        (originalConicCarrierWeight zRoot hr (node h U a) • H a) := by
  calc
    _ = ∑ a ∈ samples p Bouter (outerSquare χ) w h U,
        weight (originalConicCarrierWeight zRoot hr) w h U a • H a := by
      apply Finset.sum_subset
        (samples_subset_external zRoot hr χ hχ hw hinner houter hh hh₁ U hU)
      intro a _ ha
      have hz : weight (originalConicCarrierWeight zRoot hr) w h U a = 0 := by
        by_contra hne
        exact ha ((mem_samples_iff hw hinner hh hh₁ hU).mpr hne)
      rw [hz, zero_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ, mul_comm, mul_smul]
      rfl

private theorem outer_nonzero_parameter {χ : CarrierParameter → ℝ} {R : ℝ}
    (hχ : MapsTo parameter (tsupport χ) (FrozenMenu.parameterInterior R))
    (z : Point) (hz : outerSquare χ z ≠ 0) :
    WithLp.toLp 2 z ∈ FrozenMenu.parameterInterior R := by
  have hne : χ (carrierSamplingEquiv.symm z) ≠ 0 := by
    intro he
    apply hz
    simp [outerSquare, he]
  have hp := hχ (subset_tsupport χ hne)
  have he : parameter (carrierSamplingEquiv.symm z) = WithLp.toLp 2 z := by
    obtain ⟨q, rfl⟩ := carrierSamplingEquiv.surjective z
    rw [carrierSamplingEquiv.symm_apply_apply, parameter_apply]
    ext c
    fin_cases c <;> rfl
  exact he ▸ hp

private theorem outer_weight_parameter {χ : CarrierParameter → ℝ} {R : ℝ}
    (hχ : MapsTo parameter (tsupport χ) (FrozenMenu.parameterInterior R))
    (w : ℝ → ℝ) (h : ℝ) (U : Lattice → Point) (a : Sample)
    (ha : weight (outerSquare χ) w h U a ≠ 0) :
    WithLp.toLp 2 (node h U a) ∈ FrozenMenu.parameterInterior R :=
  outer_nonzero_parameter hχ _ (weight_ne_zero_factors ha).1

end JanetCartan.PhysicalSampling.OriginalOuterWeightsTemplate
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalOuterWeightsTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private partial def fixInputsAux (source : Name) (type : Expr)
    (args bound : Array Expr) (remaining : Array (Name × Expr)) : MetaM Expr := do
  let type ← whnf type
  if let .forallE name domain body bi := type then
    let short := name.eraseMacroScopes
    if let some (_, value) := remaining.find? (fun p ↦ p.1 == short) then
      unless ← isDefEq (← inferType value) domain do
        throwError "original outer weights: wrong actual input {source}.{short}"
      fixInputsAux source (body.instantiate1 value) (args.push value) bound
        (remaining.filter (fun p ↦ p.1 != short))
    else
      withLocalDecl name bi domain fun x ↦
        fixInputsAux source (body.instantiate1 x) (args.push x) (bound.push x) remaining
  else
    unless remaining.isEmpty do
      throwError "original outer weights: unused actual specialization fields for {source}"
    mkLambdaFVars bound (mkAppN (mkConst source) args)

/-- Fix only named original inputs of an existing proved consequence. All
remaining ordinary window/shift/summand arguments retain their exact telescope;
no new analytic field or typeclass witness is invented. -/
private def fixInputs (source : Name) (fixed : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "original outer weights: unexpected universe-polymorphic fixed interface {source}"
  fixInputsAux source info.type #[] #[] fixed

/-- Apply exactly one sampling cap and one strong cap to original22, then reuse
74's ONE original21 cutoff. Only a common bounding cube is selected here. -/
elab "construct_original_outer_weights" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalSampling.OriginalOuterWeights
  let source := `JanetCartan.PhysicalBackground.OriginalOuterCutoff
  let indexName := `JanetCartan.PhysicalSampling.OriginalWeights.Index
  let info ← getConstInfo indexName
  forallTelescope info.type fun all result ↦ do
    unless all.size == 22 && result.isSort do
      throwError "original outer weights: expected exact original22 index ABI"
    let n := (← inferType all[1]!).getAppArgs.back!
    unless ← isDefEq n (mkApp (mkConst ``Nat.succ) all[0]!) do
      throwError "original outer weights: physical dimension is not m+1"
    let merged := mkAppN (mkConst ``samplingCappedExtra)
      #[all[0]!, all[1]!, all[2]!, all[21]!]
    let capped := mkAppN (mkConst ``PhysicalNormalInverse.strongCappedExtra)
      #[n, all[1]!, merged]
    let native := (#[n, all[1]!] ++ all[3:22].toArray).set! 20 capped
    unless native.size == 21 do
      throwError "original outer weights: exact strong selected21 reconstruction failed"
    let index ← store (ns ++ `Index) all (mkAppN (mkConst indexName) all) true
    let get (name : Name) : Expr := mkAppN (mkConst (source ++ name)) native
    let rawχ := get `χ
    let .forallE _ sourceIndex _ _ ← whnf (← inferType rawχ) |
      throwError "original outer weights: original cutoff is not on one finite incidence index"
    unless ← isDefEq sourceIndex index do
      throwError "original outer weights: original74 index is not SAME once-capped OriginalWeights.Index"
    discard <| store (ns ++ `index_eq_outer_source) all (← mkEqRefl index)
      false (some (← mkEq sourceIndex index))
    let χ ← store (ns ++ `χ) all rawχ true
    let some χbody := (← getConstInfo (source ++ `χ)).value? |
      throwError "original outer weights: actual74 cutoff getter has no definition"
    let chosenχ ← Core.betaReduce (χbody.beta native)
    let mut replacements : Array (Expr × Expr) := #[(sourceIndex, index), (rawχ, χ), (chosenχ, χ)]
    for name in #[`root, `a, `parameterRadius, `Voriginal, `window] do
      let value := get name
      let target := (← inferType value).replace fun e ↦
        replacements.findSome? fun pair ↦ if e == pair.1 then some pair.2 else none
      let retained ← store (ns ++ name) all value true (some target)
      replacements := replacements.push (value, retained)
    for name in #[`smooth, `range, `compact, `support_original, `support_parameter,
        `support_signed, `plateau, `on_carrier, `finite] do
      let proof := get name
      let target := (← inferType proof).replace fun e ↦
        replacements.findSome? fun pair ↦ if e == pair.1 then some pair.2 else none
      discard <| store (ns ++ Name.mkSimple s!"χ_{name}") all proof false (some target)
    let localField (name : Name) : Expr := mkAppN (mkConst (ns ++ name)) all
    let ψ ← withLocalDeclD `i index fun i ↦ do
      let value ← mkAppM ``outerSquare #[mkApp χ i]
      store (ns ++ `ψ) all (← mkLambdaFVars #[i] value) true
    let replaceData (type : Expr) : Expr := type.replace fun e ↦
      if e.isAppOfArity ``outerSquare 1 && e.appArg!.isApp && e.appArg!.appFn! == χ then
        some (mkApp ψ e.appArg!.appArg!)
      else replacements.findSome? fun pair ↦ if e == pair.1 then some pair.2 else none
    let oldB := mkAppN (mkConst ``OriginalWeights.B) all
    let oldHB := mkAppN (mkConst ``OriginalWeights.hB) all
    let packet ← mkAppM ``common_outer_cube
      #[χ, localField `χ_range, localField `χ_compact, oldHB]
    let packet ← store (ns ++ `exists_cube) all packet false (some (replaceData (← inferType packet)))
    let B ← store (ns ++ `B) all (← mkAppM ``Classical.choose #[packet]) true
    let hspec ← mkAppM ``Classical.choose_spec #[packet]
    let .lam _ _ predicate _ := (← whnf (← inferType packet)).appArg! |
      throwError "original outer weights: common cube packet is not its single existential"
    let spec ← store (ns ++ `cube_spec) all hspec false (some (predicate.instantiate1 B))
    discard <| store (ns ++ `hB) all (.proj ``And 0 spec)
    let hinc ← store (ns ++ `inner_B_le) all (.proj ``And 0 (.proj ``And 1 spec))
    let hb ← store (ns ++ `patchBounds) all (.proj ``And 1 (.proj ``And 1 spec))
    let one ← mkNumeral (mkConst ``Real) 1
    let inner := mkAppN (mkConst ``OriginalWeights.φ) all
    let innerBounds := mkAppN (mkConst ``OriginalWeights.patchBounds) all
    let hρ := mkAppN (mkConst ``PhysicalSeed.SelectedBoundary.ha') native
    withLocalDeclD `i index fun i ↦ do
      let save (name : Name) (proof : Expr) : MetaM Unit := do
        discard <| store (ns ++ name) all (← mkLambdaFVars #[i] proof)
          false (some (← mkForallFVars #[i] (replaceData (← inferType proof))))
      save `smooth (← mkAppM ``outer_smooth #[mkApp (localField `χ_smooth) i])
      save `compact (← mkAppM ``outer_compact #[mkApp (localField `χ_compact) i])
      let innerCommon ← mkAppM ``enlarge_inner_cube #[mkApp innerBounds i, hinc]
      save `inner_patchBounds innerCommon
      let common : Array (Name × Expr) := #[( `zRoot, mkApp (localField `root) i),
        (`r, mkApp (localField `a) i), (`hr, mkApp hρ i), (`χ, mkApp χ i),
        (`hχ, mkApp (localField `χ_on_carrier) i)]
      save `inner_weight_eq (← fixInputs ``OriginalExternalWeights.weight_eq_carrier_weight_mul_external common)
      save `sqrt_inner_weight_eq (← fixInputs ``OriginalExternalWeights.sqrt_weight_eq_carrier_cutoff_mul_external common)
      let bounds := common ++ #[(`p, all[2]!), (`Binner, oldB), (`Bouter, B),
        (`hinner, mkApp innerBounds i), (`houter, mkApp hb i)]
      save `samples_subset (← fixInputs ``OriginalExternalWeights.samples_subset_external
        (bounds.push (`Pouter, one)))
      save `geometry (← fixInputs ``Sampling.Realization.sampleGeometry_of_admissible
        #[(`p,all[2]!), (`B,B), (`P,one), (`ψ,mkApp ψ i), (`hψ,mkApp hb i)])
      save `inner_sum_eq_outer (← fixInputs ``retained_inner_sum bounds)
      save `inner_samples_eq_common (← fixInputs ``inner_samples_eq_common
        #[(`p, all[2]!), (`Binner, oldB), (`B, B), (`φ, mkApp inner i),
          (`hinner, mkApp innerBounds i), (`hcommon, innerCommon)])
      save `nonzero_parameter (← fixInputs ``outer_nonzero_parameter
        #[(`χ, mkApp χ i), (`R, mkApp (localField `parameterRadius) i),
          (`hχ, mkApp (localField `χ_support_parameter) i)])
      save `weight_parameter (← fixInputs ``outer_weight_parameter
        #[(`χ, mkApp χ i), (`R, mkApp (localField `parameterRadius) i),
          (`hχ, mkApp (localField `χ_support_parameter) i)])
  logInfo "original22 outer weights: SAME original74 χ, sampling then strong cap ONCE, SAME original index, one prehistory common cube, exact zero-safe μ/sqrtμ/index/sum identities; no shift or inverse chosen"

end JanetCartan.PhysicalSampling.OriginalOuterWeightsTemplate
end
