module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredFrequencies
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ScaleGap
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# The original common-shift signed pair in its physical fine-scale window

The external sample's actual separation is **half** a mesh. At one threshold
before histories, shifts, signs, and orders, the literal product frequency
`R_j^carrierExponent * pair.beat` dominates the entire fine envelope and the
original history coefficient scale. The same chosen `pair` supplies the scalar
sum/difference identity and the angular conclusion on the whole original χ₂
support. No point of that support, second shift, new pair, or success event is
selected (`main:eq:all-pair-scales`, `main:prop:pairs`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalWindow

/-- The complete fine envelope, including its fixed prefactor, not the coarse
carrier or the true signed beat (`app:ch_pairs:eq:pairs-lag-envelope`). -/
def fineScale (C R : ℝ) : ℝ := max 1 C * R^(1+meanSlack)

theorem scale_exists (C : ℝ) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R ≥ S, ∀ ρ L : ℝ,
      (1/2:ℝ) * (R^carrierExponent * R^(-separationExponent)) ≤ ρ →
      L ≤ max 1 C * R^(1+meanSlack) → 2 ≤ ρ ∧ L ≤ ρ^(1-1/1000 : ℝ) :=
  SignedProductEstimates.exists_signed_pair_scale_threshold (c := (1/2:ℝ)) (by norm_num) (max 1 C)

/-- One numerical threshold, before the original graph's reached history and
before the common external shift (`main:eq:all-pair-scales`). -/
def scaleThreshold (C : ℝ) : ℝ := Classical.choose (scale_exists C)

theorem two_le_scaleThreshold (C : ℝ) : 2 ≤ scaleThreshold C :=
  (Classical.choose_spec (scale_exists C)).1

/-- The numeric stage bound used by the native sampled pair. Keeping this
proof public avoids putting an imported private proof in a public pair type. -/
theorem stage_one (C R₀ : ℝ) (hR₀ : scaleThreshold C ≤ R₀) (j : ℕ) :
    1 ≤ historyScale R₀ growthExponent j := by
  have h : 1 ≤ R₀ := (by norm_num : (1:ℝ) ≤ 2).trans ((two_le_scaleThreshold C).trans hR₀)
  exact h.trans (le_historyScale h j)

/-- Apply the fixed half-mesh threshold at an actual history stage. The complete
fine envelope itself is estimated, with no assumed inequality on an invented
pair scale (`main:eq:all-pair-scales`). The sampled-pair application below
supplies the beat bound from the native geometric `pair_spec`. -/
theorem history_pair_window (C R₀ : ℝ) (hR₀ : scaleThreshold C ≤ R₀) (j : ℕ) (beat : ℝ)
    (hbeat : (historyScale R₀ growthExponent j)^(-separationExponent)/2 ≤ beat) :
    let R := historyScale R₀ growthExponent j
    let ρ := R^carrierExponent * beat
    1 ≤ currentCoefficientScale R₀ j ∧ currentCoefficientScale R₀ j ≤ fineScale C R ∧
      2 ≤ ρ ∧ fineScale C R ≤ ρ^(1-1/1000 : ℝ) ∧ fineScale C R ≤ ρ := by
  intro R ρ
  have h₀ : 1 ≤ R₀ := (by norm_num : (1:ℝ) ≤ 2).trans ((two_le_scaleThreshold C).trans hR₀)
  have hR := h₀.trans (le_historyScale h₀ j)
  have hlower : (1/2:ℝ)*(R^carrierExponent*R^(-separationExponent)) ≤ ρ := by
    calc
      _ = R^carrierExponent*(R^(-separationExponent)/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbeat (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hg := (Classical.choose_spec (scale_exists C)).2 R (hR₀.trans (le_historyScale h₀ j))
    ρ (fineScale C R) hlower le_rfl
  have hL : currentCoefficientScale R₀ j ≤ fineScale C R := by
    calc
      currentCoefficientScale R₀ j = R^coefficientExponent := rfl
      _ ≤ R^(1+meanSlack) := Real.rpow_le_rpow_of_exponent_le hR (by norm_num [coefficientExponent,meanSlack])
      _ = 1 * R^(1+meanSlack) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hρ : 1 ≤ ρ := (by norm_num : (1:ℝ) ≤ 2).trans hg.1
  exact ⟨one_le_currentCoefficientScale h₀ j,hL,hg.1,hg.2,hg.2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hρ (by norm_num : (1-1/1000:ℝ) ≤ 1))⟩

end JanetCartan.PhysicalPairs.OriginalWindow
end

public meta section
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalWindow
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def out := `JanetCartan.PhysicalPairs.OriginalWindow
private def samples := `JanetCartan.PhysicalInitialization.OriginalSampledPairs

/- Rebind only the reached-threshold proof on the existing actual geometric
row. The native scalar signed pair and its common ξ are taken from the type of
the actual angular theorem itself; the loop does not select any witness. -/
run_cmd liftTermElabM do
  let producer := samples ++ `actual_colored_frequency
  forallBoundedTelescope (← getConstInfo producer).type (some 36) fun base rest => do
    unless base.size == 36 do throwError "original pair: changed fixed graph inputs"
    withLocalDeclD `Cscale (mkConst ``Real) fun C => do
      forallBoundedTelescope rest (some 1) fun R₀ next => do
        unless R₀.size == 1 do throwError "original pair: missing original initial scale"
        let .forallE _ reached continuation _ := next | throwError "original pair: missing graph admission"
        unless reached.isAppOfArity ``LE.le 4 do throwError "original pair: changed reached-scale inequality"
        let old := reached.getAppArgs[2]!
        unless old.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
          throwError "original pair: changed native graph threshold"
        let numeric := mkApp (mkConst (out ++ `scaleThreshold)) C
        let pre := base.push C
        let combined ← mkAppM ``max #[old,numeric]
        let S ← store (out ++ `S) pre combined true
        let two ← mkNumeral (mkConst ``Real) 2
        let hleft ← mkAppM `le_max_left #[old,numeric]
        let hright ← mkAppM `le_max_right #[old,numeric]
        let hS ← mkAppM `le_trans #[mkApp (mkConst (out ++ `two_le_scaleThreshold)) C,hright]
        discard <| store (out ++ `hS) pre hS false (some (← mkAppM ``LE.le #[two,S]))
        withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R₀[0]!]) fun hR₀ => do
          let hgraph ← mkAppM `le_trans #[hleft,hR₀]
          let hscale ← mkAppM `le_trans #[hright,hR₀]
          forallBoundedTelescope (continuation.instantiate1 hgraph) (some 10) fun dyn _ => do
            unless dyn.size == 10 do throwError "original pair: changed history/ξ/sign telescope"
            let actual := mkAppN (mkConst producer) (base ++ R₀ ++ #[hgraph] ++ dyn)
            let actualType ← inferType actual
            let some q := actualType.find? (fun e => e.isAppOfArity (samples ++ `pair) 30)
              | throwError "original pair: the external common-ξ pair disappeared from the native angular conclusion"
            let stageProof := mkAppN (mkConst (out ++ `stage_one)) #[C,R₀[0]!,hscale,dyn[0]!]
            let oldProof := q.getAppArgs[24]!
            let args := q.getAppArgs.set! 24 stageProof
            let publicAngular := actualType.replace fun e => if e == oldProof then some stageProof else none
            let spec := mkAppN (mkConst (samples ++ `pair_spec)) args
            let hb := Expr.proj ``And 0 spec
            let beat := (← inferType hb).getAppArgs.back!
            let window := mkAppN (mkConst (out ++ `history_pair_window)) #[C,R₀[0]!,hscale,dyn[0]!,beat,hb]
            let wtype ← inferType window
            let stype ← inferType spec
            let restType := mkApp2 (mkConst ``And) stype publicAngular
            let restProof := mkAppN (mkConst ``And.intro) #[stype,publicAngular,spec,actual]
            let certificate := mkAppN (mkConst ``And.intro) #[wtype,restType,window,restProof]
            discard <| store (out ++ `on_original_sample) (pre ++ R₀ ++ #[hR₀] ++ dyn) certificate false
              (some (mkApp2 (mkConst ``And) wtype restType))
            addDocStringCore (out ++ `on_original_sample) "The actual external signed pair at the SAME inner shift, with the exact half-mesh separation, full scalar signed identity and original chi2 angular result. The original coefficient and full fine scales satisfy the true-frequency 1-1/1000 window, uniformly after one prehistory threshold (main:eq:all-pair-scales; main:prop:pairs)."
  logInfo "original common-ξ signed pair: native scalar/χ₂ angular certificate and actual λ·beat at every reached history, including the half mesh; full fine-scale window 1-1/1000"

end JanetCartan.PhysicalPairs.OriginalWindow
end
