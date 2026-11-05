module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalProtected
public import JanetCartan.Iteration.PhysicalInitialization.ColoredRefinementBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.OriginalSignedResidualDecay.SourceAnnulus
public meta import Lean

/-!
# The actual colored refinement of the retained original protection

For `app:defn:exhaustive-pair-groups` and `app:rem:exhaustive-signed-pairs`,
append the finite sampling colors to the SAME original21 protected tuple.
Exactly one angular packet chooses eta and k; all its radial, angular and
true-beat certificates are cached together. The new radial constants are
Rcolor=k*R, aColor=a/4 and AColor=(2*A+a)*colorTotal k. The original physical
ball, projected immersion neighborhood, cones, charts and later operators are
not selected again. Ksource is the explicit radial image of the closed colored
direction set, NOT the old angular compact. It contains the beat-normalized
pair vectors for `PhysicalPairs.CorrectedApplication` (`app:ch_pairs:setup:pairs-lag`).
The remaining fixed-band validation and full-source chain compatibility are
separate parent obligations, not consequences claimed by this module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization.OriginalColoredProtection
open SignedPairs ColoredRefinement ActualCarriers.ConstructedSignedGeometry

/-- Exactly the original sampling color type; its order precedes every source
scale, history and sample (`app:ch_waves:thm:sampling`). -/
abbrev Color (pOrder : ℕ) : Type := Fin 3 → Fin (pOrder+1)

private theorem retainedColorPacket (C : Type) [Fintype C]
    {n : ℕ} {I X : Type} [Finite I]
    (S : I → Set (Euclidean 3)) (f : X → I → Euclidean 3 → Euclidean n)
    (R : I → ℝ) (hR : ∀ i, 1 ≤ R i) (hRi : Function.Injective R)
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A)
    (Ω : Set (Euclidean n)) (hsym : ∀ v ∈ Ω, -v ∈ Ω)
    (hclosure : closure (directionSet f S) ⊆ interior Ω)
    (htrue : ∀ x (q : Pair I (Euclidean 3) S),
      (∀ L ∈ cubeBadSubspaces n, a*q.beat ≤ ‖projectAway L (q.vector (f x))‖) ∧
      q.vector (f x) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
        a*(lam*q.beat) ≤ ‖lam • q.vector (f x)‖ ∧
        ‖lam • q.vector (f x)‖ ≤ A*(lam*q.beat)) :
    let Groups := I × C
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1/4 ∧ ∃ k : C → ℝ,
      (∀ c, 1 ≤ k c) ∧ Function.Injective k ∧
      let Rcolor : Groups → ℝ := fun ic ↦ k ic.2*R ic.1
      (∀ ic, 1 ≤ Rcolor ic) ∧ Function.Injective Rcolor ∧
      (∀ c d, k c < k d → ((A/2+a/2)/(eta*(a/2)))*k c ≤ k d) ∧
      let Scolor : Groups → Set (Euclidean 3) := fun ic ↦ S ic.1
      let family : X → Groups → Euclidean 3 → Euclidean n := fun x ic z ↦ k ic.2 • f x ic.1 z
      closure (directionSet family Scolor) ⊆ interior Ω ∧
      let aColor := a/4
      let AColor := (2*A+a)*colorTotal k
      0 < aColor ∧ 0 < AColor ∧
      ∀ x (q : Pair Groups (Euclidean 3) Scolor),
        (∀ L ∈ cubeBadSubspaces n, aColor*q.beat ≤ ‖projectAway L (q.vector (family x))‖) ∧
        q.vector (family x) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          aColor*(lam*q.beat) ≤ ‖lam • q.vector (family x)‖ ∧
          ‖lam • q.vector (family x)‖ ≤ AColor*(lam*q.beat) := by
  have hpair (x : X) (q : Pair I (Euclidean 3) S) :
      a*q.beat ≤ ‖q.vector (f x)‖ ∧ ‖q.vector (f x)‖ ≤ A*q.beat := by
    simpa only [one_mul, one_smul] using (htrue x q).2.2 1 zero_le_one
  obtain ⟨eta, heta, hetaq, k, hk, hki, hRcolor, hRiColor, hsep, hprotect⟩ :=
    exists_refined_angular_packet (C := C) S f R hR hRi a A ha hA hpair Ω hsym hclosure
  have hbounds := refined_signed_bounds S f a A ha hA hpair
    (fun x q L hL ↦ (htrue x q).1 L hL) k hk hki eta heta hetaq hsep
  exact ⟨eta, heta, hetaq, k, hk, hki, hRcolor, hRiColor, hsep, hprotect,
    hbounds.1, hbounds.2.1, hbounds.2.2⟩

private theorem retainedBandGap {C : Type} [Fintype C]
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A) (k : C → ℝ) (hk : ∀ c, 1 ≤ k c) :
    a/4 < (2*A+a)*colorTotal k := by
  have hsum : 0 ≤ ∑ c, k c := Finset.sum_nonneg (fun c _ ↦ zero_le_one.trans (hk c))
  have htotal : 1 ≤ colorTotal k := by
    dsimp only [colorTotal]
    linarith
  have hpos : 0 ≤ 2*A+a := by positivity
  calc
    a/4 < 2*A+a := by linarith
    _ ≤ (2*A+a)*colorTotal k := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htotal hpos

private theorem retainedSourceAnnulus {n : ℕ} (hn : 5 ≤ n) {I X : Type}
    (family : X → I → Euclidean 3 → Euclidean n) (S : I → Set (Euclidean 3))
    (Ω : Set (Euclidean n)) (hΩ : IsCompact Ω) (a A : ℝ) (ha : 0 < a)
    (hdirection : closure (directionSet family S) ⊆ interior Ω)
    (htrue : ∀ x (q : Pair I (Euclidean 3) S),
      (∀ L ∈ cubeBadSubspaces n, a*q.beat ≤ ‖projectAway L (q.vector (family x))‖) ∧
      q.vector (family x) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
        a*(lam*q.beat) ≤ ‖lam • q.vector (family x)‖ ∧
        ‖lam • q.vector (family x)‖ ≤ A*(lam*q.beat)) :
    let Ksource := (fun p : ℝ × Euclidean n ↦ p.1 • p.2) ''
      (Icc a A ×ˢ (closure (directionSet family S) ∩ sphere 0 1))
    IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ ProtectedFlow.normalizedCovector ξ ∈ interior Ω) ∧
      ∀ x (q : Pair I (Euclidean 3) S), q.beat⁻¹ • q.vector (family x) ∈ Ksource := by
  have hband (x : X) (q : Pair I (Euclidean 3) S) :
      a*q.beat ≤ ‖q.vector (family x)‖ ∧ ‖q.vector (family x)‖ ≤ A*q.beat := by
    simpa only [one_mul, one_smul] using (htrue x q).2.2 1 zero_le_one
  cases n with
  | zero => omega
  | succ d =>
    exact ArbitraryAccuracy.SelectedLocalization.original_supplied_signed_source_annulus_interior
      family S hΩ ha hdirection hband

private theorem nativeCurrent_color {n : ℕ} {D : FrozenMenu.CoverData n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (C : Type) (k : C → ℝ)
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {I : Type} (assign : I → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : I → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius)
      6 (Q - fun _ ↦ cubeStress n) < (T i).family.threshold) (x : Euclidean n) :
    (fun (ic : I × C) z ↦ k ic.2 • currentGroup T assign R Q hQ hlow x ic.1 z) =
      currentGroup T (fun ic : I × C ↦ assign ic.1) (fun ic ↦ k ic.2*R ic.1) Q hQ hlow x := by
  funext ic z
  simp only [currentGroup, mul_smul]

end JanetCartan.PhysicalInitialization.OriginalColoredProtection
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalColoredProtection
open Lean Meta Elab Command
open OriginalProtectedTemplate

/-- Build only from the verified original21 declarations. The single combined
packet retains every certificate before anything is projected or named. -/
elab "construct_retained_original_color_packet" : command => liftTermElabM do
  let old := `JanetCartan.PhysicalInitialization.OriginalProtected
  let ns := `JanetCartan.PhysicalInitialization.OriginalColoredProtection
  let info ← getConstInfo (old ++ `signed_protection)
  forallBoundedTelescope info.type (some 21) fun xs _ => do
    unless xs.size == 21 do throwError "retained color packet: expected exact original21 prefix"
    withLocalDeclD `pOrder (mkConst ``Nat) fun pOrder => do
      let params := xs.push pOrder
      let get (name : Name) := mkAppN (mkConst (old ++ name)) xs
      let C ← mkAppM ``Color #[pOrder]
      let D ← mkAppM ``PhysicalSeed.OriginalBoundary.D #[xs[1]!]
      let S ← mkAppM ``ActualCarriers.ConstructedSignedGeometry.groupCube #[D, get `assign]
      let h ← mkAppM ``retainedColorPacket #[C, S, get `family, get `R, get `fact0, get `fact1,
        get `a, get `A, get `fact6, get `fact7, get `Ω₀, get `fact18, get `fact28, get `fact29]
      let actual ← store (ns ++ `colored_protection) params h
      select ns params actual
      for (name, index) in #[(`eta_pos, 0), (`eta_le_quarter, 1), (`scale_ge_one, 2),
          (`scale_injective, 3), (`radial_ge_one, 4), (`radial_injective, 5),
          (`scale_separation, 6), (`protected_directions, 7), (`aColor_pos, 8), (`AColor_pos, 9)] do
        discard <| store (ns ++ name) params
          (mkAppN (mkConst (ns ++ Name.mkSimple s!"fact{index}")) params)
      discard <| store (ns ++ `signed_bounds) params (mkAppN (mkConst (ns ++ `continuation)) params)
      let colored (name : Name) := mkAppN (mkConst (ns ++ name)) params
      let gap ← mkAppM ``retainedBandGap
        #[get `a, get `A, get `fact6, get `fact7, colored `k, colored `scale_ge_one]
      let gapType ← mkAppM ``LT.lt #[colored `aColor, colored `AColor]
      discard <| store (ns ++ `aColor_lt_AColor) params gap false (some gapType)
      let sourceProof ← mkAppM ``retainedSourceAnnulus
        #[xs[1]!, colored `family, colored `Scolor, get `Ω₀, get `fact11,
          colored `aColor, colored `AColor, colored `aColor_pos,
          colored `protected_directions, colored `signed_bounds]
      let .letE _ _ sourceValue sourceBody _ ← inferType sourceProof
        | throwError "retained color packet: expected the explicit source-annulus let, not a new choice"
      let Ksource ← store (ns ++ `Ksource) params sourceValue true
      let sourceSpec ← store (ns ++ `source_annulus) params sourceProof false
        (some (sourceBody.instantiate1 Ksource))
      discard <| store (ns ++ `source_compact) params (.proj ``And 0 sourceSpec)
      discard <| store (ns ++ `source_normalized_interior) params
        (.proj ``And 0 (.proj ``And 1 sourceSpec))
      discard <| store (ns ++ `normalized_pair_mem_source) params
        (.proj ``And 1 (.proj ``And 1 sourceSpec))
      let groups := mkAppN (mkConst (ns ++ `Groups)) params
      let assign ← withLocalDeclD `ic groups fun ic =>
        mkLambdaFVars #[ic] (mkApp (get `assign) (.proj ``Prod 0 ic))
      let assign ← store (ns ++ `assign) params assign true
      let oldFamily := get `family
      let .forallE _ pointType _ _ ← whnf (← inferType oldFamily)
        | throwError "retained color packet: native family lost its original physical index"
      withLocalDeclD `z pointType fun z => do
        let familyBody := ((← getConstInfo (old ++ `family)).value! (allowOpaque := true)).beta xs
        let native ← zetaReduce (familyBody.beta #[z])
        unless native.isAppOfArity ``ActualCarriers.ConstructedSignedGeometry.currentGroup 12 do
          throwError "retained color packet: expected literal native currentGroup, got {native}"
        let args := native.getAppArgs
        let T ← mkAppM ``PhysicalSeed.OriginalBoundary.T #[xs[1]!]
        unless ← isDefEq args[4]! T do
          throwError "retained color packet: native patch family changed"
        unless ← isDefEq args[6]! (get `assign) do
          throwError "retained color packet: native original group assignment changed"
        unless ← isDefEq args[7]! (get `R) do
          throwError "retained color packet: native original radial map changed"
        unless ← isDefEq args[11]! (.proj ``Subtype 0 (.proj ``Prod 1 z)) do
          throwError "retained color packet: native original physical point changed"
        let k := mkAppN (mkConst (ns ++ `k)) params
        let Rcolor := mkAppN (mkConst (ns ++ `Rcolor)) params
        let current ← mkAppM ``ActualCarriers.ConstructedSignedGeometry.currentGroup
          #[T, assign, Rcolor, args[8]!, args[9]!, args[10]!, args[11]!]
        let proof ← mkAppM ``nativeCurrent_color
          #[C, k, T, get `assign, get `R, args[8]!, args[9]!, args[10]!, args[11]!]
        let target ← mkEq (mkApp (mkAppN (mkConst (ns ++ `family)) params) z) current
        unless ← isDefEq (← inferType proof) target do
          throwError "retained color packet: literal colored/native family coupling mismatch"
        discard <| store (ns ++ `family_eq_currentGroup) params
          (← mkLambdaFVars #[z] proof) false (some (← mkForallFVars #[z] target))
  logInfo "original21 plus pOrder: one retained eta/k packet, SAME old family/cones, exact Rcolor and all true-beat bounds; native currentGroup/radial/assignment/physical-point guards passed"

construct_retained_original_color_packet

end JanetCartan.PhysicalInitialization.OriginalColoredProtection
end
