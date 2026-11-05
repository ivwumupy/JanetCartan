module

public import JanetCartan.Iteration.PhysicalBackground.ActualReference
public import JanetCartan.Iteration.PhysicalPrimary.OriginalIncidence
public import JanetCartan.Iteration.PhysicalSampling.OriginalMargins
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Bounds
public meta import Lean

/-!
# Source-scale admissions shared by the positive sampler and source53/graph42

Meet the numerical source caps before σ, without changing the independently
fixed signed γ. Reach every original source39, the chosen graph34 and the
parent's event threshold before R₀. The unchanged graph projects to the weak38
history. The explicit telescopes below avoid re-inferring the selected original
reference at each argument (`new:sec:order-of-choices`,
`app:ch_response:cor:current-atoms`, `main:eq:history-current`).
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.PhysicalSampling.OriginalSourceGraphAdmission

/-- The SAME numerical order covers the native graph, canonical carrier and
all retained initial-label derivative reserves. -/
theorem orders_of_source_reserve {d rStar : ℕ}
    (h : 16 + RawPrimary.SliceBounds.rawSliceParameterOrder (d+1) ≤ rStar) :
    8 ≤ rStar ∧ RegularSector.FiniteEvolution.sectorLowOrder d + 2 ≤ rStar ∧
    ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder (d+1) ≤ rStar := by
  simp only [RawPrimary.SliceBounds.rawSliceParameterOrder,
    RawPrimary.SliceBounds.rawSliceJetOrder] at h
  simp only [RegularSector.FiniteEvolution.sectorLowOrder,
    RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    FourierIntegral.WholeImageGeometry.wholeImagePhaseReserve,
    FourierIntegral.LowBounds.primitiveNormalReserve,
    FourierIntegral.FullLowBounds.fullLowReserve_eq,
    ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder]
  omega

/-- One strict-positive source belongs to all four original intervals. -/
theorem four_admissions {a b c d σ : ℝ} (h : σ ∈ Ioc 0 (min a (min b (min c d)))) :
    σ ∈ Ioc 0 a ∧ σ ∈ Ioc 0 b ∧ σ ∈ Ioc 0 c ∧ σ ∈ Ioc 0 d :=
  ⟨⟨h.1,h.2.trans (min_le_left _ _)⟩,
   ⟨h.1,(h.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩,
   ⟨h.1,((h.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)⟩,
   ⟨h.1,((h.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)⟩⟩

/-- Already-proved original finite maximum, with the reached weak history
kept rather than a second independent history hypothesis. -/
theorem join_source_rows {I : Type} [Fintype I] {G W : ℝ} (parentS : ℝ) (A : I → ℝ)
    (hg : 2 ≤ G) (hweak : ∀ R : ℝ, G ≤ R → W ≤ R) :
    ∃ S : ℝ, 2 ≤ S ∧ parentS ≤ S ∧ G ≤ S ∧ (∀ i, A i ≤ S) ∧
      ∀ R : ℝ, S ≤ R → W ≤ R := by
  obtain ⟨S,hS,rows⟩ := PhysicalInitialization.OriginalRegular.common_graph_threshold (max parentS G) A
  have hG : G ≤ S := (le_max_right _ _).trans hS
  exact ⟨S,hg.trans hG,(le_max_left _ _).trans hS,hG,rows,fun R hR ↦ hweak R (hG.trans hR)⟩

end JanetCartan.PhysicalSampling.OriginalSourceGraphAdmission
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalSourceGraphAdmissionApplication
open Lean Meta Elab Command
private def ps := `JanetCartan.PhysicalSampling
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def graph := reg ++ `Graph
private def signed := `JanetCartan.PhysicalPrimary.OriginalIncidence
private def dest := ps ++ `OriginalSourceGraphAdmission
private def src := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def p0 (e : Expr) := Expr.proj ``And 0 e
private def p1 (e : Expr) := Expr.proj ``And 1 e
private def save (q : Name) (xs : Array Expr) (e : Expr) (data := false) (ty? : Option Expr := none) : MetaM Expr := do
  let t ← instantiateMVars (← mkForallFVars xs (ty?.getD (← inferType e)))
  let v ← instantiateMVars (← mkLambdaFVars xs e)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar ||
      t.hasSorry || v.hasSorry then throwError "original source/graph: open {q}"
  let name := dest ++ q
  if data then addDecl (.defnDecl {name,levelParams := [],type := t,value := v,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type := t,value := v}) (forceExpose := true)
  logInfo m!"checked original source53/graph42 prehistory {q} at {xs.size} inputs"
  return mkAppN (mkConst name) xs

private def withOriginal (l : Nat) (k : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (ps ++ `OriginalMargins.δ)).type (some 22) fun w _ => do
    let n := (← inferType w[1]!).appArg!
    let merge := mkAppN (mkConst (ps ++ `samplingCappedExtra)) #[w[0]!,w[1]!,w[2]!,w[21]!]
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,w[1]!,merge]
    let g := (w[:2].toArray ++ w[3:22].toArray).set! 20 merge
    let native := g.set! 0 n
    forallBoundedTelescope (← inferType (mkAppN (mkConst (graph ++ `cap40)) g)) (some (l-22)) fun extra _ =>
      k (w ++ extra) (g ++ extra[:2].toArray) native (native.set! 20 cap)

elab "select_original_graph_tolerance " i:num : command => liftTermElabM <| withOriginal 24 fun x g _ _ => do
  let δ := mkAppN (mkConst (ps ++ `OriginalMargins.δ)) x[:22].toArray
  let γ := mkAppN (mkConst (signed ++ `Common.γ)) g
  match i.getNat with
  | 0 => discard <| save `graphTolerance x (← mkAppM ``Min.min #[δ,γ]) true
  | 1 =>
    let h ← mkAppM `lt_min #[mkAppN (mkConst (ps ++ `OriginalMargins.hδ)) x[:22].toArray,mkAppN (mkConst (signed ++ `Common.fact0)) g]
    let goal ← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,mkAppN (mkConst (dest ++ `graphTolerance)) x]
    discard <| save `graphTolerance_pos x h false (some goal)
  | 2 =>
    let goal ← mkAppM ``LE.le #[mkAppN (mkConst (dest ++ `graphTolerance)) x,δ]
    discard <| save `graphTolerance_le_sampler x (← mkAppM `min_le_left #[δ,γ]) false (some goal)
  | _ => throwError "source/graph: unknown tolerance field"

private def caps (x g native fixed : Array Expr) : Array Expr :=
  #[mkAppN (mkConst (graph ++ `fact0)) (g ++ x[24:26].toArray),
    mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact1) native,
    mkAppN (mkConst `JanetCartan.PhysicalBackground.original_sourceCap_pos) fixed,
    mkAppN (mkConst (signed ++ `sourceCap_pos)) g]

elab "admit_original_source_graph_caps " i:num : command => liftTermElabM <| withOriginal 26 fun x g native fixed => do
  let h := caps x g native fixed
  let a ← h.mapM fun v => do return (← inferType v).appArg!
  let cap := mkAppN (mkConst (dest ++ `scaleCeiling)) x
  match i.getNat with
  | 0 => discard <| save `scaleCeiling x (← mkAppM ``Min.min #[a[0]!,← mkAppM ``Min.min #[a[1]!,← mkAppM ``Min.min #[a[2]!,a[3]!]]]) true
  | 1 =>
    let hp ← mkAppM `lt_min #[h[0]!,← mkAppM `lt_min #[h[1]!,← mkAppM `lt_min #[h[2]!,h[3]!]]]
    let goal ← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,cap]
    discard <| save `scaleCeiling_pos x hp false (some goal)
  | 2 | 3 =>
    withLocalDeclD `σ (mkConst ``Real) fun σ => do
      let z ← mkNumeral (mkConst ``Real) 0
      let dom ← mkAppM ``Membership.mem #[← mkAppM ``Set.Ioc #[z,cap],σ]
      withLocalDeclD `hσ dom fun hσ => do
        let p := x ++ #[σ,hσ]
        if i.getNat == 2 then
          discard <| save `scale_admissions p (mkAppN (mkConst (dest ++ `four_admissions)) (a ++ #[σ,hσ]))
        else
          let hG := p0 (mkAppN (mkConst (dest ++ `scale_admissions)) p)
          discard <| save `regular_scale p (mkAppN (mkConst (graph ++ `regular_scale)) (g ++ x[24:26].toArray ++ #[σ,hG]))
  | _ => throwError "source/graph: unknown source-scale field"

elab "join_actual_original_source_graph_thresholds" : command => liftTermElabM <| withOriginal 26 fun x g _ _ => do
  let admissions := mkAppN (mkConst (dest ++ `scale_admissions)) x
  forallBoundedTelescope (← inferType admissions) (some 2) fun source _ => do
    let h := mkAppN admissions source
    let gh := g ++ x[24:26].toArray ++ #[source[0]!,p0 h]
    let G := mkAppN (mkConst (graph ++ `S)) gh
    forallBoundedTelescope (← inferType G) (some 4) fun order _ => do
      let n := (← inferType x[1]!).appArg!
      let r := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
      let reserve ← mkAppM ``HAdd.hAdd #[mkNatLit 16,r]
      withLocalDeclD `hreserve (← mkAppM ``LE.le #[reserve,order[2]!]) fun hres => do
        let orders := mkAppN (mkConst (dest ++ `orders_of_source_reserve)) #[x[0]!,order[2]!,hres]
        let oo := order ++ #[p0 orders,p0 (p1 orders)]
        forallBoundedTelescope (← inferType (mkAppN G oo)) (some 1) fun ho _ => do
          let gg := gh ++ oo ++ ho
          let rg := mkAppN (mkConst (graph ++ `regular_reached)) gg
          let hs := mkAppN (mkConst (graph ++ `hS)) gg
          let sourcePre := g ++ #[source[0]!,p0 (p1 h),p0 (p1 (p1 h))] ++ order ++ #[p1 (p1 orders),ho[0]!]
          let SS := mkAppN (mkConst (src ++ `S)) sourcePre
          forallBoundedTelescope (← inferType SS) (some 2) fun low _ => do
            let SS := mkAppN SS low
            let I := mkAppN (mkConst (ps ++ `OriginalWeights.Index)) x[:22].toArray
            withLocalDeclD `i I fun i => do
              let si := mkApp SS i
              let atTy := (← whnf (← inferType si)).bindingDomain!
              withLocalDeclD `Ar (← mkForallFVars #[i] atTy) fun Ar => do
                let si := mkApp si (mkApp Ar i)
                let ht := (← whnf (← inferType si)).bindingDomain!
                withLocalDeclD `hAr (← mkForallFVars #[i] ht) fun hAr => do
                  let rows ← mkLambdaFVars #[i] (mkAppN si #[mkApp hAr i,r,hres])
                  withLocalDeclD `parentS (mkConst ``Real) fun parent => do
                    discard <| save `exists_preHistory_threshold
                      (x ++ source ++ order ++ #[hres,ho[0]!] ++ low ++ #[Ar,hAr,parent])
                      (← mkAppM (dest ++ `join_source_rows) #[parent,rows,hs,rg])

end JanetCartan.PhysicalSampling.OriginalSourceGraphAdmissionApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option Elab.async false
select_original_graph_tolerance 0
select_original_graph_tolerance 1
select_original_graph_tolerance 2
admit_original_source_graph_caps 0
admit_original_source_graph_caps 1
admit_original_source_graph_caps 2
admit_original_source_graph_caps 3
