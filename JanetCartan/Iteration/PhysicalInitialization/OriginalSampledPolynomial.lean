module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledOperatorBounds
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledLeakage
public import JanetCartan.Iteration.PhysicalPrimary.OriginalHistoryFamily
public meta import Lean

/-!
# Polynomial costs on all physical signed-pair histories

Index by **all** actual histories above the common regular-sector and
coefficient threshold. The frequency is the normalized signed product's
frequency, not necessarily its primary carrier. The slow scale stays free
in its signed window. Apply the full measured-factor theorem on this whole
family; the singleton-at-one ordinary estimate is not such a bound.
This is the polynomial cost needed by the observed-power proof of
`app:ch_regular:lem:finite-chain` for `main:prop:pairs`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
open PhysicalPrimary.OriginalHistoryFamily RegularSector.FiniteEvolution
/-- Both thresholds precede every raw history and oscillation frequency. -/
abbrev Histories (d : ℕ) (B : ℝ) (kMin : ℕ) (Sreg Scoeff : ℝ) :=
  {i : RawIndex d Unit // Admitted B kMin (1/1000) (max Sreg Scoeff) i}
/-- On every member of the full family both original thresholds are reached,
    and the true signed frequency dominates the actual slow scale. -/
theorem admitted_data (d : ℕ) (B : ℝ) (kMin : ℕ) (Sreg Scoeff : ℝ)
    (hS : 2 ≤ Scoeff) (i : Histories d B kMin Sreg Scoeff) :
    Sreg ≤ i.1.R₀ ∧ Scoeff ≤ i.1.R₀ ∧ RevisedGlobal.IsAdmissibleHistory B i.1.R₀ kMin i.1.u i.1.ell ∧
    1 ≤ i.1.K ∧ i.1.K ≤ i.1.lam ∧ currentCoefficientScale i.1.R₀ i.1.length ≤ i.1.K := by
  have hs := (le_max_right Sreg Scoeff).trans i.2.1
  exact ⟨(le_max_left Sreg Scoeff).trans i.2.1,hs,i.2.2.1,
    (one_le_currentCoefficientScale ((by norm_num : (1:ℝ) ≤ 2).trans (hS.trans hs)) _).trans i.2.2.2.2.1,
    i.2.2.2.2.2.1.trans (Real.rpow_le_self_of_one_le i.2.2.2.1 (by norm_num)),i.2.2.2.2.1⟩
theorem coefficient_reserve (d rStar : ℕ) (h : sectorLowOrder d + 2 ≤ rStar) :
    2 + sectorLowOrder d ≤ rStar := by simpa only [Nat.add_comm 2] using h
theorem one_le_reserve (d : ℕ) : 1 ≤ sectorLowOrder d := by
  have h := (sectorLowOrder_bounds d).2.2
  omega
theorem range_norm {E : Type} (f : E → ℝ) (h : ∀ y, f y ∈ Set.Icc (0:ℝ) 1) :
    ∀ y, ‖f y‖ ≤ 1 := fun y ↦ (Real.norm_of_nonneg (h y).1).trans_le (h y).2
theorem native_open (n : ℕ) (r : ℝ) : IsOpen (Metric.ball (0 : Euclidean n) r) := Metric.isOpen_ball
/-- Passing the stronger graph threshold only forgets a numeric inequality. -/
def forget_graph_threshold {d : ℕ} {B : ℝ} {kMin : ℕ} {Sweak Sgraph Sop : ℝ}
    (h : Sweak ≤ Sgraph) (i : Histories d B kMin Sgraph Sop) : Histories d B kMin Sweak Sop :=
  ⟨i.val,(max_le_max h (le_refl Sop)).trans i.2.1,i.2.2⟩
/-- Restrict a single, already uniform signed-factor cost to the measured
    source's actual index. The orders, powers and constants are unchanged. -/
theorem pullback_cost {ι β E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : GradedScale E} {H : GradedScale F}
    {ρ : ι → ℝ} {T : ι → E →ₗ[ℝ] F} (e : β → ι)
    (hc : ResponseTransfer.HasPolynomialSobolevCost G H ρ T) :
    ResponseTransfer.HasPolynomialSobolevCost G H (fun i ↦ ρ (e i)) (fun i ↦ T (e i)) := by
  intro s
  obtain ⟨t,c,D,hD,h⟩ := hc s
  exact ⟨t,c,D,hD,fun i v hv ↦ h (e i) v hv⟩
end JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def base := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def leak := `JanetCartan.PhysicalInitialization.OriginalSampledLeakage
private def pdo := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
private def sym := `JanetCartan.PhysicalPrimary.OriginalRetardedSymbols
private def a (k : Name) (p : Array Expr) := mkAppN (mkConst k) p
private def down (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => down (.proj ``And 1 h) k
private def atIndex (h : Expr) (k : Nat) := Expr.proj ``And 0 (down h k)
private def byName (key : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec readNames : Expr → Array (Option Expr)
    | .forallE n _ body _ => #[(known.find? (·.1 == n)).map (·.2)] ++ readNames body
    | .mdata _ e => readNames e
    | _ => #[]
  let opts := readNames (← getConstInfo key).type
  unless (opts.filter Option.isSome).size == known.size do throwError "missing ordinary binder of {key}"
  mkAppOptM key opts
private def nativePrefix (key : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo key
  let mut b := info.type
  let mut args := #[]
  for _ in [:known.size] do
    let .forallE n _ body _ := b.consumeMData | throwError "native polynomial spine ended early"
    let some (_,arg) := known.find? (·.1 == n) | throwError "missing actual physical polynomial input {n}"
    args := args.push arg
    b := body
  unless b.bindingName! == `a do throwError "expected the first residual letter, got {b.bindingName!}"
  return mkAppN (mkConst key (info.levelParams.map fun _ => .zero)) args

run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `Current.projected)).type (some 32) fun s _ => do
    let fixed := s[:23].toArray
    let stat (k : Name) := a (reg ++ k) fixed
    let d := s[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let hn := s[1]!
    let reserve := a `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[d]
    let coeff := s[:28].toArray ++ #[reserve,s[28]!,s[29]!,a ``coefficient_reserve #[d,s[27]!,s[30]!],s[31]!]
    let hargs := #[d,s[25]!,s[28]!,a (reg ++ `History.S) s,a (op ++ `S) coeff]
    let I ← store (base ++ `Family) s (a ``Histories hargs) true
    let original := #[n] ++ fixed[1:21].toArray
    let q (k : Name) := a (`JanetCartan.PhysicalInitialization.OriginalProtected ++ k) original
    let cap := a `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,original[20]!]
    let sd := original.set! 20 cap
    let μ := a `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure sd
    let hp := a (reg ++ `screened_pos) #[n,hn,q `r,μ,q `fact2,a `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure sd]
    let core := a (reg ++ `core_spec) #[n,hn,a (reg ++ `screenedRadius) #[n,hn,q `r,μ],hp]
    let hΩ := a ``native_open #[n,a `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,hn]]
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let Ω := fa[1]!
    let KQ ← mkAppM `Metric.closedBall #[fa[2]!,fa[3]!]
    let hKQ ← mkAppM `ProperSpace.isCompact_closedBall #[fa[2]!,fa[3]!]
    let input ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask #[f]
    let hin ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask_range #[f]
    let E ← inferType fa[2]!
    let hib := a ``range_norm #[E,input,hin]
    let hob := a ``range_norm #[E,stat `output,stat `fact18]
    let univ := mkApp (mkConst `Set.univ [.zero]) E
    let meas ← synthInstance (mkApp (mkConst `MeasurableSpace [.zero]) (← inferType fa[2]!))
    let hUniv ← byName `MeasurableSet.univ #[(`α,← inferType fa[2]!),(`m,meas)]
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
    let costBound := mkApp (stat `fact27) one
    let hcost ← forallBoundedTelescope (← inferType costBound) (some 2) fun p _ => do
      mkLambdaFVars p (← mkAppM ``le_of_lt #[mkAppN costBound p])
    let mask (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalSourceMasks ++ k) fixed
    let hχ₂ := mask `χ₂_smooth
    let hχ₃ := mask `χ₃_smooth
    let χ₂ := (← inferType hχ₂).appArg!
    let χ₃ := (← inferType hχ₃).appArg!
    let hνU ← mkAppM `Set.subset_univ #[← mkAppM `tsupport #[χ₃]]
    let hμU ← mkAppM `Set.subset_univ #[← mkAppM `tsupport #[χ₂]]
    withLocalDeclD `i I fun i => do
      let raw ← mkAppM ``Subtype.val #[i]
      let index (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,raw]
      let proof := a ``admitted_data (hargs ++ #[a (op ++ `fact0) coeff,i])
      let common := #[index `length,index `u,index `ell,atIndex proof 2]
      let w := s ++ #[index `R₀,atIndex proof 0] ++ common
      let cur (k : Name) := a (reg ++ `Current ++ k) w
      let hp := a (leak ++ `current_coefficients) (coeff ++ #[index `R₀,atIndex proof 1] ++ common ++ #[KQ,hKQ,index `K,down proof 5])
      let make (v : Expr) := mkLambdaFVars #[i] v
      let low := mkAppN (cur `fact2) #[KQ,hKQ]
      let hl ← mkAppM `JanetCartan.PhysicalPrimary.OriginalWordOrdinary.algebraic_low_bounds #[KQ,cur `Q,cur `B,atIndex low 0,atIndex low 1]
      let hQ ← byName `ContDiff.contDiffOn #[(`s,Ω),(`h,cur `hQ)]
      let hB ← byName `ContDiff.contDiffOn #[(`s,Ω),(`h,cur `hB)]
      let hmap ← mkAppM `Set.MapsTo.mono_left #[cur `fact0,← mkAppM `Set.subset_univ #[Ω]]
      let ep := a (sym ++ `endpoint_native) w
      let ret := a (sym ++ `physical_residual_retarded_bounds) w
      forallBoundedTelescope (← inferType ep) (some 1) fun p _ => do
        let hAlg := a (pdo ++ `algebraic_bounds) (w ++ p ++ #[one])
        let normal := Expr.proj ``And 0 hAlg
        let jet := Expr.proj ``And 1 hAlg
        let onSector (v : Expr) := mkLambdaFVars p v
        let phase := (← inferType (mkAppN ret p)).getAppArgs[7]!
        let field (k : Name) := a (pdo ++ `Algebraic ++ k) fixed
        let A := a (leak ++ `Aprofile) coeff
        let hA := a (leak ++ `Aprofile_nonneg) coeff
        let known : Array (Name × Expr) := #[(`d,d),(`ι,I),(`Ω,Ω),(`x,fa[2]!),(`RQ,fa[3]!),(`M,fa[6]!),(`A₀,fa[4]!),(`K,fa[5]!),
          (`f,f),(`hK,q `fact14),(`hΩ,hΩ),(`hRQΩ,atIndex core 2),(`threshold,stat `L),(`ht,stat `hL),
          (`output,stat `output),(`ho,stat `fact17),(`hoc,stat `fact19),(`hob,hob),(`hos,stat `fact20),(`hib,hib),
          (`Rbox,stat `Rbox),(`Ralg,field `Rbox),(`Malg,field `Mbound),(`base,mkApp (stat `base) one),(`D,stat `Dpdo),
          (`Dgain,stat `Dgain),(`Gain,stat `Gain),(`cost,mkApp (stat `cost) one),(`C,← onSector (a (pdo ++ `Dalgebraic) fixed)),
          (`AQ,A),(`AB,A),(`hDgain,stat `fact31),(`hGain,stat `fact32),(`hcost,hcost),(`hC,← onSector (a (pdo ++ `Dalgebraic_nonneg) fixed)),
          (`hAQ,hA),(`hAB,hA),(`ρ,← make (index `lam)),(`L,← make (index `K)),(`hL,← make (atIndex proof 3)),
          (`hLρ,← make (atIndex proof 4)),(`Rstar,reserve),(`hRstar,a ``one_le_reserve #[d]),
          (`Q,← make (cur `Q)),(`B,← make (cur `B)),(`hQ,← make hQ),(`hB,← make hB),(`hmap,← make hmap),
          (`hQl,← make (.proj ``And 0 hl)),(`hBl,← make (.proj ``And 1 hl)),
          (`hQp,← make (.proj ``And 0 hp)),(`hBp,← make (.proj ``And 1 hp)),
          (`W₁,← make (cur `W₁)),(`T,← make (mkApp (cur `Op) one)),(`Ψ,← make (← onSector phase)),
          (`χout,stat `χout),(`χsource,stat `χsource),(`hs,stat `hs),(`hendpoint,← make ep),(`hretarded,← make ret),
          (`hnormal,← make (← onSector normal)),(`hjets,← make (← onSector jet)),(`μ,χ₂),(`ν,χ₃),(`hμ,hχ₂),(`hν,hχ₃),
          (`hμc,mask `χ₂_compact),(`hνc,mask `χ₃_compact),(`hμb,← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[stat `χ₂]),
          (`hνb,← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[stat `χ₃]),(`U,univ),(`hU,hUniv),(`hνU,hνU),(`hμU,hμU)]
        let key := `JanetCartan.RegularSector.FiniteResidual.FiniteIdentity.selectedFullPairedResidualTerm_measured_hasPolynomialRestrictionCost_with_signed
        let h ← nativePrefix key known
        forallBoundedTelescope (← inferType h) (some 2) fun ab _ => do
          let signed := down (mkAppN h ab) 2
          -- The norm bounds hob and hib have static types; their native proofs
          -- cannot leave an irrelevant representative i free in the family.
          discard <| store (base ++ `all_signed_costs) (s ++ ab) signed

/- The graph uses its protected comparison threshold. Both costs below
   belong to the whole SAME graph family and retain independent adjoints. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `Graph.S)).type (some 34) fun g _ => do
    let d := g[0]!
    let fixed := g[:23].toArray
    let weak := fixed ++ #[g[25]!,a (reg ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
    let reserve := a `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[d]
    let coeff := weak[:28].toArray ++ #[reserve,weak[28]!,weak[29]!,a ``coefficient_reserve #[d,weak[27]!,weak[30]!],weak[31]!]
    let Sgraph := a (reg ++ `Graph.S) g
    let Sreg := a (reg ++ `History.S) weak
    let Sop := a (op ++ `S) coeff
    let gs := #[d,weak[25]!,weak[28]!,Sgraph,Sop]
    let I ← store (base ++ `GraphFamily) g (a ``Histories gs) true
    let reached := a (reg ++ `Graph.regular_reached) (g ++ #[Sgraph,← mkAppM ``le_refl #[Sgraph]])
    let restrictMap := a ``forget_graph_threshold #[d,weak[25]!,weak[28]!,Sreg,Sgraph,Sop,reached]
    let cost := a (base ++ `all_signed_costs) weak
    forallBoundedTelescope (← inferType cost) (some 3) fun ab _ => do
      let out ← mkAppM ``pullback_cost #[restrictMap,mkAppN cost ab]
      discard <| store (base ++ `graph_signed_costs) (g ++ ab) out
      withLocalDeclD `i I fun i => do
        let proof := a ``admitted_data (gs ++ #[a (op ++ `fact0) coeff,i])
        let raw ← mkAppM ``Subtype.val #[i]
        let idx (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,raw]
        let hWeak := a (reg ++ `Graph.regular_reached) (g ++ #[idx `R₀,atIndex proof 0])
        let w := weak ++ #[idx `R₀,hWeak,idx `length,idx `u,idx `ell,atIndex proof 2]
        let lo := a `JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds.actual_low_bounds (w ++ ab[:2].toArray)
        discard <| store (base ++ `graph_signed_low) (g ++ ab) (← mkLambdaFVars #[i] (mkApp (down lo 2) ab[2]!))
end JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
end
