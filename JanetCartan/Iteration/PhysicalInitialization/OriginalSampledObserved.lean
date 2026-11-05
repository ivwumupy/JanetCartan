module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPolynomial
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.ObservedChains
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Measured
public meta import Lean

/-!
# Original measured powers: the physical observation inputs

Instantiate `measuredResidual_hchain_of_individual_estimates` on the original
normalized solver's physical norm ball, not the ambient Euclidean space.
All operator fields, including the angular algebraic symbol, are pulled back
from the actual history; reindexing by measured source labels changes no
threshold, coefficient, chart or operator (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalInitialization.OriginalSampledObserved
open Set Metric MeasureTheory
open scoped ContDiff
/-- The paper's signed-pair gap, distinct from the primary gap. -/
theorem signed_gap_positive : 0 < (1/1000 : ℝ) := by norm_num
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization SmallSupport LocalSobolev
open ArbitraryAccuracy FiniteChain.Graph
/-- Real inclusion and extension of the original local source; no second
    source cutoff is inserted (`app:ch_regular:eq:source-tail`). -/
def complexSource {d : ℕ} {D : Set (Euclidean (d+1))} (hD : MeasurableSet D)
    (u : LocalL2 D (Euclidean (d+1))) : LocalL2 (Set.univ : Set (Euclidean (d+1))) (EuclideanSpace ℂ (Fin (d+1))) :=
  restrictL2 univ (l2ComplexInclusion volume (zeroExtend hD u))
/-- The literal source input quantified by `PhysicalPairs.LocalCorrectedApplication`.
    Its producer is the original signed first-mask estimate, not a residual-power
    estimate. All masks and depths come after the source and its true frequency. -/
def FirstMaskInput {d : ℕ} {ι : Type} (ρ : ι → ℝ)
    (source : ι → LocalL2 (Set.univ : Set (Euclidean (d+1))) (EuclideanSpace ℂ (Fin (d+1))))
    (S : Set (Euclidean (d+1) × Euclidean (d+1))) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ A : ℕ → ℝ, (∀ k, 0 ≤ A k) →
  ∀ m : ι → LocalizerSymbol (d+1),
    (∀ i, ContDiff ℝ ∞ (m i)) → (∀ i, HasCompactSupport (m i)) →
    (∀ i z, m i z ∈ Icc (0:ℝ) 1) →
    (∀ i k z, ‖iteratedFDeriv ℝ k (m i) z‖ ≤ A k) →
    (∀ i y ξ, m i (y,-ξ) = m i (y,ξ)) →
    (∀ i, cthickening δ S ⊆ interior {z | m i z = 1}) →
    ∀ M : ι → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
    (∀ i v, M i v =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer (ρ i) (m i) (fun z ↦ (v z).ofLp) y)) →
    ∀ s, RapidDecayAt (restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ)
      s ρ (fun _ ↦ 1) (fun i ↦ source i - localRetardedOperator MeasurableSet.univ univ (M i) (source i))
/-- Zero extension and measurement do not enlarge the actual global letter
    norm (`app:ch_regular:lem:finite-chain`). -/
theorem restricted_norm_bound {d q : ℕ} {C : ℝ}
    (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (hT : ‖T‖ ≤ C)
    (v : LocalL2 (Set.univ : Set (Euclidean (d+1))) (EuclideanSpace ℂ (Fin q))) :
    ‖localRetardedOperator MeasurableSet.univ univ T v‖ ≤ C*‖v‖ := by
  change ‖restrictL2 univ (T (zeroExtend MeasurableSet.univ v))‖ ≤ _
  calc
    _ ≤ ‖T (zeroExtend MeasurableSet.univ v)‖ := by
      simpa only [one_mul] using (restrictL2 (d := d) (q := q) univ).le_of_opNorm_le
        (norm_restrictL2_le univ) _
    _ ≤ C*‖zeroExtend MeasurableSet.univ v‖ := T.le_of_opNorm_le hT _
    _ = _ := by rw [LinearIsometry.norm_map]
/-- The fixed low bound is uniform after any reindexing by source labels. -/
theorem uniform_low_cost {d q : ℕ} {ι : Type} {C : ℝ} (hC : 0 ≤ C)
    (ρ : ι → ℝ) (T : ι → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hT : ∀ i, ‖T i‖ ≤ C) :
    ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖localRetardedOperator MeasurableSet.univ univ (T i) v‖ ≤ D*(ρ i)^c*‖v‖ := by
  exact ⟨C,0,hC,fun i v ↦ by simpa only [Real.rpow_zero,mul_one] using restricted_norm_bound (T i) (hT i) v⟩
/-- The same signed letter followed by a right proof localizer has a uniform
    low bound, with no commutation of either physical cutoff. -/
theorem uniform_near_cost {d q : ℕ} {ι : Type} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ρ : ι → ℝ) (T R : ι → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hT : ∀ i, ‖T i‖ ≤ C) (hR : ∀ i, ‖R i‖ ≤ D) :
    ∃ A c : ℝ, 0 ≤ A ∧ ∀ i v,
      ‖localRetardedOperator MeasurableSet.univ univ (T i)
        (localRetardedOperator MeasurableSet.univ univ (R i) v)‖ ≤ A*(ρ i)^c*‖v‖ := by
  refine ⟨C*D,0,mul_nonneg hC hD,fun i v ↦ ?_⟩
  simpa only [Real.rpow_zero,mul_one,mul_assoc] using
    (restricted_norm_bound (T i) (hT i) _).trans (mul_le_mul_of_nonneg_left (restricted_norm_bound (R i) (hR i) v) hC)
/-- Normalize only the notation of the terminal producer's natural frequency
    power; the slow-scale loss and source operator remain unchanged. -/
theorem nat_frequency_power {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GradedScale E) (s p b accuracy : ℕ) (C ρ L : ℝ) (v u : E)
    (h : v ∈ G.level s ∧ G.gradeNorm s v ≤ C*ρ^p*L^b*(L/ρ)^accuracy*‖u‖) :
    v ∈ G.level s ∧ G.gradeNorm s v ≤ C*ρ^(p:ℝ)*L^b*(L/ρ)^accuracy*‖u‖ := by
  simpa only [Real.rpow_natCast] using h

theorem graph_reached {d : ℕ} {B : ℝ} {k : ℕ} {S C : ℝ}
    (i : OriginalSampledPolynomial.Histories d B k S C) : S ≤ i.val.R₀ :=
  (le_max_left S C).trans i.2.1
theorem native_norm_ball (n : ℕ) (r : ℝ) : MeasurableSet (ball (0 : Euclidean n) r) :=
  isOpen_ball.measurableSet
theorem core_in_physical (n : ℕ) (r R : ℝ) : ball (0 : Euclidean n) (min r R) ⊆ ball 0 R :=
  ball_subset_ball (min_le_right _ _)
theorem bounded_mask {E : Type} (f : E → ℝ) (h : ∀ z, f z ∈ Icc (0:ℝ) 1) :
    ∀ z, ‖f z‖ ≤ 1 := fun z ↦ (Real.norm_of_nonneg (h z).1).trans_le (h z).2
end JanetCartan.PhysicalInitialization.OriginalSampledObserved
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledObserved
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def root := `JanetCartan.PhysicalInitialization.OriginalSampledObserved
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def pdo := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
private def key := `JanetCartan.RegularSector.NormalizedResidualWords.ObservedChains.measuredResidual_hchain_of_individual_estimates
private def a (k : Name) (args : Array Expr) := mkAppN (mkConst k) args
private def down (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => down (.proj ``And 1 h) k
private def head (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
private def initialNames : Expr → Array Name
  | .forallE n _ body _ => if n == `u then #[] else #[n] ++ initialNames body
  | .mdata _ e => initialNames e
  | _ => #[]

run_cmd liftTermElabM <| withTransparency .reducible do
  let info ← getConstInfo key
  let names := initialNames info.type
  unless names.back! == `houtput do throwError "unexpected observed-power geometry spine {names}"
  let fn := mkConst key (info.levelParams.map fun _ => .zero)
  forallBoundedTelescope (← inferType fn) (some names.size) fun p _ => do
    let h := mkAppN fn p
    let P ← store (root ++ `Packet.for_source) p (← inferType h) true
    discard <| store (root ++ `Producer.for_source) p h false (some P)

run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `Graph.S)).type (some 34) fun g _ => do
    let fixed := g[:23].toArray
    let stat (k : Name) := a (reg ++ k) fixed
    let d := g[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let weak := fixed ++ #[g[25]!,a (reg ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
    let I := a (poly ++ `GraphFamily) g
    let orig := #[n] ++ fixed[1:21].toArray
    let q (k : Name) := a (`JanetCartan.PhysicalInitialization.OriginalProtected ++ k) orig
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let E ← inferType fa[2]!
    let D ← mkAppM `Metric.ball #[fa[2]!,stat `normRadius]
    let hD := a ``native_norm_ball #[n,stat `normRadius]
    let bumps := stat `afterChoice_χ₃
    let hχ₂D ← mkAppM `Set.Subset.trans #[head bumps 0,stat `hUW]
    let hχ₃D ← mkAppM `Set.Subset.trans #[head bumps 1,stat `hUW]
    let U := (← inferType (head bumps 1)).appArg!
    let phys ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.physicalRadius #[f]
    let hU := a `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open fixed
    let hcore := a ``core_in_physical #[n,stat `r,phys]
    let both := head bumps 7
    let houtput ← forallBoundedTelescope (← inferType both) (some 2) fun y _ => mkLambdaFVars y (.proj ``And 0 (mkAppN both y))
    let input ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask #[f]
    let hin ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask_range #[f]
    let hib := a ``bounded_mask #[E,input,hin]
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
    withLocalDeclD `β (mkSort .one) fun β => do
      withLocalDeclD `indices (← mkArrow β I) fun e => do
       withLocalDeclD `j β fun j => do
        let i := mkApp e j
        let r ← mkAppM ``Subtype.val #[i]
        let field (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,r]
        let hReached ← mkAppM ``graph_reached #[i]
        let admiss := head (← mkAppM `Subtype.property #[i]) 1
        let w := weak ++ #[field `R₀,a (reg ++ `Graph.regular_reached) (g ++ #[field `R₀,hReached]),field `length,field `u,field `ell,admiss]
        let cur (k : Name) := a (reg ++ `Current ++ k) w
        let family (v : Expr) := mkLambdaFVars #[j] v
        forallBoundedTelescope (← inferType (cur `fact3)) (some 1) fun p _ => do
          let hb ← family (← mkLambdaFVars p (.proj ``And 0 (a (pdo ++ `algebraic_bounds) (w ++ p ++ #[one]))))
          let known : Array (Name × Expr) := #[(`d,d),(`ι,β),(`Ω,fa[1]!),(`x,fa[2]!),(`RQ,fa[3]!),(`C₀,fa[6]!),(`A₀,fa[4]!),(`K,fa[5]!),
            (`f,f),(`hK,q `fact14),(`hsym,q `fact21),(`L₀,stat `L),(`hL₀,stat `hL),(`Q,← family (cur `Q)),(`B,← family (cur `B)),
            (`W₁,← family (cur `W₁)),(`T,← family (mkApp (cur `Op) one)),(`output,stat `output),(`ho,stat `fact17),(`hoc,stat `fact19),
            (`hor,stat `fact18),(`hib,hib),(`hsupp,stat `fact20),(`Ralg,← family (a (pdo ++ `Algebraic.Rbox) fixed)),
            (`Calg,← family (a (pdo ++ `Algebraic.Mbound) fixed)),(`hb,hb),(`χ₂,stat `χ₂),(`χ₃,stat `χ₃),(`hnest,head bumps 2),
            (`D,D),(`hD,hD),(`hχ₂D,hχ₂D),(`hχ₃D,hχ₃D),(`U,U),(`hU,hU),(`hχ₃U,head bumps 1),(`hcore,hcore),(`houtput,houtput)]
          let names := initialNames (← getConstInfo key).type
          let args ← names.mapM fun name => do
            let some (_,v) := known.find? (·.1 == name) | throwError "missing original geometry field {name}"
            pure v
          discard <| store (root ++ `for_reindexed_sources) (g ++ #[β,e]) (a (root ++ `Producer.for_source) args)

/- The actual Neumann localizer is precisely the same measured residual.
   This equality inserts restriction/zero-extension at every local power;
   it makes no claim about powers of a global operator. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `Current.projected)).type (some 38) fun w _ => do
    let fixed := w[:23].toArray
    let stat (k : Name) := a (reg ++ k) fixed
    let cur (k : Name) := a (reg ++ `Current ++ k) w
    let n := mkApp (mkConst ``Nat.succ) w[0]!
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let orig := #[n] ++ fixed[1:21].toArray
    let hK := a `JanetCartan.PhysicalInitialization.OriginalProtected.fact14 orig
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
    let hnorm := a ``native_norm_ball #[n,stat `normRadius]
    let D ← mkAppM `Metric.ball #[fa[2]!,stat `normRadius]
    let r := (← inferType (stat `hrU)).appArg!
    let budget := (← inferType (stat `hbudget)).appArg!
    let known : Array (Name × Expr) := #[(`d,w[0]!),(`Ω,fa[1]!),(`x,fa[2]!),(`RQ,fa[3]!),(`M,fa[6]!),(`A₀,fa[4]!),(`K,fa[5]!),
      (`U,D),(`r,r),(`budget,budget),(`f,f),(`hK,hK),(`L,stat `L),(`Q,cur `Q),(`B,cur `B),(`W₁,cur `W₁),
      (`output,stat `output),(`ho,cur `ho),(`hob,cur `hob),(`hib,cur `hib),(`T,mkApp (cur `Op) one),(`hU,hnorm),
      (`c,fa[2]!),(`hr,stat `hrU),(`hball,stat `hUW),(`hmem,cur `hmem),(`hbudget,stat `hbudget),
      (`hbound,cur `hbound),(`χ₂,stat `χ₂),(`χ₃,stat `χ₃),(`hs₂,head (stat `afterChoice_χ₃) 0)]
    let name := `JanetCartan.RegularSector.NormalizedResidualWords.localizedResidual_normalized_eq_measured
    let rec options : Expr → Array (Option Expr)
      | .forallE n _ body _ => #[(known.find? (·.1 == n)).map (·.2)] ++ options body
      | .mdata _ e => options e
      | _ => #[]
    let opts := options (← getConstInfo name).type
    unless (opts.filter Option.isSome).size == known.size do throwError "missing native measured residual binder"
    unless opts.all Option.isSome do throwError "unfilled implicit of original measured residual"
    let h := a name (opts.map Option.get!)
    let ty ← inferType h
    discard <| store (root ++ `native_residual_identity) w h false (some (← mkEq (cur `Kloc) ty.getAppArgs[2]!))
end JanetCartan.PhysicalInitialization.OriginalSampledObserved
end
