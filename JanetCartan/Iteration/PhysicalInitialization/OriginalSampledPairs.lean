module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtectionApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeights
public import JanetCartan.Iteration.PhysicalSampling.OriginalWindow
public import JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.SampleGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Geometry
public meta import Lean

/-!
# Protected signed products of the actual outer sample

Use the external χ² sample, not an angularly weighted subset. A plus pair may
be diagonal; a minus pair is required to have distinct labels, not distinct
patches. Each pair is fixed before its phase is evaluated anywhere. Its true
beat is retained on the original physical current and the support of χ₂.
Consumers: `PhysicalPairs.exists_physical_signed_correctedSource_decay_of_supplied_core_factory`,
`app:rem:exhaustive-signed-pairs`, `app:ch_pairs:setup:pairs-lag`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalSampledPairs
open CanonicalRowComparison SeparatedSampling FrozenMenu SignedPairs PhysicalSampling
open SignedProductEstimates InitialSourceLocalization RegularSector.FiniteMasks.ActualFamily

/-- The two signs share the actual external sample and original convolved window.
The signed group is the full (row,color); no numerical radius is used as a label.
The same-group minus beat is the exact distance of its two original nodes. -/
private theorem of_outer_nodes {J : Type} (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ)
    (radius : J → ℝ) (hz : ∀ j z, ψ j z ≠ 0 → WithLp.toLp 2 z ∈ parameterInterior (radius j))
    (hp : 0 < p) (R : ℝ) (hR : 1 ≤ R) (U : J → Lattice → Point) :
    let h := R ^ (-separationExponent)
    let I := SampleIndex p B ψ (OriginalWindow.window p) h U
    let group := fun i : I ↦ (i.1,color p i.2.val.1)
    let z := fun i : I ↦ (WithLp.toLp 2 (node h (U i.1) i.2) : Euclidean 3)
    let S := fun g : J × OriginalColoredProtection.Color p ↦ parameterCube (radius g.1)
    ∀ (minus : Bool) (i j : I), (minus = true → i ≠ j) →
      ∃ q : Pair (J × OriginalColoredProtection.Color p) (Euclidean 3) S,
        h/2 ≤ q.beat ∧
        (minus = false → q.beat = 1) ∧
        (minus = true → group i = group j → q.beat = ‖z i-z j‖) ∧
        (group i ≠ group j → q.beat = 1) ∧
        ∀ f : (J × OriginalColoredProtection.Color p) → Euclidean 3 → ℝ,
          q.vector f = if minus then f (group i) (z i) - f (group j) (z j)
                       else f (group i) (z i) + f (group j) (z j) := by
  intro h I group z S
  have hRpos := zero_lt_one.trans_le hR
  have hh : 0 < h := Real.rpow_pos_of_pos hRpos _
  have hone : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num [separationExponent])
  have hhalf : h/2 ≤ 1 := by linarith
  have hnodes (i : I) : z i ∈ S (group i) :=
    original_sample_node_mem_parameterCube radius
      (fun a v hv k ↦ (hz a v hv k).le) i
  have hsep (i j : I) (hne : i ≠ j) (hg : group i = group j) : h/2 ≤ ‖z i - z j‖ :=
    original_sample_same_group_separation (OriginalWindow.window_bounds hp) hh i j hne hg
  intro minus i j hdiag
  cases minus with
  | false =>
    obtain ⟨q,hb,hv⟩ := sample_plus_represented_with_beat (E := ℝ) group z hnodes i j
    exact ⟨q,hb ▸ hhalf,fun _ ↦ hb,fun h ↦ Bool.noConfusion h,fun _ ↦ hb,hv⟩
  | true =>
    obtain ⟨q,hb,hin,hout,hv⟩ := sample_minus_represented_with_beat (E := ℝ)
      (half_pos hh) hhalf group z hnodes hsep (hdiag rfl)
    exact ⟨q,hb,fun h ↦ Bool.noConfusion h,fun _ ↦ hin,hout,hv⟩

/-- The existing inverse chart, hence the entire actual χ₂ source support, is
inside the retained signed-protection ball; no physical cutoff is shrunk. -/
private theorem chart_in_protected {d : ℕ} (hn : 5 ≤ d+1) {r μ : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    {K : Set (Euclidean (d+1))} {M : ℝ}
    (f : ActualMaskFamily (ball 0 (PhysicalSeed.OriginalBoundary.b hn)) 0
      (OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ)) (cubeStress (d+1)) K M)
    (t : ℝ) : ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ⊆ closedBall 0 r := by
  exact (ball_subset_ball (min_le_right _ _)).trans <| ball_subset_closedBall.trans <|
    (closedBall_subset_closedBall (by linarith only [f.physicalRadius_pos] :
      f.physicalRadius ≤ 4*f.physicalRadius)).trans <| f.physicalBall_coefficientDomain.trans <|
    closedBall_subset_closedBall (OriginalRegular.core_inside_native_cutoffs hn hr hμ).1.le

/-- Transport the exact three native protections to the literal `currentGroup`.
In particular the radial component is NOT identified with the old uncolored band. -/
private theorem at_current {G : Type} {d : ℕ} {S : G → Set (Euclidean 3)}
    {family current : G → Euclidean 3 → Euclidean (d+1)} (e : family = current)
    (q : Pair G (Euclidean 3) S) {a A : ℝ} {K : Set (Euclidean (d+1))}
    (h : (∀ L ∈ cubeBadSubspaces (d+1), a*q.beat ≤ ‖projectAway L (q.vector family)‖) ∧
      q.vector family ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam → a*(lam*q.beat) ≤ ‖lam • q.vector family‖ ∧
        ‖lam • q.vector family‖ ≤ A*(lam*q.beat))
    (hk : q.beat⁻¹ • q.vector family ∈ K) :
    (∀ L ∈ cubeBadSubspaces (d+1), a*q.beat ≤ ‖projectAway L (q.vector current)‖) ∧
      q.vector current ≠ 0 ∧ (∀ lam : ℝ, 0 ≤ lam → a*(lam*q.beat) ≤ ‖lam • q.vector current‖ ∧
        ‖lam • q.vector current‖ ≤ A*(lam*q.beat)) ∧ q.beat⁻¹ • q.vector current ∈ K := by
  subst current
  exact ⟨h.1,h.2.1,h.2.2,hk⟩

end JanetCartan.PhysicalInitialization.OriginalSampledPairs
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledPairs
open Lean Meta Elab Command OriginalProtectedTemplate
private def base := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def mkN (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs

/- Keep one signed pair over the actual outer index before any subsequent
choice of physical point, word depth or Fourier mask. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (outer ++ `ψ)).type (some 22) fun p _ => do
    let get (s : Name) := mkN (outer ++ s) p
    let proof := mkN ``of_outer_nodes #[get `Index,p[2]!,get `B,get `ψ,get `parameterRadius,get `nonzero_parameter]
    let t ← inferType proof
    let target ← forallBoundedTelescope t (some 4) fun args rhs => do
      let .letE _ _ h b _ := rhs | throwError "sampled pair: missing the physical mesh"
      let .letE _ _ I b _ := b.instantiate1 h | throwError "sampled pair: missing outer SampleIndex"
      let .letE _ _ g b _ := b.instantiate1 I | throwError "sampled pair: missing actual row/color"
      let .letE _ _ z b _ := b.instantiate1 g | throwError "sampled pair: missing actual spatial node"
      let .letE _ _ S b _ := b.instantiate1 z | throwError "sampled pair: missing signed cube"
      let nativeS := mkN (col ++ `Scolor) p
      discard <| store (base ++ `cube_eq) p (← mkEqRefl S) false (some (← mkEq S nativeS))
      mkForallFVars args (b.instantiate1 nativeS)
    discard <| store (base ++ `exists_on_outer_sample) p proof false (some target)

/- Prove the geometric inclusion once, BEFORE substituting the merged graph's
   original data. This keeps the selected physical radius opaque downstream. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `f)).type (some 23) fun s _ => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let ordinary := #[n] ++ s[1:21].toArray
    let capped := mkN `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,s[1]!,ordinary[20]!]
    let sel := ordinary.set! 20 capped
    let radius := mkN `JanetCartan.PhysicalInitialization.OriginalProtected.r ordinary
    let μ := mkN `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure sel
    let hμ := mkN `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure sel
    let hr := mkN `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 ordinary
    let f := mkN (reg ++ `f) s
    let ft ← inferType f
    unless ft.isAppOf `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily do
      throwError "sampled pair: expected original finite mask family, got {ft.getAppFn.constName?}"
    let fa := ft.getAppArgs
    let chartProof := mkN ``chart_in_protected
      #[s[0]!,s[1]!,radius,μ,hr,hμ,fa[fa.size-2]!,fa.back!,f,mkN (reg ++ `r) s]
    discard <| store (base ++ `chart_subset) s chartProof

/- Cache the actual weak projected immersion on graph42. Its physical map is
   exactly the one already certified by OriginalGraphResponse.same_finite_map. -/
elab "original_sampled_pair_current " kind:num : command => liftTermElabM <| withTransparency .reducible do
  let graph := reg ++ `Graph
  let margin := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.raw_frame_margin_native
  forallBoundedTelescope (← getConstInfo margin).type (some 42) fun x tail => do
    let reached ← inferType x[37]!
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity (graph ++ `S) 34 do throwError "sampled pair: lost original reached graph threshold"
    let g := S.getAppArgs
    let p := x[:22].toArray
    let s := g[:23].toArray
    let weak := s ++ #[g[25]!,mkN (graph ++ `regular_scale) g[:27].toArray] ++ g[27:34].toArray ++
      #[x[36]!,mkN (graph ++ `regular_reached) (g ++ x[36:38].toArray)] ++ x[38:42].toArray
    let projected := mkN (reg ++ `Current.projected) weak
    let some F := tail.find? (fun e => e.isAppOf `JanetCartan.RevisedGlobal.finiteMap && e.appArg! == x[39]!)
      | throwError "sampled pair: missing sampling graph finite map"
    let masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
    let get (name : Name) := mkN (col ++ name) p
    let own (name : Name) := mkN (base ++ name) x
    if kind.getNat == 0 then
      discard <| store (base ++ `projected) x projected true
      return
    if kind.getNat == 1 then
      let native := mkN `JanetCartan.PhysicalSampling.OriginalGraphResponse.same_finite_map x
      unless (← inferType native).appArg! == F do throwError "sampled graph map changed"
      discard <| store (base ++ `same_current) x native false
        (some (← mkEq (.proj ``Subtype 0 (own `projected)) F))
      return
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let eucl := mkApp (mkConst `JanetCartan.Euclidean) n
    if kind.getNat == 4 then
      let support := mkN (masks ++ `χ₂_support_chart) s
      let st ← inferType support
      let source := st.getAppArgs[st.getAppNumArgs-2]!
      withLocalDeclD `y eucl fun y => do
        withLocalDeclD `hy (← mkAppM ``Membership.mem #[source,y]) fun hy => do
          let restricted := mkAppN (own `on_actual_chart) #[y,mkAppN support #[y,hy]]
          discard <| store (base ++ `on_actual_source) (x ++ #[y,hy]) restricted
      return
    let U := mkN (masks ++ `chart) s
    let pairType := (← inferType (get `signed_bounds)).bindingDomain!
    unless pairType.isAppOfArity ``Prod 2 do throwError "missing projected-map/physical-point product"
    withLocalDeclD `y eucl fun y => do
      withLocalDeclD `hy (← mkAppM ``Membership.mem #[U,y]) fun hy => do
        let xyz := x ++ #[y,hy]
        if kind.getNat == 2 then
          let pointType ← whnf pairType.appArg!
          unless pointType.isAppOfArity ``Subtype 2 do throwError "missing protected physical point subtype"
          let hmember := mkN (base ++ `chart_subset) (s ++ #[y,hy])
          let Y := mkAppN (mkConst ``Subtype.mk [.one]) (pointType.getAppArgs ++ #[y,hmember])
          discard <| store (base ++ `state) xyz
            (mkAppN (mkConst ``Prod.mk [.zero,.zero]) (pairType.getAppArgs ++ #[own `projected,Y])) true (some pairType)
          return
        unless kind.getNat == 3 do throwError "unknown original pair field"
        let state := mkN (base ++ `state) xyz
        let eqn := mkApp (get `family_eq_currentGroup) state
        let eqType ← inferType eqn
        let family := eqType.getAppArgs[1]!
        let current := eqType.appArg!
        unless current.isAppOfArity `JanetCartan.ActualCarriers.ConstructedSignedGeometry.currentGroup 12 do
          throwError "lost currentGroup at the original signed source"
        let bounds := mkApp (get `signed_bounds) state
        let contain := mkApp (get `normalized_pair_mem_source) state
        forallBoundedTelescope (← inferType bounds) (some 1) fun qs _ => do
          let q := qs[0]!
          let proof := mkN ``at_current #[get `Groups,s[0]!,get `Scolor,family,current,eqn,
            q,get `aColor,get `AColor,get `Ksource,mkApp bounds q,mkApp contain q]
          discard <| store (base ++ `on_actual_chart) (xyz ++ qs) proof

original_sampled_pair_current 0
original_sampled_pair_current 1
original_sampled_pair_current 2
original_sampled_pair_current 3
original_sampled_pair_current 4

end JanetCartan.PhysicalInitialization.OriginalSampledPairs
end
