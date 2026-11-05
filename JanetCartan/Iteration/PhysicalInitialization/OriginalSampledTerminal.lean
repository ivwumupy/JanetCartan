module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtectionApplication
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.TerminalMaskApplication
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.MeanCorrectedSource.ObservedCore.Coordinates

/-!
# Terminal masks on the original colored forcing sphere and fixed physical solver

One quantitative comparison chart family supplies the offset-free bound,
its derivative bound, characteristic source coverage and the fixed bad-set
buffer. The actual normalized source annulus may have a larger radial range
than the original uncolored one. Only its directions are passed to the
angular plateau of the unchanged regular-sector inverse
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalSampledTerminal
open ActualCarriers PhysicalSeed RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.AlgebraicChart
open ProtectedFlow ArbitraryAccuracy.SelectedLocalization
open MeanCorrectedSource.ObservedCore.Coordinates

/- Preserve the original Ω and RQ. The larger colored radial shell is used only
   as a compact SOURCE; the fixed angular plateaus and f are left unchanged. -/
proof_from terminal_at_screened_radius {d : ℕ} (hn : 5 ≤ d+1) (r RQ : ℝ) (hr : 0 < r) (hcore : RQ < r)
    (Ω₀ Ω₁ Γin Γout : Set (Euclidean (d+1))) (hΩ : Ω₀ ⊆ interior Ω₁) (hΩΓ : Ω₁ ⊆ interior Γin)
    (hΓ : Γin ⊆ interior Γout) (hΓout : IsCompact Γout)
    (hΩsym : ∀ ξ ∈ Ω₁, -ξ ∈ Ω₁) (hΓsym : ∀ ξ ∈ Γout, -ξ ∈ Γout)
    (c C Lx ε M : ℝ) (hc : 0 < c) (hC : 0 < C) (hL : 0 ≤ Lx) (hε : 0 < ε) (hM : 0 < M)
    (f : ActualMaskFamily (ball 0 (OriginalBoundary.b hn)) 0
      RQ (cubeStress (d+1)) Γout M)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hcert : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (t : ℝ) (χ₂ : ContDiffBump (0 : (Euclidean (d+1))))
    (hsupport : tsupport (χ₂ : (Euclidean (d+1)) → ℝ) ⊆ ball 0 (min t f.physicalRadius))
    (Ksource : Set (Euclidean (d+1))) (hK : IsCompact Ksource)
    (hsource : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ interior Ω₀) (output : (Euclidean (d+1)) → ℝ) := by
  have hphys : ball (0 : (Euclidean (d+1))) f.physicalRadius ⊆ closedBall 0
      RQ :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (show f.physicalRadius ≤ 4*f.physicalRadius by linarith [f.physicalRadius_pos]))).trans
        f.physicalBall_coefficientDomain
  have hχ := hsupport.trans (ball_subset_ball (min_le_right _ _))
  exact exists_selected_terminal_even_masks_with_localizer_estimates.{0,0,0}
    f isOpen_ball T speed G rootCost hcert hradii (eT d) (eI d) hΓout hΓsym hr hM.le hc hC hL hε
    (closedBall_subset_ball (by linarith : RQ < 2*r))
    (hΩΓ.trans (interior_subset.trans hΓ)) hΩsym χ₂ χ₂.hasCompactSupport hχ
    ((hχ.trans hphys).trans (closedBall_subset_ball hcore)) hK (fun ξ hξ => ⟨(hsource ξ hξ).1,hΩ (interior_subset (hsource ξ hξ).2)⟩) isOpen_univ
    (subset_univ _) (subset_univ _) output
private theorem graph_radius_le {a b : ℝ} (ha : 0 < a) (h : 3*a < b) : a ≤ b := by linarith
private theorem graph_buffer_in_outer {n : ℕ} {Γin Γout : Set (Euclidean n)}
    (hnest : Γin ⊆ interior Γout) {P : Set (Euclidean n × Euclidean n)} {ε : ℝ}
    (h : ∀ q ∈ P, closedBall (normalizedCovector q.2) ε ⊆ interior Γin \ cubeBadSubspaceUnion n) :
    ∀ q ∈ P, closedBall (normalizedCovector q.2) ε ⊆ Γout :=
  fun q hq _ hξ => interior_subset (hnest (interior_subset (h q hq hξ).1))
end JanetCartan.PhysicalInitialization.OriginalSampledTerminal
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledTerminal
open Lean Meta Elab Command OriginalProtectedTemplate
private def base := `JanetCartan.PhysicalInitialization.OriginalSampledTerminal
private def protectedNS := `JanetCartan.PhysicalInitialization.OriginalProtected
private def tail (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => tail (.proj ``And 1 h) k
private def part (h : Expr) (k : Nat) := Expr.proj ``And 0 (tail h k)
run_cmd liftTermElabM do
  let info ← getConstInfo (protectedNS ++ `quantitative_continuation)
  forallBoundedTelescope info.type (some 21) fun x _ => do
    let get (n : Name) := mkAppN (mkConst (protectedNS ++ n)) x
    let radii := get `fact24
    forallBoundedTelescope (← inferType radii) (some 1) fun i _ => do
      let h ← mkAppM ``graph_radius_le #[get `fact2,mkAppN radii i]
      discard <| store (base ++ `graph_radii) x (← mkLambdaFVars i h)
    let quant := get `quantitative_continuation
    forallBoundedTelescope (← inferType quant) (some 1) fun fr _ => do
      let ex := tail (mkAppN quant fr) 2
      let exType ← whnf (← inferType ex)
      unless exType.isAppOfArity ``Exists 2 do throwError "missing quantitative comparison chart witness"
      let params := x ++ fr
      let charts ← store (base ++ `comparison_charts) params (← mkAppM ``Classical.choose #[ex]) true
      let rest ← store (base ++ `comparison_spec) params (← mkAppM ``Classical.choose_spec #[ex]) false
        (some (exType.appArg!.beta #[charts]))
      for (name,k) in #[(`graph_derivative,0),(`graph_norm,1),(`graph_covers,4)] do
        discard <| store (base ++ name) params (part rest k)
      let hout ← mkAppM ``graph_buffer_in_outer #[get `fact17,part rest 5]
      discard <| store (base ++ `graph_buffer) params hout
  for k in #[`comparison_charts,`graph_radii,`graph_derivative,`graph_norm,`graph_covers,`graph_buffer] do
    let ax ← Lean.collectAxioms (base ++ k)
    unless ax.all (fun n => #[`propext,`Classical.choice,`Quot.sound].contains n) do throwError "{k}: {ax}"
  logInfo "One native current, the same chart family for derivative, two-sided gradient, source coverage and closed outer buffer."

/- The static prefix is the native outer22 followed by its two solver orders.
   This reconstructs exactly the same once-sampling-capped original23 as the
   later graph, without choosing any history, spectrum, depth or pair. -/
private def ordinaryForTerminal (p : Array Expr) : Array Expr :=
  let d := p[0]!
  let hn := p[1]!
  let merged := mkAppN (mkConst ``PhysicalSampling.samplingCappedExtra) #[d,hn,p[2]!,p[21]!]
  (#[mkApp (mkConst ``Nat.succ) d,hn] ++ p[3:22].toArray).set! 20 merged

/-- Literal inputs of the actual static terminal application. The sampling cap
is applied in the regular prefix and the strong cap only in its selected seed.
Used also when applying these same proof masks to the original retarded chain. -/
def actualTerminalArguments (p order : Array Expr) : MetaM (Array Expr) := do
  let reg := `JanetCartan.PhysicalInitialization.OriginalRegular
  let col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
  let d := p[0]!
  let hn := p[1]!
  let ordinary := ordinaryForTerminal p
  let n := ordinary[0]!
  let s := (ordinary.set! 0 d) ++ order
  let q (name : Name) := mkAppN (mkConst (protectedNS ++ name)) ordinary
  let colGet (name : Name) := mkAppN (mkConst (col ++ name)) p
  let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,ordinary[20]!]
  let seed := ordinary.set! 20 cap
  let μ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure) seed
  let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) seed
  let core := mkAppN (mkConst (reg ++ `core_inside_native_cutoffs)) #[n,hn,q `r,μ,q `fact2,hμ]
  let get (name : Name) := mkAppN (mkConst (reg ++ name)) s
  let f := get `f
  let fa := (← inferType f).getAppArgs
  unless fa.size == 7 do throwError "missing the original seven-field finite mask family"
  return #[d,hn,q `r,fa[3]!,q `fact2,part core 0,
    q `Ω₀,q `Ω₁,q `Γin,q `Γout,q `fact15,q `fact16,q `fact17,q `fact14,q `fact19,q `fact21,
    q `cgraph,q `Cgraph,q `Lx,q `ε,get `M,q `cgraph_pos,q `Cgraph_pos,q `Lx_nonnegative,q `fact8,get `fact0,
    f,get `evolutionTime,get `speedGap,get `rootSize,get `rootCost,get `fact11,get `fact13,
    get `r,get `χ₂,part (get `afterChoice_χ₃) 0,colGet `Ksource,colGet `source_compact,
    colGet `source_normalized_interior,get `output]

run_cmd liftTermElabM <| withTransparency .reducible do
  let idx := `JanetCartan.PhysicalSampling.OriginalWeights.Index
  forallBoundedTelescope (← getConstInfo idx).type (some 22) fun p _ => do
    let s := (ordinaryForTerminal p).set! 0 p[0]!
    let f := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalRegular.f) s
    forallBoundedTelescope (← inferType f) (some 2) fun order _ => do
      let args ← actualTerminalArguments p order
      discard <| store (base ++ `fixed_terminal) (p ++ order)
        (mkAppN (mkConst (base ++ `terminal_at_screened_radius)) args)
      logInfo "The original24 regular-sector f and actual colored Ksource give the terminal-mask family before any history, depth, or stage frequency."

end JanetCartan.PhysicalInitialization.OriginalSampledTerminal
end
