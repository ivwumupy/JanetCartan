module
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.CubeGeometry

/-! # Carrier upper bound and genuine size jets at each original signed pair

The lower bound for lag does not yield an upper carrier bound. Only the
actual same-group difference may have beat different from one, and its two
points belong to the SAME original compact parameter cube. The phase used in
the size estimate is the actual sum/difference of complete sampled angles
divided by λ·beat, with no doubled-frequency convention.
`app:ch_pairs:eq:pairs-lag-sum-size`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace JanetCartan.PhysicalPairs.OriginalSizeFrequency
open FrozenMenu SignedPairs
variable {J Λ : Type} [Fintype J]

def cubePrice (radius : J → ℝ) : ℝ := max 1 (∑ j, diam (parameterCube (radius j)))

theorem cubePrice_nonneg (radius : J → ℝ) : 0 ≤ cubePrice radius := zero_le_one.trans (le_max_left _ _)

theorem beat_bound (radius : J → ℝ) (q : Pair (J × Λ) (Euclidean 3) (fun g ↦ parameterCube (radius g.1))) : q.beat ≤ cubePrice radius := by
  cases q with
  | sum => exact le_max_left _ _
  | cross => exact le_max_left _ _
  | difference g z w _ =>
    have hd := dist_le_diam_of_mem (isCompact_parameterCube (radius g.1)).isBounded z.property w.property
    rw [dist_eq_norm] at hd
    exact hd.trans ((Finset.single_le_sum (f := fun j ↦ diam (parameterCube (radius j))) (fun _ _ ↦ diam_nonneg) (Finset.mem_univ g.1)).trans (le_max_right _ _))

theorem true_upper (radius : J → ℝ) (q : Pair (J × Λ) (Euclidean 3) (fun g ↦ parameterCube (radius g.1))) {R : ℝ} (hR : 1 ≤ R) :
    R^carrierExponent*q.beat ≤ cubePrice radius*R^carrierExponent := (mul_le_mul_of_nonneg_left (beat_bound radius q) (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans_eq (mul_comm _ _)

theorem fine_le_carrier (C R₀ : ℝ) (h₀ : OriginalWindow.scaleThreshold C ≤ R₀) (j : ℕ) :
    let R := historyScale R₀ growthExponent j
    OriginalWindow.fineScale C R ≤ R^carrierExponent := by
  intro R
  have hR := OriginalWindow.stage_one C R₀ h₀ j
  have hh : R^(-separationExponent) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num [separationExponent])
  simpa only [mul_one] using (OriginalWindow.history_pair_window C R₀ h₀ j 1 (by linarith : R^(-separationExponent)/2 ≤ 1)).2.2.2.2

variable {n : ℕ} {G I : Type} {S : G → Set (Euclidean 3)}
local notation "E" => Euclidean n

theorem angle_ratio (q : Pair G (Euclidean 3) S) (φ : G → Euclidean 3 → E → ℝ) (g : I → G) (z : I → Euclidean 3)
    (minus : Bool) (i j : I) (h : ∀ f : G → Euclidean 3 → ℝ, q.vector f = if minus then f (g i) (z i)-f (g j) (z j) else f (g i) (z i)+f (g j) (z j))
    (lam : ℝ) (hlam : lam ≠ 0) :
    let θ := fun k x ↦ lam * φ (g k) (z k) x
    (fun x ↦ (if minus then θ i x - θ j x else θ i x + θ j x)/(lam*q.beat)) = fun x ↦ q.vector (fun a v ↦ φ a v x)/q.beat := by
  intro θ
  funext x
  rw [h]
  cases minus <;> simp only [Bool.false_eq_true,↓reduceIte,θ,← mul_add,← mul_sub] <;> field_simp [hlam,q.beat_pos.ne']

def phasePrice (D : ℕ → ℝ) (k : ℕ) : ℝ := OriginalFirstMask.phaseCost D (k-1)

theorem phasePrice_nonneg (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k) (k : ℕ) : 0 ≤ phasePrice D k := OriginalFirstMask.phaseCost_nonneg D hD (k-1)

theorem same_jets (V : Set E) (ext raw angle : E → ℝ) (D : ℕ → ℝ) (L : ℝ)
    (hext : ContDiff ℝ ∞ ext) (hg : ∀ x ∈ V, ext =ᶠ[𝓝 x] raw) (he : angle = raw)
    (hj : ∀ x ∈ V, ∀ j, ‖iteratedFDeriv ℝ (j+1) ext x‖ ≤ OriginalFirstMask.phaseCost D j * L^j) :
    ContDiffOn ℝ ∞ angle V ∧ ∀ x ∈ V, ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k angle x‖ ≤ phasePrice D k*L^(k-1) := by
  subst angle
  constructor
  · exact fun x hx ↦ (hext.contDiffAt.congr_of_eventuallyEq (hg x hx).symm).contDiffWithinAt
  · intro x hx k hk
    cases k with
    | zero => omega
    | succ j =>
      rw [← ((hg x hx).iteratedFDeriv ℝ (j+1)).eq_of_nhds]
      simpa only [phasePrice,Nat.add_sub_cancel] using hj x hx j
end JanetCartan.PhysicalPairs.OriginalSizeFrequency
end
public meta section
set_option maxHeartbeats 1100000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSizeFrequency
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSizeFrequency
private def geom := `JanetCartan.PhysicalPairs.OriginalMaskGeometry
private def hs := `JanetCartan.PhysicalPairs.SampledHistory
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "prove_native_size_frequencies " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hs ++ `index)).type (some 49) fun p gf => do
    let base := p[:22].toArray
    let J := a (outer ++ `Index) base
    let jraw := ((← getConstInfo (outer ++ `Index)).value! (allowOpaque := true)).beta base
    let fi ← synthInstance (mkApp (mkConst `Fintype [.zero]) jraw)
    let r := a (outer ++ `parameterRadius) base
    let cost := a (ns ++ `cubePrice) #[J,fi,r]
    if piece.getNat == 0 then
      let named ← store (ns ++ `constant) base cost true
      let pf := a (ns ++ `cubePrice_nonneg) #[J,fi,r]
      discard <| store (ns ++ `constant_nonneg) base pf false (some ((← inferType pf).replace fun e => if e == cost then some named else none))
      return
    let cert := a (hs ++ `native_window) p
    let some q := (← inferType cert).find? (fun e => e.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalSampledPairs.pair 30) | throwError "missing actual protection pair"
    let qa := q.getAppArgs
    let index := ((← getConstInfo (hs ++ `index)).value! (allowOpaque := true)).beta p
    let hT := index.getAppArgs[8]!
    let G := (← inferType q).getAppArgs[0]!
    let col := G.appArg!
    if piece.getNat == 1 then
      let pf := a (ns ++ `true_upper) #[J,col,fi,r,q,qa[23]!,qa[24]!]
      discard <| store (ns ++ `rho_le_carrier) p pf false (some ((← inferType pf).replace fun e => if e == cost then some (a (ns ++ `constant) base) else none))
      discard <| store (ns ++ `fine_le_lam) p (a (ns ++ `fine_le_carrier) #[p[36]!,p[37]!,hT,p[39]!])
      return
    let red := ((← getConstInfo (quad ++ `reduced_on_original_sample)).value! (allowOpaque := true)).beta p
    let v := red.getAppArgs
    unless red.isAppOfArity (quad ++ `reduced_form) 18 do throwError "changed original complete signed reduction"
    let ratio := a (ns ++ `angle_ratio) (#[v[0]!] ++ v[2:13].toArray ++ v[16:18].toArray)
    let tt ← whnfR (← inferType ratio)
    unless tt.isAppOfArity ``Eq 3 do throwError "lost original full sampled angle quotient"
    let V := a `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart gf.getAppArgs[:23].toArray
    let D := a `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile p[:36].toArray
    let window := Expr.proj ``And 0 cert
    let fine := (← inferType (.proj ``And 0 (.proj ``And 1 window))).appArg!
    let specs := a (ns ++ `same_jets) #[v[0]!,V,a (geom ++ `phase) p,tt.getAppArgs[2]!,tt.getAppArgs[1]!,D,fine,a (geom ++ `smooth) p,a (geom ++ `germ) p,ratio,a (geom ++ `higher_jets) p]
    discard <| store (ns ++ `angle_smooth) p (.proj ``And 0 specs)
    discard <| store (ns ++ `angle_jets) p (.proj ``And 1 specs)
prove_native_size_frequencies 0
prove_native_size_frequencies 1
prove_native_size_frequencies 2
end JanetCartan.PhysicalPairs.OriginalSizeFrequency
end
