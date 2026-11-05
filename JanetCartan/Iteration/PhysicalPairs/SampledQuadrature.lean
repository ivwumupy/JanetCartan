module

public import JanetCartan.Iteration.PhysicalPairs.SampledHistory
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledMetric
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.CurrentPhases
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# Literal signed stress quadrature on the very same external outer sample

Read the native colored current's ORIGINAL radial carrier family *before* any
point or source test. Its normalized scalar phase uses the previously chosen
original pair (not a second representation). For the unmodified supplied final
Schwartz waves the actual complete demodulated derivatives, second-amplitude
conjugation on the minus term, original χ₂, original stress multiplier, and
original full projected stress give the exact real quadrature at the previously
entered `λ*beat`. This is the datum of `OriginalSampledObserved.FirstMaskInput`,
not a first-mask decay estimate or a bound on the primary waves.
`app:ch_pairs:eq:pairs-lag-one-error`, `app:ch_pairs:lem:pairs-ledger`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 16000
open Set Metric
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.SampledQuadrature
open ActualCarriers CurrentFullPhase FrozenMenu ConstructedSignedGeometry SignedPairs SignedProductEstimates
open ResponseTransfer.SourceNegative ResponseSourceExtension ProjectedStressFrame UniformStep Sampling.BackgroundModulation

/-- The unaltered original colored scalar family. Its gradient is the
`currentGroup` on the native chart; colors remain in the radial multiplier. -/
def radialCarrier {n : ℕ} {D : CoverData n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {G : Type} (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : G → ℝ) (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T i).family.threshold) : G → Euclidean 3 → Euclidean n → ℝ :=
  fun g z y ↦ R g * (T (assign g)).carrier ⟨Q,hQ,hlow (assign g)⟩ y z

/-- The gradient of the normalized scalar is exactly the unrecentered native
signed covector divided by its true beat, not merely a direction in its cone. -/
theorem gradient_radial_pair {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {G : Type} (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : G → ℝ) (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T i).family.threshold)
    (q : Pair G (Euclidean 3) (groupCube D assign)) (x : Euclidean n)
    (hx : ∀ i, x ∈ ball (0 : Euclidean n) (T i).physicalRadius) :
    gradient (fun y ↦ q.vector (fun g z ↦ radialCarrier T assign R Q hQ hlow g z y) / q.beat) x =
      q.beat⁻¹ • q.vector (ConstructedSignedGeometry.currentGroup T assign R Q hQ hlow x) := by
  let φ := radialCarrier T assign R Q hQ hlow
  have hd (g) (z) (hz : z ∈ groupCube D assign g) : DifferentiableAt ℝ (φ g z) x := by
    let Tg := T (assign g)
    have hp := (hD.2.2.2.2.1 (assign g).1 (assign g).2).1
    have hz' : z ∈ parameterInterior (2 * (D.patches (assign g).1 (assign g).2).radius) :=
      parameterCube_subset_doubledInterior hp.1 hz
    let cg : Euclidean n × Euclidean 3 → ℝ := fun v ↦ Tg.carrier ⟨Q,hQ,hlow (assign g)⟩ v.1 v.2
    have ht : ContDiffAt ℝ ∞ cg (x,z) := (Tg.carrier_smooth hp ⟨Q,hQ,hlow (assign g)⟩).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds ⟨hx (assign g),hz'⟩)
    have hs : ContDiffAt ℝ ∞ (fun y : Euclidean n ↦ (y,z)) x := contDiffAt_id.prodMk contDiffAt_const
    have hslice : ContDiffAt ℝ ∞ (fun y ↦ cg (y,z)) x := ht.comp (g := cg) (f := fun y ↦ (y,z)) x hs
    exact (hslice.differentiableAt (by simp)).const_mul (R g)
  have hg (g) (z) (hz : z ∈ groupCube D assign g) : gradient (φ g z) x =
      ConstructedSignedGeometry.currentGroup T assign R Q hQ hlow x g z :=
    (currentGroup_eq_gradient_radial_carrier hD T assign R Q hQ hlow g (hx _) hz).symm
  apply (InnerProductSpace.toDual ℝ (Euclidean n)).injective
  rw [toDual_gradient,fderiv_normalized_signed_pair_phase q φ hd,map_smul]
  congr 1
  cases q with
  | difference g z w hne =>
    simp only [Pair.vector,map_sub,←hg g z z.property,←hg g w w.property,toDual_gradient]
  | sum g z w =>
    simp only [Pair.vector,map_add,←hg g z z.property,←hg g w w.property,toDual_gradient]
  | cross g k hne z w s t hs ht =>
    simp only [Pair.vector,map_add,map_smul,←hg g z z.property,←hg k w w.property,toDual_gradient]

/-- Use the exact original compact coefficient ball containing the whole
physical chart to reach every selected outer carrier's native spatial domain. -/
theorem chart_in_carriers {d : ℕ} (hn : 5 ≤ d+1) (r μ : ℝ) (hr : 0 < r) (hμ : 0 < μ)
    {K : Set (Euclidean (d+1))} {M : ℝ}
    (f : RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily
      (ball 0 (PhysicalSeed.OriginalBoundary.b hn)) 0
      (PhysicalInitialization.OriginalRegular.coreRadius hn (PhysicalInitialization.OriginalRegular.screenedRadius hn r μ))
      (cubeStress (d+1)) K M) (t : ℝ) (y : Euclidean (d+1))
    (hy : y ∈ ball (0 : Euclidean (d+1)) (min t f.physicalRadius)) :
    ∀ a, y ∈ ball (0 : Euclidean (d+1)) (PhysicalSeed.OriginalBoundary.T hn a).physicalRadius := by
  have hy' := ball_subset_closedBall ((ball_subset_ball (min_le_right t f.physicalRadius)) hy)
  have hc := f.physicalBall_coefficientDomain ((closedBall_subset_closedBall
    (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 4*f.physicalRadius)) hy')
  exact fun a ↦ ((PhysicalInitialization.OriginalRegular.core_spec hn
    (PhysicalInitialization.OriginalRegular.screened_pos hn hr hμ)).2.2.2 a).2 hc

theorem gradient_source_mem {E : Type} (K : Set E) {v w : E} (h : v=w) (hw : w ∈ K) : v ∈ K := h.symm ▸ hw

theorem carrier_ne_zero {lam beat : ℝ} (h : 2 ≤ lam*beat) : lam ≠ 0 := by
  rintro rfl
  norm_num at h

/-- Apply the *given* original scalar pair identity to the full derivatives of
Schwartz waves, then its original real row; there is no choice of a pair or an
assumption about a factorized leading amplitude. -/
theorem reduced_form {n N : ℕ} {G I : Type} {S : G → Set (Euclidean 3)}
    (q : Pair G (Euclidean 3) S) (φ : G → Euclidean 3 → Euclidean n → ℝ)
    (g : I → G) (z : I → Euclidean 3) (minus : Bool) (i j : I)
    (hp : ∀ f : G → Euclidean 3 → ℝ, q.vector f =
      if minus then f (g i) (z i)-f (g j) (z j) else f (g i) (z i)+f (g j) (z j))
    (χ η : Euclidean n → ℝ) (Q : Euclidean n → Fin n → MetricTensor n) (lam : ℝ) (hlam : lam ≠ 0)
    (W : I → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N))) :
    let θ := fun k y ↦ lam * φ (g k) (z k) y
    let A := sampledDerivativeAmplitude (fun k ↦ (W k : Euclidean n → EuclideanSpace ℂ (Fin N))) θ
    let ϕ := fun y ↦ q.vector (fun a v ↦ φ a v y) / q.beat
    let tensor := fun y ↦ if minus then symmetricBilinearTensor (A i y) ((A j y).map conj)
      else symmetricBilinearTensor (A i y) (A j y)
    (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η (AmbientResponse.stressSource Q
      (fun x ↦ χ x • (if minus then ProductSum.minusSource θ A i j x else ProductSum.plusSource θ A i j x))) y)) =
      fun y ↦ euclideanRealPart (modulatedSource χ ϕ
        (fun x ↦ η x • ((1/2:ℝ) • complexStressContraction (Q x) (tensor x))) (lam*q.beat) y) := by
  intro θ A ϕ tensor
  cases minus with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
    rw [cutoff_plusSource_eq_real_signedPair_source q φ g z i j hp χ A hlam]
    exact cutoff_stressSource_real_modulated_eq Q χ η ϕ tensor (lam*q.beat)
  | true =>
    simp only [↓reduceIte] at hp ⊢
    rw [cutoff_minusSource_eq_real_signedPair_source q φ g z i j hp χ A hlam]
    exact cutoff_stressSource_real_modulated_eq Q χ η ϕ tensor (lam*q.beat)
end JanetCartan.PhysicalPairs.SampledQuadrature
end

public meta section
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.SampledQuadrature
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.SampledQuadrature
private def samples := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def tail (p : Expr) : Nat → Expr
  | 0 => p
  | j+1 => tail (.proj ``And 1 p) j

/- Avoid introducing even a temporary point of χ₂'s support. The projected
component of a generic state is all the scalar family depends upon. -/
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (samples ++ `projected)).type (some 42) fun x _ => do
    let projected := a (samples ++ `projected) x
    let e := a (col ++ `family_eq_currentGroup) x[:22].toArray
    forallBoundedTelescope (← inferType e) (some 1) fun state eq => do
      let c := eq.getAppArgs.back!
      unless c.isAppOfArity `JanetCartan.ActualCarriers.ConstructedSignedGeometry.currentGroup 12 do throwError "missing native colored covectors"
      let replace := fun (exp : Expr) => exp.replace fun y =>
        match y with
        | .proj ``Prod 0 z => if z == state[0]! then some projected else none
        | _ => if y.isAppOfArity ``Prod.fst 3 && y.appArg! == state[0]! then some projected else none
      let fixed := c.getAppArgs[:11].toArray.map replace
      for i in [:fixed.size] do
        if (fixed[i]!.find? fun z => z == state[0]!).isSome then throwError "scalar phase retained point dependence at currentGroup slot {i}"
      let Q ← store (ns ++ `Q) x fixed[8]! true
      unless fixed[8]!.isAppOf `JanetCartan.ProjectedStressFrame.projectedStress do throwError "lost raw projected stress"
      let hQ ← store (ns ++ `Q_smooth) x fixed[9]! false (some ((← inferType fixed[9]!).replace fun z => if z == fixed[8]! then some Q else none))
      let low ← store (ns ++ `Q_low) x fixed[10]! false (some ((← inferType fixed[10]!).replace fun z => if z == fixed[8]! then some Q else none))
      discard <| store (ns ++ `group_phase) x (a (ns ++ `radialCarrier) (((fixed.set! 8 Q).set! 9 hQ).set! 10 low)) true
  logInfo "literal original radial scalar family on the actual projected graph, with no physical point/shift/sign selected"

run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p family => do
    unless p.size == 49 && family.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily 34 do throwError "missing actual signed sample label"
    let fixed := family.getAppArgs[:23].toArray
    let reached := Expr.proj ``And 0 (a (hist ++ `measured_history) p)
    let now := p[:36].toArray ++ #[p[37]!,reached] ++ p[39:43].toArray
    let cert := a (hist ++ `native_window) p
    let window := Expr.proj ``And 0 cert
    let spec := Expr.proj ``And 0 (.proj ``And 1 cert)
    let hscalar := tail spec 4
    let hfreq := Expr.proj ``And 0 (tail window 2)
    let prod := (← inferType hfreq).getAppArgs.back!
    let lam := prod.getAppArgs[prod.getAppNumArgs-2]!
    let hne ← mkAppM (ns ++ `carrier_ne_zero) #[hfreq]
    let χ := (← inferType (a (masks ++ `χ₂_smooth) fixed)).appArg!
    let η := (← inferType (a (masks ++ `χsrc_smooth) fixed)).appArg!
    let Q := a (ns ++ `Q) now
    let φ := a (ns ++ `group_phase) now
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := a `JanetCartan.embeddingDimension #[n]
    let some q := (← inferType hscalar).find? (fun e => e.isAppOfArity (samples ++ `pair) 30) | throwError "lost original signed pair"
    forallBoundedTelescope (← inferType hscalar) (some 1) fun f eq => do
      let some atI := eq.getAppArgs.back!.find? (fun e => e.getAppFn == f[0]! && e.getAppNumArgs == 2 &&
        (e.find? fun z => z == p[46]!).isSome) | throwError "missing original outer row/node of first sample"
      let group ← mkLambdaFVars #[p[46]!] atI.getAppArgs[0]!
      let node ← mkLambdaFVars #[p[46]!] atI.getAppArgs[1]!
      let reduced ← mkAppOptM (ns ++ `reduced_form) #[n,N,none,none,none,q,φ,group,node,p[45]!,p[46]!,p[47]!,
        hscalar,χ,η,Q,lam,hne]
      discard <| store (ns ++ `reduced_on_original_sample) p reduced
    let reg := `JanetCartan.PhysicalInitialization.OriginalRegular
    let fix := #[n] ++ fixed[1:21].toArray
    let cap := a `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,p[1]!,fix[20]!]
    let sel := fix.set! 20 cap
    let f := a (reg ++ `f) fixed
    let fa := (← inferType f).getAppArgs
    let xArgs := #[p[0]!,p[1]!,a `JanetCartan.PhysicalInitialization.OriginalProtected.r fix,
      a `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure sel,
      a `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 fix,
      a `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure sel,fa[fa.size-2]!,fa.back!,f,a (reg ++ `r) fixed]
    let c := ((← getConstInfo (ns ++ `group_phase)).value! (allowOpaque := true)).beta now
    unless c.isAppOfArity (ns ++ `radialCarrier) 11 do throwError "missing unaltered native scalar phase"
    let ca := c.getAppArgs
    let hD := a `JanetCartan.PhysicalSeed.OriginalBoundary.hD #[n,p[1]!]
    let ht := (← inferType hD).getAppArgs
    let grad := #[n,ca[1]!,ht[ht.size-2]!,ht.back!,hD] ++ ca[2:11].toArray ++ #[q]
    let K := a (col ++ `Ksource) p[:22].toArray
    let input := a (samples ++ `on_actual_chart) now
    forallBoundedTelescope (← inferType input) (some 2) fun y _ => do
      let hh := a (ns ++ `chart_in_carriers) (xArgs ++ y)
      let he := a (ns ++ `gradient_radial_pair) (grad ++ #[y[0]!,hh])
      let angular := mkAppN input (y ++ #[q])
      let mem := tail angular 3
      let eType ← inferType he
      let target := eType.replace fun e => if e == c then some φ else none
      let eq ← store (ns ++ `gradient_on_chart) (p ++ y) he false (some target)
      discard <| store (ns ++ `gradient_in_source) (p ++ y) (← mkAppM (ns ++ `gradient_source_mem) #[K,eq,mem])
  logInfo "original χ₂ once, original stress cutoff/full Q; exact real signed product of complete derivative amplitudes at SAME external pair/frequency for the final supplied Schwartz waves; literal gradient in the original source annulus"
end JanetCartan.PhysicalPairs.SampledQuadrature
end
