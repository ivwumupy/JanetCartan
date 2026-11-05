module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation.Coordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeLiouville
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability

/-!
# Lifting the root flow to every temporal energy

For the direct-evolution connection in `app:ch_regular:lem:finite-chain`, the
field of `τ-h` is derived from its scalar differential. A root trajectory lifts
to this field at every energy. Uniqueness and concatenation use the same smooth
root on the entire compared trajectories, deriving the required Lipschitz bound
from their compact images. These lemmas do not identify the current pencil's
root with the initialized protection symbol; that is a separate obligation.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- Forget the temporal covector, retaining the physical root state in
`app:ch_regular:lem:finite-chain`. -/
def spacetimeRootState (z : Euclidean (d + 1) × Euclidean (d + 1)) :
    RootState (Euclidean d) := (z.1 0, (spatialPart z.1, spatialPart z.2))

/-- The scalar Hamiltonian of the elapsed graph. It is defined at all
energies, not only on the characteristic set (`app:ch_regular:lem:finite-chain`). -/
def rootSuspension (h : RootState (Euclidean d) → ℝ)
    (z : Euclidean (d + 1) × Euclidean (d + 1)) : ℝ :=
  z.2 0 - h (spacetimeRootState z)

/-- Restore the temporal covector at a fixed energy. The spatial curve is
exactly the one constructed in `TwoTimeFlow`
(`app:ch_regular:lem:finite-chain`). -/
def rootSuspensionState (h : RootState (Euclidean d) → ℝ) (e : ℝ)
    (z : RootState (Euclidean d)) : Euclidean (d + 1) × Euclidean (d + 1) :=
  (timeSpacePoint z.1 z.2.1, timeSpacePoint (e + h z) z.2.2)

/-- The lift retains the same root state
(`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem spacetimeRootState_rootSuspensionState
    (h : RootState (Euclidean d) → ℝ) (e : ℝ) (z : RootState (Euclidean d)) :
    spacetimeRootState (rootSuspensionState h e z) = z := by
  simp [spacetimeRootState, rootSuspensionState]

/-- The arbitrary temporal energy is unchanged by the lifted root state
(`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem rootSuspension_rootSuspensionState
    (h : RootState (Euclidean d) → ℝ) (e : ℝ) (z : RootState (Euclidean d)) :
    rootSuspension h (rootSuspensionState h e z) = e := by
  simp [rootSuspension, rootSuspensionState, spacetimeRootState]

/-- The Hamilton velocity of `τ-h`, written in literal physical coordinates.
It will be identified with the derivative of the scalar Hamiltonian
(`app:ch_regular:lem:finite-chain`). -/
def rootSuspensionField (h : RootState (Euclidean d) → ℝ)
    (z : Euclidean (d + 1) × Euclidean (d + 1)) :
    Euclidean (d + 1) × Euclidean (d + 1) :=
  let w := spacetimeRootState z
  (timeSpacePoint 1 (-rootMomentumGradient h w),
    timeSpacePoint (fderiv ℝ h w (1, (0, 0))) (rootPositionGradient h w))

/-- The full physical differential of `τ-h`, including its time term.
Consumer: comparison with the retained protected Hamilton flow
(`app:ch_regular:thm:no-return`). -/
theorem hasFDerivAt_rootSuspension
    {h : RootState (Euclidean d) → ℝ}
    {z : Euclidean (d + 1) × Euclidean (d + 1)}
    (hh : DifferentiableAt ℝ h (spacetimeRootState z)) :
    HasFDerivAt (rootSuspension h)
      (HamiltonPhase.hamiltonDifferential (-(rootSuspensionField h z).2)
        (rootSuspensionField h z).1) z := by
  have hx := (ContinuousLinearMap.fst ℝ (Euclidean (d + 1)) (Euclidean (d + 1))).hasFDerivAt (x := z)
  have hp := (ContinuousLinearMap.snd ℝ (Euclidean (d + 1)) (Euclidean (d + 1))).hasFDerivAt (x := z)
  have ht (v : Euclidean (d + 1)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := v)
  have hc := ((ht z.1).comp z hx).prodMk ((spatialPartCLM.hasFDerivAt.comp z hx).prodMk
    (spatialPartCLM.hasFDerivAt.comp z hp))
  have hd := ((ht z.2).comp z hp).sub (hh.hasFDerivAt.comp z hc)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [HamiltonPhase.hamiltonDifferential_apply, inner_neg_left,
    rootSuspensionField, inner_eq_time_add_spatial, timeSpacePoint_time,
    spatialPart_timeSpacePoint, inner_neg_left,
    sub_apply, ContinuousLinearMap.comp_apply]
  change -(fderiv ℝ h (spacetimeRootState z) (1, (0, 0)) * v.1 0 +
      inner ℝ (rootPositionGradient h (spacetimeRootState z)) (spatialPart v.1)) +
      (1 * v.2 0 - inner ℝ (rootMomentumGradient h (spacetimeRootState z)) (spatialPart v.2)) =
    v.2 0 - fderiv ℝ h (spacetimeRootState z) (spacetimeRootState v)
  conv_rhs => rw [root_fderiv_split]
  dsimp [spacetimeRootState]
  ring

/-- The displayed velocity is the Hamilton field of the actual scalar
`τ-h`; no Hamilton field is inserted as a hypothesis
(`app:ch_regular:lem:finite-chain`). -/
theorem rootSuspensionField_eq_differential
    {h : RootState (Euclidean d) → ℝ}
    {z : Euclidean (d + 1) × Euclidean (d + 1)}
    (hh : DifferentiableAt ℝ h (spacetimeRootState z)) :
    rootSuspensionField h z =
      HamiltonPhase.hamiltonFieldOfDifferential (fderiv ℝ (rootSuspension h) z) := by
  rw [(hasFDerivAt_rootSuspension hh).fderiv]
  have hx : (HamiltonPhase.hamiltonDifferential (-(rootSuspensionField h z).2)
      (rootSuspensionField h z).1).comp
        (ContinuousLinearMap.inl ℝ (Euclidean (d + 1)) (Euclidean (d + 1))) =
      InnerProductSpace.toDual ℝ _ (-(rootSuspensionField h z).2) := by
    ext v
    simp
  have hp : (HamiltonPhase.hamiltonDifferential (-(rootSuspensionField h z).2)
      (rootSuspensionField h z).1).comp
        (ContinuousLinearMap.inr ℝ (Euclidean (d + 1)) (Euclidean (d + 1))) =
      InnerProductSpace.toDual ℝ _ (rootSuspensionField h z).1 := by
    ext v
    simp
  simp [HamiltonPhase.hamiltonFieldOfDifferential, hx, hp]

/-- Along the actual root ODE, only the explicit time derivative changes
`h`; the spatial Hamilton terms cancel
(`app:ch_regular:lem:finite-chain`). -/
theorem root_fderiv_along_hamiltonField (h : RootState (Euclidean d) → ℝ)
    (z : RootState (Euclidean d)) :
    fderiv ℝ h z (rootHamiltonField h z) = fderiv ℝ h z (1, (0, 0)) := by
  rw [root_fderiv_split]
  simp [rootHamiltonField, real_inner_comm]

/-- Lift an actual root solution at any fixed energy to the Hamilton ODE
of `τ-h`. Consumer: full elapsed-graph relations in
`app:ch_regular:lem:finite-chain`. -/
theorem hasDerivAt_rootSuspensionState
    {h : RootState (Euclidean d) → ℝ} {Z : ℝ → RootState (Euclidean d)}
    {u : ℝ} (e : ℝ) (hh : DifferentiableAt ℝ h (Z u))
    (hZ : HasDerivAt Z (rootHamiltonField h (Z u)) u) :
    HasDerivAt (fun v ↦ rootSuspensionState h e (Z v))
      (rootSuspensionField h (rootSuspensionState h e (Z u))) u := by
  have ht := (ContinuousLinearMap.fst ℝ ℝ (Euclidean d × Euclidean d)).hasFDerivAt.comp_hasDerivAt u hZ
  have hy := ((ContinuousLinearMap.fst ℝ (Euclidean d) (Euclidean d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d))).hasFDerivAt.comp_hasDerivAt u hZ
  have hp := ((ContinuousLinearMap.snd ℝ (Euclidean d) (Euclidean d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d))).hasFDerivAt.comp_hasDerivAt u hZ
  have hh' := (hh.hasFDerivAt.comp_hasDerivAt u hZ).const_add e
  have hd := (timeSpacePointCLM.hasFDerivAt.comp_hasDerivAt u (ht.prodMk hy)).prodMk
    (timeSpacePointCLM.hasFDerivAt.comp_hasDerivAt u (hh'.prodMk hp))
  change HasDerivAt (fun v ↦ rootSuspensionState h e (Z v))
    (timeSpacePoint 1 (-rootMomentumGradient h (Z u)),
      timeSpacePoint (fderiv ℝ h (Z u) (rootHamiltonField h (Z u)))
        (rootPositionGradient h (Z u))) u at hd
  rw [root_fderiv_along_hamiltonField] at hd
  simpa only [rootSuspensionField, spacetimeRootState_rootSuspensionState] using hd


/-- Two solutions of the SAME smooth root field agree on their whole
common time interval. The Lipschitz bound is obtained from the compact
union of the actual trajectories, not assumed. Consumer: identifying the
direct evolution with retained protected flow charts
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`). -/
theorem rootHamiltonCurve_unique
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    {Z Y : ℝ → RootState (Euclidean d)} {a b : ℝ}
    (hZ : ∀ u ∈ Icc a b, HasDerivAt Z (rootHamiltonField h (Z u)) u)
    (hY : ∀ u ∈ Icc a b, HasDerivAt Y (rootHamiltonField h (Y u)) u)
    (hZD : MapsTo Z (Icc a b) D) (hYD : MapsTo Y (Icc a b) D)
    (hi : Z a = Y a) : EqOn Z Y (Icc a b) := by
  let K := Z '' Icc a b ∪ Y '' Icc a b
  have hZc : ContinuousOn Z (Icc a b) := fun u hu ↦ (hZ u hu).continuousAt.continuousWithinAt
  have hYc : ContinuousOn Y (Icc a b) := fun u hu ↦ (hY u hu).continuousAt.continuousWithinAt
  have hK : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hZc).union (isCompact_Icc.image_of_continuousOn hYc)
  have hKD : K ⊆ D := by
    rintro z (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact hZD hu
    · exact hYD hu
  have hfield := (contDiffOn_rootHamiltonField hD hh).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hloc : LocallyLipschitzOn K (rootHamiltonField h) := by
    intro z hz
    obtain ⟨L, U, hU, hL⟩ := (hfield.contDiffAt (hD.mem_nhds (hKD hz))).exists_lipschitzOnWith
    exact ⟨L, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hloc
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ rootHamiltonField h)
    (s := fun _ ↦ K) (fun _ _ ↦ hL) hZc
    (fun u hu ↦ (hZ u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu ↦ Or.inl ⟨u, Ico_subset_Icc_self hu, rfl⟩) hYc
    (fun u hu ↦ (hY u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu ↦ Or.inr ⟨u, Ico_subset_Icc_self hu, rfl⟩) hi

/-- Consecutive root-flow pieces concatenate to the SAME flow whenever
the entire two compared trajectories lie in the common root domain.
This is derived from ODE uniqueness, not a stipulated composition law
(`app:ch_regular:lem:finite-chain`). -/
theorem rootFlow_add_of_whole_segments
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (z : RootState (Euclidean d)) (r : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hi : Φ (Φ (z, r), 0) = Φ (z, r))
    (hfirst : ∀ u ∈ Icc 0 s, HasDerivAt (fun v ↦ Φ (Φ (z, r), v))
      (rootHamiltonField h (Φ (Φ (z, r), u))) u)
    (hsecond : ∀ u ∈ Icc 0 s, HasDerivAt (fun v ↦ Φ (z, v))
      (rootHamiltonField h (Φ (z, r + u))) (r + u))
    (hfirstD : ∀ u ∈ Icc 0 s, Φ (Φ (z, r), u) ∈ D)
    (hsecondD : ∀ u ∈ Icc 0 s, Φ (z, r + u) ∈ D) :
    Φ (Φ (z, r), s) = Φ (z, r + s) := by
  apply rootHamiltonCurve_unique hD hh hfirst (Y := fun u ↦ Φ (z, r + u))
    (fun u hu ↦ ?_) hfirstD hsecondD (by simpa only [add_zero] using hi) ⟨hs, le_rfl⟩
  simpa only [one_smul, Function.comp_def] using
    (hsecond u hu).scomp u ((hasDerivAt_id u).const_add r)


end JanetCartan.ArbitraryAccuracy
