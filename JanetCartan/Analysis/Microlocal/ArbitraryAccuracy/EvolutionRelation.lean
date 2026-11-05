module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation.Suspension
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimePhase
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Phase

/-!
# The direct elapsed graph and its actual Hamilton flow

For `app:ch_regular:lem:finite-chain`, use the literal `elapsedPhase`
`Θ_r = (t-r)τ + Ψ(t,t-r,y,η)`. Both time identities of the constructed two-time
phase identify its full canonical relation, including the input base and
arbitrary input temporal covector. `exists_local_elapsed_hamilton_graph`
instantiates the local phase constructor from a smooth homogeneous root.

Differentiation in elapsed time imposes zero source energy at interior
stationarity; the zero-time boundary is the full diagonal. These are distinct
from the all-energy graph at fixed elapsed time. A forward chain's elapsed
times telescope inside the fixed slab, independently of depth.

The consumers are the primitive graph-localization instantiation, the
integrated-kernel stationarity argument and the connection to initialized
protection. This is a local geometric deduction, not the quantitative response:
common coefficient-family buffers, the match to the actual protected pencil,
the operator identification, all residual branches and all analytic tail
estimates still have to be instantiated by their actual producers.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- The two-time phase constructed from the actual inverse flow chart, in the
curried format of the fixed-time representation
(`app:ch_regular:lem:finite-chain`). -/
def chartPhase (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
    (TwoTimePoint (Euclidean d))) : TwoTimePhase d :=
  fun t s y η ↦ twoTimePhase C (t, (s, (y, η)))

/-- The point of the two-time chart used by the literal elapsed phase
(`app:ch_regular:lem:finite-chain`). -/
def elapsedChartPoint (r : ℝ) (x ξ : Euclidean (d + 1)) :
    TwoTimePoint (Euclidean d) :=
  (x 0, (x 0 - r, (spatialPart x, spatialPart ξ)))

/-- The input base determined by `∂ξ Θ_r`; its physical time is `t-r`
(`app:ch_regular:eq:joint-stationary`). -/
def elapsedInputBase (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
    (TwoTimePoint (Euclidean d))) (r : ℝ) (x ξ : Euclidean (d + 1)) :
    Euclidean (d + 1) :=
  timeSpacePoint (x 0 - r) ((C.symm (elapsedChartPoint r x ξ)).2.2.1)

/-- The output covector determined by `∂x Θ_r`. Both Hamilton--Jacobi time
terms are retained, so the formula holds at every input temporal covector
(`app:ch_regular:eq:joint-stationary`). -/
def elapsedOutputCovector (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r : ℝ) (x ξ : Euclidean (d + 1)) : Euclidean (d + 1) :=
  let q := elapsedChartPoint r x ξ
  let z := (C.symm q).2.2.1
  let p := (twoTimeState Φ (C.symm q)).2.2
  timeSpacePoint (ξ 0 + h (q.1, (q.2.2.1, p)) - h (q.2.1, (z, q.2.2.2))) p

/-- Differentiate the actual elapsed phase in its physical output position.
The input is the differential proved by `hasFDerivAt_twoTimePhase`, not an
assumed canonical relation (`app:ch_regular:eq:joint-stationary`). -/
theorem hasFDerivAt_elapsedChartPhase_output
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    HasFDerivAt (fun u ↦ elapsedPhase (chartPhase C) r u ξ)
      (innerSL ℝ (elapsedOutputCovector h Φ C r x ξ)) x := by
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := x)
  have hc := ht.prodMk ((ht.sub_const r).prodMk
    (spatialPartCLM.hasFDerivAt.prodMk (hasFDerivAt_const (𝕜 := ℝ) (spatialPart ξ) x)))
  have hd := ((ht.sub_const r).mul_const (ξ 0)).add (hphase.comp x hc)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [elapsedOutputCovector, twoTimePhaseDifferential, inner_eq_time_add_spatial,
    elapsedChartPoint]
  ring

/-- Differentiate the actual elapsed phase in its full input covector,
including the source-base time equation (`app:ch_regular:eq:joint-stationary`). -/
theorem hasFDerivAt_elapsedChartPhase_covector
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    HasFDerivAt (elapsedPhase (chartPhase C) r x)
      (innerSL ℝ (elapsedInputBase C r x ξ)) ξ := by
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := ξ)
  have hc := (hasFDerivAt_const (𝕜 := ℝ) (x 0) ξ).prodMk
    ((hasFDerivAt_const (𝕜 := ℝ) (x 0 - r) ξ).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) (spatialPart x) ξ).prodMk spatialPartCLM.hasFDerivAt))
  have hd := (ht.const_mul (x 0 - r)).add (hphase.comp ξ hc)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [elapsedInputBase, twoTimePhaseDifferential, inner_eq_time_add_spatial,
    elapsedChartPoint]

/-- The full canonical relation of `Θ_r`, at arbitrary temporal covector,
with the physical source base retained (`app:ch_regular:eq:joint-stationary`). -/
theorem forwardRelation_elapsedChartPhase_iff
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {z ξ x ζ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ ↔
      z = elapsedInputBase C r x ξ ∧ ζ = elapsedOutputCovector h Φ C r x ξ := by
  rw [FiniteChain.Graph.ForwardRelation,
    (hasFDerivAt_elapsedChartPhase_output hphase).fderiv,
    (hasFDerivAt_elapsedChartPhase_covector hphase).fderiv,
    innerSL_inj, innerSL_inj]
  tauto


/-- Evaluation of the inverse chart is evaluation of the SAME root flow at
elapsed time `r`. This uses all of the inverse-chart coordinate identities,
including the source time (`app:ch_regular:eq:joint-stationary`). -/
theorem twoTimeState_elapsedChartPoint
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {x ξ : Euclidean (d + 1)} (hq : elapsedChartPoint r x ξ ∈ C.target) :
    twoTimeState Φ (C.symm (elapsedChartPoint r x ξ)) =
      Φ (spacetimeRootState (elapsedInputBase C r x ξ, ξ), r) := by
  obtain ⟨ht, hs, hη, _⟩ := twoTimeChart_inverse_coordinates hC hq
  have hw : (C.symm (elapsedChartPoint r x ξ)).2 =
      spacetimeRootState (elapsedInputBase C r x ξ, ξ) := by
    apply Prod.ext
    · simpa [spacetimeRootState, elapsedInputBase, elapsedChartPoint] using hs
    · apply Prod.ext
      · simp [spacetimeRootState, elapsedInputBase]
      · exact hη
  change Φ ((C.symm (elapsedChartPoint r x ξ)).2,
    (C.symm (elapsedChartPoint r x ξ)).1 - (C.symm (elapsedChartPoint r x ξ)).2.1) = _
  rw [ht, hs, hw]
  simp only [elapsedChartPoint, sub_sub_cancel]

/-- The full elapsed graph is the lift of the original root flow at the
input energy `τ-h`. This is an all-energy identity. The clock and chart
hypotheses are outputs of `exists_localTwoTimeHamiltonPhase`; there is no
identification with an unrelated fixed-transverse retarded operator
(`app:ch_regular:lem:finite-chain`). -/
theorem forwardRelation_elapsedChartPhase_flow
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {z ξ x ζ : Euclidean (d + 1)}
    (hq : elapsedChartPoint r x ξ ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r x ξ))).1 = x 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ) :
    (x, ζ) = rootSuspensionState h (rootSuspension h (z, ξ))
      (Φ (spacetimeRootState (z, ξ), r)) ∧ z 0 + r = x 0 := by
  obtain ⟨rfl, rfl⟩ := (forwardRelation_elapsedChartPhase_iff hphase).mp hrel
  have hflow := twoTimeState_elapsedChartPoint hC hq
  have hy := (twoTimeChart_inverse_coordinates hC hq).2.2.2
  rw [← hflow]
  constructor
  · apply Prod.ext
    · change x = timeSpacePoint _ _
      rw [hclock, hy]
      exact (timeSpacePoint_coordinates x).symm
    · have hstate : twoTimeState Φ (C.symm (elapsedChartPoint r x ξ)) =
          (x 0, (spatialPart x, (twoTimeState Φ (C.symm (elapsedChartPoint r x ξ))).2.2)) :=
        Prod.ext hclock (Prod.ext hy rfl)
      dsimp only [elapsedOutputCovector, rootSuspensionState]
      rw [hstate]
      simp only [rootSuspension, spacetimeRootState, elapsedInputBase,
        timeSpacePoint_time, spatialPart_timeSpacePoint, elapsedChartPoint]
      congr 1
      ring
  · simp [elapsedInputBase]

/-- The elapsed graph preserves `τ-h` at every temporal covector, as a
consequence of its identified flow (`app:ch_regular:lem:finite-chain`). -/
theorem forwardRelation_elapsedChartPhase_energy
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {z ξ x ζ : Euclidean (d + 1)}
    (hq : elapsedChartPoint r x ξ ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r x ξ))).1 = x 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ) :
    rootSuspension h (x, ζ) = rootSuspension h (z, ξ) := by
  rw [(forwardRelation_elapsedChartPhase_flow hC hq hclock hphase hrel).1,
    rootSuspension_rootSuspensionState]

/-- The full base equation of the elapsed graph gives its exact
elapsed time. No characteristic-set restriction is used
(`app:ch_regular:lem:finite-chain`). -/
theorem forwardRelation_elapsedChartPhase_time
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {z ξ x ζ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ) :
    x 0 - z 0 = r := by
  rw [(forwardRelation_elapsedChartPhase_iff hphase).mp hrel |>.1]
  simp [elapsedInputBase]

/-- For a finite chain of actual elapsed graphs the total elapsed time is
exactly the endpoint time difference. Thus increasing proof depth does not
enlarge the physical slab (`app:ch_regular:lem:finite-chain`). -/
theorem elapsed_graph_chain_total_time
    (h : ℕ → RootState (Euclidean d) → ℝ)
    (Φ : ℕ → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : ℕ → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r : ℕ → ℝ) (z : ℕ → Euclidean (d + 1) × Euclidean (d + 1)) (N : ℕ)
    (hphase : ∀ j < N, HasFDerivAt (twoTimePhase (C j))
      (twoTimePhaseDifferential (h j) (Φ j) (C j)
        (elapsedChartPoint (r j) (z (j + 1)).1 (z j).2))
      (elapsedChartPoint (r j) (z (j + 1)).1 (z j).2))
    (hrel : ∀ j < N, FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase (C j)) (r j))
      (z j).1 (z j).2 (z (j + 1)).1 (z (j + 1)).2) :
    ∑ j ∈ Finset.range N, r j = (z N).1 0 - (z 0).1 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih
      (fun j hj ↦ hphase j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hrel j (Nat.lt_succ_of_lt hj)),
      ← forwardRelation_elapsedChartPhase_time (hphase N (Nat.lt_succ_self N))
        (hrel N (Nat.lt_succ_self N))]
    ring


/-- All intermediate bases of a forward elapsed-graph chain stay between
its endpoint times, and its total integration time is bounded by the same
fixed slab length independently of depth (`app:ch_regular:lem:finite-chain`). -/
theorem elapsed_graph_chain_fixed_slab
    (h : ℕ → RootState (Euclidean d) → ℝ)
    (Φ : ℕ → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : ℕ → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r : ℕ → ℝ) (z : ℕ → Euclidean (d + 1) × Euclidean (d + 1)) (N : ℕ)
    (hphase : ∀ j < N, HasFDerivAt (twoTimePhase (C j))
      (twoTimePhaseDifferential (h j) (Φ j) (C j)
        (elapsedChartPoint (r j) (z (j + 1)).1 (z j).2))
      (elapsedChartPoint (r j) (z (j + 1)).1 (z j).2))
    (hrel : ∀ j < N, FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase (C j)) (r j))
      (z j).1 (z j).2 (z (j + 1)).1 (z (j + 1)).2)
    (hr : ∀ j < N, 0 ≤ r j) {a b : ℝ} (ha : a ≤ (z 0).1 0) (hb : (z N).1 0 ≤ b) :
    (∀ j ≤ N, (z j).1 0 ∈ Icc a b) ∧
      (∑ j ∈ Finset.range N, r j) ≤ b - a := by
  have htotal := elapsed_graph_chain_total_time h Φ C r z N hphase hrel
  constructor
  · intro j hj
    have hjtotal := elapsed_graph_chain_total_time h Φ C r z j
      (fun k hk ↦ hphase k (hk.trans_le hj))
      (fun k hk ↦ hrel k (hk.trans_le hj))
    have hnonneg : 0 ≤ ∑ k ∈ Finset.range j, r k :=
      Finset.sum_nonneg (fun k hk ↦ hr k ((Finset.mem_range.mp hk).trans_le hj))
    have hle : (∑ k ∈ Finset.range j, r k) ≤ ∑ k ∈ Finset.range N, r k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
        (fun k hk _ ↦ hr k (Finset.mem_range.mp hk))
    constructor <;> linarith
  · linarith


/-- Construct the local elapsed Hamilton graph from the smooth homogeneous
root. The phase differential, both canonical derivatives, the lifted ODE at
EVERY energy and the full flow relation are conclusions of the existing
two-time phase constructor. This supplies the geometric primitive for the
direct factors of `app:ch_regular:lem:finite-chain`; it does not instantiate
the finite current-coefficient family or assert any operator estimate. -/
theorem exists_local_elapsed_hamilton_graph
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ c : ℝ in 𝓝 1, h (z.1, (z.2.1, c • z.2.2)) = c * h z)
    {z₀ : RootState (Euclidean d)} (hz₀ : z₀ ∈ D) :
    ∃ R > (0 : ℝ), ∃ ε > (0 : ℝ),
    ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
    ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      C.source ⊆ twoTimeDomain z₀ R ε ∧ (z₀.1, z₀) ∈ C.target ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      (∀ w ∈ Metric.ball z₀ R, Φ (w, 0) = w) ∧
      (∀ w ∈ Metric.ball z₀ R, ∀ u ∈ Ioo (-ε) ε, ∀ e : ℝ,
        HasDerivAt (fun v ↦ rootSuspensionState h e (Φ (w, v)))
          (HamiltonPhase.hamiltonFieldOfDifferential
            (fderiv ℝ (rootSuspension h) (rootSuspensionState h e (Φ (w, u))))) u) ∧
      ∀ r x ξ, elapsedChartPoint r x ξ ∈ C.target →
        HasFDerivAt (fun u ↦ elapsedPhase (chartPhase C) r u ξ)
          (innerSL ℝ (elapsedOutputCovector h Φ C r x ξ)) x ∧
        HasFDerivAt (elapsedPhase (chartPhase C) r x)
          (innerSL ℝ (elapsedInputBase C r x ξ)) ξ ∧
        ∀ z ζ, FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ →
          (x, ζ) = rootSuspensionState h (rootSuspension h (z, ξ))
            (Φ (spacetimeRootState (z, ξ), r)) ∧ z 0 + r = x 0 := by
  obtain ⟨R, hR, ε, hε, Φ, C, _, hi, hd, hm, _, hclock, hC, hsource,
    _, hzC, _, _, hsmooth, hphase, _⟩ := exists_localTwoTimeHamiltonPhase hD hh hhom hz₀
  refine ⟨R, hR, ε, hε, Φ, C, hC, hsource, hzC, hsmooth, hi, ?_, ?_⟩
  · intro w hw u hu e
    have hhd : DifferentiableAt ℝ h (Φ (w, u)) :=
      (hh.contDiffAt (hD.mem_nhds (hm w hw u hu))).differentiableAt (by simp)
    have hhd' : DifferentiableAt ℝ h
        (spacetimeRootState (rootSuspensionState h e (Φ (w, u)))) := by
      simpa only [spacetimeRootState_rootSuspensionState] using hhd
    rw [← rootSuspensionField_eq_differential hhd']
    exact hasDerivAt_rootSuspensionState e hhd (hd w hw u hu)
  · intro r x ξ hq
    refine ⟨hasFDerivAt_elapsedChartPhase_output (hphase _ hq),
      hasFDerivAt_elapsedChartPhase_covector (hphase _ hq), ?_⟩
    intro z ζ hrel
    have hc := hclock _ (hsource (C.map_target hq))
    rw [(twoTimeChart_inverse_coordinates hC hq).1] at hc
    exact forwardRelation_elapsedChartPhase_flow hC hq hc (hphase _ hq) hrel


/-- Differentiation in elapsed time retains the source-time Hamilton--Jacobi
term. Its stationary equation is the ORIGINAL source energy `τ-h=0`
(`app:ch_regular:lem:finite-chain`, retarded interior branch). -/
theorem hasDerivAt_elapsedChartPhase_elapsed
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    HasDerivAt (fun u ↦ elapsedPhase (chartPhase C) u x ξ)
      (-rootSuspension h (elapsedInputBase C r x ξ, ξ)) r := by
  have hs := (hasDerivAt_const r (x 0)).sub (hasDerivAt_id r)
  have hc := (hasDerivAt_const r (x 0)).prodMk
    (hs.prodMk ((hasDerivAt_const r (spatialPart x)).prodMk
      (hasDerivAt_const r (spatialPart ξ))))
  have hd := (hs.mul_const (ξ 0)).add (hphase.comp_hasDerivAt r hc)
  convert! hd using 1
  simp [twoTimePhaseDifferential, rootSuspension, spacetimeRootState,
    elapsedInputBase, elapsedChartPoint]
  ring

/-- Interior stationarity of the elapsed integration enforces zero energy
on its full canonical relation. This is distinct from the all-energy graph
at one fixed elapsed time (`app:ch_regular:lem:finite-chain`). -/
theorem elapsed_graph_interior_stationary_energy
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {z ξ x ζ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ)
    (hstationary : deriv (fun u ↦ elapsedPhase (chartPhase C) u x ξ) r = 0) :
    rootSuspension h (z, ξ) = 0 := by
  rw [(hasDerivAt_elapsedChartPhase_elapsed hphase).deriv, neg_eq_zero] at hstationary
  simpa only [(forwardRelation_elapsedChartPhase_iff hphase).mp hrel |>.1] using hstationary

/-- At the zero elapsed-time boundary, the actual inverse chart and the
initial condition of its flow give the full diagonal, including both base
and covector. Consumer: the boundary branch of the direct retarded kernel
in `app:ch_regular:lem:finite-chain`. -/
theorem elapsed_graph_zero_diagonal
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {z ξ x ζ : Euclidean (d + 1)} (hq : elapsedChartPoint 0 x ξ ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 x ξ)).2, 0) = (C.symm (elapsedChartPoint 0 x ξ)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 x ξ)) (elapsedChartPoint 0 x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) 0) z ξ x ζ) :
    z = x ∧ ζ = ξ := by
  obtain ⟨ht, hs, hη, hy⟩ := twoTimeChart_inverse_coordinates hC hq
  have hstate : twoTimeState Φ (C.symm (elapsedChartPoint 0 x ξ)) =
      (C.symm (elapsedChartPoint 0 x ξ)).2 := by
    change Φ (_, (C.symm (elapsedChartPoint 0 x ξ)).1 -
      (C.symm (elapsedChartPoint 0 x ξ)).2.1) = _
    rw [ht, hs]
    simpa only [elapsedChartPoint, sub_zero, sub_self] using hi
  rw [hstate] at hy
  obtain ⟨rfl, rfl⟩ := (forwardRelation_elapsedChartPhase_iff hphase).mp hrel
  constructor
  · dsimp only [elapsedInputBase]
    rw [hy]
    simpa only [elapsedChartPoint, sub_zero] using timeSpacePoint_coordinates x
  · dsimp only [elapsedOutputCovector]
    rw [hstate, hη, hy]
    simp only [elapsedChartPoint, sub_zero, add_sub_cancel_right, timeSpacePoint_coordinates]

end JanetCartan.ArbitraryAccuracy
