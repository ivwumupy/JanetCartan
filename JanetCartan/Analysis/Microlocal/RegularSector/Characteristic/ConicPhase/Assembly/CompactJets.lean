module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.TimeSpace

/-!
# Actual compact sets for the conic phase budgets

The fixed section and radial interval construct the compact sets required by
`JetBounds`; their normalized images lie in the original closed buffer.
Constants precede the local phase and every radial scale, with derivative
shift zero. Consumer: `app:ch_regular_base:lem:retarded-kernel` and its
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral KernelIdentification FullAmplitudePrimitiveBudget.Local
variable {d : ℕ}

/-- A compact radial band of the fixed angular section, used for the
normalized jets in `app:ch_regular_base:lem:retarded-kernel`. -/
def radialSectionBand (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε a b : ℝ) :
    Set (Euclidean d) :=
  (fun p : ℝ × Euclidean d ↦ p.1 • p.2) ''
    (Icc a b ×ˢ (closedBall η₀ ε ∩ {η | ℓ η = 1}))

/-- Compactness is geometric and independent of the phase
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isCompact_radialSectionBand (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε a b : ℝ) : IsCompact (radialSectionBand ℓ η₀ ε a b) :=
  (isCompact_Icc.prod ((isCompact_closedBall η₀ ε).inter_right
    (isClosed_eq ℓ.continuous continuous_const))).image (continuous_fst.smul continuous_snd)

/-- The actual compact radial band has positive linear coordinate and
normalizes into the closed local frequency ball
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem radialSectionBand_normalizes {ℓ : Euclidean d →L[ℝ] ℝ}
    {η₀ η : Euclidean d} {ε a b : ℝ} (ha : 0 < a)
    (hη : η ∈ radialSectionBand ℓ η₀ ε a b) :
    0 < ℓ η ∧ (ℓ η)⁻¹ • η ∈ closedBall η₀ ε := by
  obtain ⟨⟨r, θ⟩, ⟨hr, hθ, hℓθ⟩, rfl⟩ := hη
  change ℓ θ = 1 at hℓθ
  have hr0 : 0 < r := ha.trans_le hr.1
  simp only [map_smul, smul_eq_mul, hℓθ, mul_one]
  exact ⟨hr0, by simpa only [inv_smul_smul₀ hr0.ne'] using hθ⟩

/-- The compact joint jet set, with both original times retained
(`app:ch_regular_base:eq:fixed-time-representation`). -/
def bufferedJetSet (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    (ε a b : ℝ) : Set (SymbolBudgets.TwoTimePoint d) :=
  (closedBall z.1 (2 * ε) ×ˢ (closedBall z.1 (2 * ε) ×ˢ
    closedBall z.2.1 (2 * ε))) ×ˢ radialSectionBand ℓ z.2.2 ε a b

/-- The fixed joint jet set is compact (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isCompact_bufferedJetSet (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : RootState (Euclidean d)) (ε a b : ℝ) : IsCompact (bufferedJetSet ℓ z ε a b) :=
  ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod
      (isCompact_radialSectionBand ℓ z.2.2 ε a b)

/-- Every point of the actual compact set normalizes into the SAME original
buffer; this discharges the compact image premise of `JetBounds` in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem bufferedJetSet_normalizes (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε a b : ℝ} (hε : 0 ≤ ε) (ha : 0 < a) :
    (∀ p ∈ bufferedJetSet ℓ z ε a b, 0 < ℓ p.2) ∧
    MapsTo (normalize ℓ ∘ budgetCoordinates) (bufferedJetSet ℓ z ε a b)
      (closedBall (z.1, z) (2 * ε)) := by
  constructor
  · intro p hp
    exact (radialSectionBand_normalizes ha hp.2).1
  · intro p hp
    have hη := (radialSectionBand_normalizes ha hp.2).2
    have hη' : (ℓ p.2)⁻¹ • p.2 ∈ closedBall z.2.2 (2 * ε) :=
      closedBall_subset_closedBall (by linarith) hη
    change (p.1.1, (p.1.2.1, (p.1.2.2, (ℓ p.2)⁻¹ • p.2))) ∈
      closedBall (z.1, z) (2 * ε)
    simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using
        And.intro hp.1.1 (And.intro hp.1.2.1 (And.intro hp.1.2.2 hη'))

/-- Fully instantiated normalized joint phase estimates on the constructed
compact band. The constant precedes the phase, the radial scale and every
jet through order `n`. The only analytic input is original local smoothness;
the derivative shift is zero (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_buffered_normalized_jet_bound (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε a b : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    {U : Set (TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ U) (n : ℕ) :
    ∃ A > (0 : ℝ), ∀ F : TwoTimePoint (Euclidean d) → ℝ,
      ContDiffOn ℝ ∞ F U → ∀ R > (0 : ℝ),
      cNorm (bufferedJetSet ℓ z ε a b) n
        (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase R
          (curriedExtend ℓ F))) ≤ A * cNorm (closedBall (z.1, z) (2 * ε)) n F ∧
      ∀ k ≤ n, ∀ p ∈ bufferedJetSet ℓ z ε a b,
        ‖iteratedFDeriv ℝ k (SymbolBudgets.jointPhase
          (SymbolBudgets.normalizedTwoTimePhase R (curriedExtend ℓ F))) p‖ ≤
            A * cNorm (closedBall (z.1, z) (2 * ε)) n F :=
  exists_normalizedTwoTimePhase_jet_bound ℓ (isCompact_bufferedJetSet ℓ z ε a b)
    (isCompact_closedBall _ _) hU hbuffer (bufferedJetSet_normalizes ℓ hε ha).1
      (bufferedJetSet_normalizes ℓ hε ha).2 n

/-- Compact elapsed jet set with a dummy source position and bounded time
frequency; its spatial band is fixed before the phase and elapsed time
(`app:ch_regular_base:eq:fixed-time-representation`). -/
def elapsedJetSet (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    (ε a b T : ℝ) : Set (Point (d + 1)) :=
  (((fun p : ℝ × Euclidean d ↦ timeSpacePoint p.1 p.2) ''
    (closedBall z.1 ε ×ˢ closedBall z.2.1 ε)) ×ˢ {0}) ×ˢ
  ((fun p : ℝ × Euclidean d ↦ timeSpacePoint p.1 p.2) ''
    (Icc (-T) T ×ˢ radialSectionBand ℓ z.2.2 ε a b))

/-- Compactness of the actual elapsed jet set
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isCompact_elapsedJetSet (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : RootState (Euclidean d)) (ε a b T : ℝ) : IsCompact (elapsedJetSet ℓ z ε a b T) :=
  ((((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
    continuous_timeSpacePoint).prod (isCompact_singleton (x := (0 : Euclidean (d + 1))))).prod
      ((isCompact_Icc.prod (isCompact_radialSectionBand ℓ z.2.2 ε a b)).image
        continuous_timeSpacePoint)

/-- All elapsed times send the actual compact set into the same original
joint jet set. This closes the elapsed inclusion premise rather than
postulating a phase estimate (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedJetSet_mapsTo (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε a b T r : ℝ} (hr : r ∈ Icc 0 ε) :
    MapsTo (SymbolBudgets.elapsedPoint r) (elapsedJetSet ℓ z ε a b T)
      (bufferedJetSet ℓ z ε a b) := by
  rintro p ⟨⟨⟨⟨t, y⟩, ⟨ht, hy⟩, hx⟩, _⟩, ⟨⟨τ, η⟩, ⟨_, hη⟩, hξ⟩⟩
  have hε : 0 ≤ ε := hr.1.trans hr.2
  have hs : dist (t - r) z.1 ≤ 2 * ε := by
    calc
      _ ≤ dist (t - r) t + dist t z.1 := dist_triangle _ _ _
      _ = r + dist t z.1 := by simp [Real.dist_eq, abs_of_nonneg hr.1]
      _ ≤ 2 * ε := by linarith [show dist t z.1 ≤ ε from ht, hr.2]
  simp only [bufferedJetSet, mem_prod, SymbolBudgets.elapsedPoint_eq, ← hx, ← hξ,
    timeSpacePoint_time, spatialPart_timeSpacePoint]
  exact ⟨⟨closedBall_subset_closedBall (by linarith) ht,
    hs, closedBall_subset_closedBall (by linarith) hy⟩, hη⟩

/-- The normalized elapsed phase reserve on an explicit compact set is
controlled by the original closed-buffer jets, with constants independent
of the phase, positive radial scale and elapsed time. No analytic compact
inclusion remains to be supplied (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem norm_iteratedFDeriv_buffered_elapsed_le (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε a b T : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    {U : Set (TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ U)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {R r : ℝ} (hR : 0 < R) (hr : r ∈ Icc 0 ε)
    {n k : ℕ} (hk : k ≤ n) {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : SymbolBudgets.phasePairInclusion p ∈ elapsedJetSet ℓ z ε a b T) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (WholeImageGeometry.normalizedPhase R
      (elapsedPhase (curriedExtend ℓ F) r))) p‖ ≤
        SymbolBudgets.phaseTimeConstant (elapsedJetSet ℓ z ε a b T) n ε +
          jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε a b) n *
            cNorm (closedBall (z.1, z) (2 * ε)) n F :=
  norm_iteratedFDeriv_normalizedElapsedPhase_curriedExtend_le ℓ
    (isCompact_elapsedJetSet ℓ z ε a b T) (isCompact_bufferedJetSet ℓ z ε a b)
    (isCompact_closedBall _ _) hU hbuffer (bufferedJetSet_normalizes ℓ hε ha).1
    (bufferedJetSet_normalizes ℓ hε ha).2 hF hR hr (elapsedJetSet_mapsTo ℓ hr) hk hp

end JanetCartan.RegularSector.Characteristic.ConicPhase
