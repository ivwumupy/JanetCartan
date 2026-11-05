module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Component pairings of the supported graph limits

The vector distributional realization supplies the three scalar component limits
in `app:ch_regular_base:eq:direct-graph-identity`. Compact tests on the physical
plateau remove the auxiliary output cutoff. Local continuity proves the
integrability needed to commute coordinate projection with the integral.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap
namespace JanetCartan.FourierIntegral.SupportedConjugation
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "L²" => Lp V 2 (volume : Measure E)

/-- The coordinate form of the actual Euclidean L² distribution, consumed by
`graphPhysicalDistributionPairing` in the supported direct graph identity.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
def coordinateDistribution (f : L²) : 𝓢'(E, Fin r → ℂ) :=
  PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ)
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).toContinuousLinearMap
    (f : 𝓢'(E, V))

/-- The source test `D_t u = -i ∂_t u`, in the same Euclidean test space.
Consumer: the transport graph in `app:ch_regular_base:eq:direct-graph-identity`. -/
def sourceTimeTest (t : Fin n) (u : graphTestSpace n r) : graphTestSpace n r :=
  -Complex.I • graphTestPartialDeriv t u

/-- Coordinate identification of the actual source derivative. No physical
Fourier normalization is absorbed into the test.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem sourceTimeTest_coordinates (t : Fin n) (u : graphTestSpace n r) (y : E) :
    ((sourceTimeTest t u).val y).ofLp =
      -Complex.I • partialDeriv (fun z ↦ (u.val z).ofLp) y t := by
  change (-Complex.I • (graphTestPartialDeriv t u).val y).ofLp = _
  rw [WithLp.ofLp_smul, graphTestPartialDeriv_coordinates]

/-- A vector realization gives component convergence for any locally equal
continuous graph sequence on the physical plateau. This is the pairing bridge
for all three undifferentiated graphs; its realization input is produced by
`exists_supported_twoTerm_fullGraph_realizations` in the final assembly.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem tendsto_component_pairing_of_realization
    {K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ}
    {χ : ℕ → E → ℂ} {a : FullAmplitude n r} {T : L² →L[ℂ] L²}
    (hreal : GraphDistributionalRealization K χ a T)
    (u : graphTestSpace n r) {O : Set E} (hO : IsOpen O)
    (g : ℕ → E → Fin r → ℂ) (hg : ∀ k, ContinuousOn (g k) O)
    (he : ∀ k, EqOn
      (K (frequencyCutFullAmplitude (χ k) a) (fun y ↦ (u.val y).ofLp)) (g k) O)
    (φ : 𝓢(E, ℂ)) (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ O) (i : Fin r) :
    Tendsto (fun k ↦ ∫ x, φ x * g k x i) atTop
      (𝓝 (coordinateDistribution (T (graphTestToLp u)) φ i)) := by
  let L := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i
  have ht := L.continuous.tendsto _ |>.comp (hreal u φ)
  have hpair (k) : Integrable (fun x ↦ φ x • WithLp.toLp 2 (g k x)) := by
    apply Continuous.integrable_of_hasCompactSupport _ hK.smul_right
    apply continuous_of_tsupport
    intro x hx
    have hxO : x ∈ O := hs (tsupport_smul_subset_left _ _ hx)
    exact φ.continuous.continuousAt.smul
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.continuous.continuousAt.comp
        ((hg k).continuousAt (hO.mem_nhds hxO)))
  apply ht.congr
  intro k
  change L (∫ x, φ x • WithLp.toLp 2
    (K (frequencyCutFullAmplitude (χ k) a) (fun y ↦ (u.val y).ofLp) x)) = _
  rw [show (∫ x, φ x • WithLp.toLp 2
      (K (frequencyCutFullAmplitude (χ k) a) (fun y ↦ (u.val y).ofLp) x)) =
      ∫ x, φ x • WithLp.toLp 2 (g k x) from by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ O
    · rw [he k hx]
    · simp [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))]]
  exact (L.integral_comp_comm (hpair k)).symm

end JanetCartan.FourierIntegral.SupportedConjugation
