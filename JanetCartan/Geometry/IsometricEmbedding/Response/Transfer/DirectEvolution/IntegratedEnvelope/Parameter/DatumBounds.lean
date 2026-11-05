module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.DatumBridge
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Local bounds for the actual original mixed datum jets

The primitive joint annular endpoint consumes L² norms of `iteratedFDeriv` of
the ORIGINAL datum on physical/parameter slices. Smoothness and a fixed compact
source support bound those norms on any compact parameter set. All jet orders
use the same parameter neighborhood; no integrated output is assumed.

Consumer: local domination in
`Parameter.TimeDifferentiation.orderedTransferAction_elapsedIntegral`, instantiated
with `AnnularSobolev.JointAssembly` and `ReverseAssembly.Joint`.
Sources: `app:ch_response:lem:energy-carrier-jets` and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "Vf" => EuclideanSpace ℂ (Fin r)

/-- The original mixed Fréchet jets have one L² profile uniform over a
compact parameter set. Support of all derivatives is proved from support of the
original datum; every L² membership and norm bound is constructed. This supplies
the datum input to the fixed-time primitive endpoint (`new:eq:carrier-ibp`). -/
theorem exists_originalDatumJet_compact_l2_bounds
    (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    {Q : Set P} (hQ : IsCompact Q) :
    ∃ Ddata : ℕ → ℝ, (∀ j, 0 ≤ Ddata j) ∧ ∀ c ∈ Q, ∀ j : ℕ,
      ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j a (x, c)) 2 volume,
        ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j a (x, c))‖ ≤ Ddata j := by
  have hsupp : tsupport a ⊆ K ×ˢ (univ : Set P) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_univ)
    intro q hq
    refine ⟨?_, mem_univ _⟩
    by_contra h
    exact hq (hs q h)
  have hzero (j : ℕ) (c : P) (x : E) (hx : x ∉ K) :
      iteratedFDeriv ℝ j a (x, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hj
    exact hx (hsupp ((tsupport_iteratedFDeriv_subset j) hj)).1
  choose B hB using fun j : ℕ ↦ (hK.prod hQ).exists_bound_of_continuousOn
    (ha.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ ∞)).continuousOn
  let I : Lp ℝ 2 (volume : Measure E) := indicatorConstLp 2
    hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)
  refine ⟨fun j ↦ max 0 (B j) * ‖I‖, fun j ↦ mul_nonneg (le_max_left _ _) (norm_nonneg _), ?_⟩
  intro c hc j
  have hcont : Continuous (fun x : E ↦ iteratedFDeriv ℝ j a (x, c)) :=
    (ha.continuous_iteratedFDeriv (by simp)).comp (continuous_id.prodMk continuous_const)
  have hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j a (x, c)) 2 volume :=
    hcont.memLp_of_hasCompactSupport
      (HasCompactSupport.intro hK (hzero j c)) (p := (2 : ENNReal))
  refine ⟨hm, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := I)
  filter_upwards [hm.coeFn_toLp, indicatorConstLp_coeFn (μ := (volume : Measure E))
    (p := 2) (hs := hK.measurableSet) (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))]
    with x hx hI
  rw [hx]
  change ‖iteratedFDeriv ℝ j a (x, c)‖ ≤ max 0 (B j) * ‖I x‖
  change _ ≤ max 0 (B j) * ‖indicatorConstLp 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ) x‖
  rw [hI]
  by_cases hxK : x ∈ K
  · simp only [indicator_of_mem hxK, norm_one, mul_one]
    exact (hB j (x, c) ⟨hxK, hc⟩).trans (le_max_right _ _)
  · simp [indicator_of_notMem hxK, hzero j c x hxK]

/-- Around each parameter in its original open domain, one common closed
ball bounds every original mixed L² jet. The profile is local and qualitative;
the final quantitative estimate still uses the original datum profile at the
chosen parameter. Consumer: Bochner differentiation for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_originalDatumJet_local_l2_bounds [FiniteDimensional ℝ P]
    (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    {U : Set P} (hU : IsOpen U) {c : P} (hc : c ∈ U) :
    ∃ ε > 0, Metric.closedBall c ε ⊆ U ∧ ∃ Ddata : ℕ → ℝ,
      (∀ j, 0 ≤ Ddata j) ∧ ∀ b ∈ Metric.closedBall c ε, ∀ j : ℕ,
      ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j a (x, b)) 2 volume,
        ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j a (x, b))‖ ≤ Ddata j := by
  let : ProperSpace P := FiniteDimensional.proper_rclike ℝ P
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  exact ⟨ε, hε, hεU,
    exists_originalDatumJet_compact_l2_bounds a ha hK hs (isCompact_closedBall c ε)⟩

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
