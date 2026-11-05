module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Cutoffs
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic

/-!
# Relating shell prefixes to the primitive producer's cutoffs

The primitive graph-family producer realizes the ball regularizations
`complexPhysicalCutoff`. A graph-shell prefix is its dyadic subsequence minus
the contracting ball. On the producer's fixed closed frequency carrier away
from zero, that contracting term vanishes uniformly for all sufficiently large
prefixes. All low shells are retained in the prefix; none are discarded by an
additional hypothesis. Consumer: identifying the shell strong limit with the
actual elapsed integral in `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph.PhysicalShells LowBounds.FrequencyCutoff
variable {n q : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false

/-- The dyadic indices used to match the graph-shell prefixes are cofinal
in the producer's original regularization sequence
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem tendsto_graphShell_producer_indices :
    Tendsto (fun N : ℕ ↦ 2 ^ N - 1) atTop atTop := by
  apply tendsto_atTop_mono (f := fun N : ℕ ↦ N) _ tendsto_id
  intro N
  have h := Nat.lt_two_pow_self (n := N)
  omega

/-- The expanding shell prefix is exactly a ball cutoff of the primitive
graph-family producer, not a different regularization profile
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem expandingCutoff_eq_producer_dyadic (N : ℕ) (ξ : E) :
    expandingCutoff N ξ = physicalCutoff (2 ^ N - 1) ξ := by
  have hrad : radius (2 ^ N - 1) = (2 : ℝ) ^ N := by
    simp only [radius, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_add_cancel]
  simp only [expandingCutoff, physicalCutoff, hrad, frequencyBump, profile]

/-- The contracting part of a shell prefix vanishes uniformly on the
producer's fixed closed carrier away from zero. This is a consequence of that
carrier, not a deletion of the low-frequency shells
(`app:ch_regular:eq:chain-tail`). -/
theorem eventually_contractingCutoff_zero_on_carrier
    {F : Set E} (hF : IsClosed F) (hzero : (0 : E) ∉ F) :
    ∀ᶠ N : ℕ in atTop, ∀ ξ ∈ F, contractingCutoff N ξ = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hF.isOpen_compl.mem_nhds hzero)
  have hlim : Tendsto (fun N : ℕ ↦ (2 : ℝ) ^ N * ε) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hε
  filter_upwards [hlim.eventually (eventually_ge_atTop 2)] with N hN
  intro ξ hξ
  have hnorm : ε ≤ ‖ξ‖ := by
    by_contra h
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h) hξ
  apply (frequencyBump n).zero_of_le_dist
  change 2 ≤ dist ((2 : ℝ) ^ N • ξ) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact hN.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))

/-- Every sufficiently long graph-shell prefix realizes exactly the same
cut full amplitude as a cofinal primitive regularization. The equality is
uniform over all amplitudes supported in the fixed carrier, hence over all
elapsed times and both literal orientations. The input `hχeq` is exported
verbatim by `exists_elapsedGraphFamily_of_primitive_phase`; no new strong
limit premise is introduced (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem eventually_graphShell_prefix_eq_producer
    {F : Set E} (hF : IsClosed F) (hzero : (0 : E) ∉ F)
    (χ : ℕ → E → ℂ)
    (hχeq : ∀ (A : FullAmplitude n q), (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) A =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) A) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : FullAmplitude n q),
      (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      frequencyCutFullAmplitude (fun ξ ↦ (∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ)) A =
        frequencyCutFullAmplitude (χ (2 ^ N - 1)) A := by
  filter_upwards [eventually_contractingCutoff_zero_on_carrier hF hzero] with N hN
  intro A hA
  rw [hχeq A hA]
  funext x y ξ
  by_cases hξ : ξ ∈ F
  · simp only [frequencyCutFullAmplitude, sum_graphCutoff, hN ξ hξ, sub_zero,
      expandingCutoff_eq_producer_dyadic, complexPhysicalCutoff]
  · simp [frequencyCutFullAmplitude, hA x y ξ hξ]

/-- The same cofinal cutoff identification holds in the literal Hilbert
adjoint order, by conjugate transposition of the forward identity. Neither
physical amplitude position is interchanged. Consumer: the adjoint elapsed
strong limit in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem eventually_graphShell_prefix_eq_producer_adjoint
    {F : Set E} (hF : IsClosed F) (hzero : (0 : E) ∉ F)
    (χ : ℕ → E → ℂ)
    (hχeq : ∀ (A : FullAmplitude n q), (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) A =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) A) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : FullAmplitude n q),
      (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      frequencyCutFullAmplitude (fun ξ ↦ (∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ))
          (fun x y ξ ↦ (A x y ξ).conjTranspose) =
        frequencyCutFullAmplitude (fun ξ ↦ star (χ (2 ^ N - 1) ξ))
          (fun x y ξ ↦ (A x y ξ).conjTranspose) := by
  filter_upwards [eventually_graphShell_prefix_eq_producer hF hzero χ hχeq] with N hN
  intro A hA
  have he := congrArg (fun B : FullAmplitude n q ↦ fun x y ξ ↦ (B x y ξ).conjTranspose)
    (hN A hA)
  funext x y ξ
  have hp := congrFun (congrFun (congrFun he x) y) ξ
  simpa only [frequencyCutFullAmplitude, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal] using hp

/-- Every finite prefix retains the low graph shells and still vanishes
near the frequency origin. This supplies the finite-kernel Fourier recovery
in `app:ch_regular:eq:chain-tail`. -/
theorem zero_notMem_tsupport_graphPrefix (N : ℕ) :
    (0 : E) ∉ tsupport (fun ξ ↦ ∑ j ∈ Finset.range N, graphCutoff j ξ) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hz := (Finset.eventually_all (Finset.range N)).mpr
    (fun j _ ↦ notMem_tsupport_iff_eventuallyEq.mp (zero_notMem_tsupport_graphCutoff (n := n) j))
  filter_upwards [hz] with ξ hξ
  simp only [Finset.sum_eq_zero (fun j hj ↦ hξ j hj), Pi.zero_apply]

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
