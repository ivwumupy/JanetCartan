module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Support
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.SupportedCarrier

/-!
# Supported carriers of the literal elapsed amplitude

Consumers are `hcarrier`, `hKphase`, and `hphysical` of
`FiniteChain.Graph.exists_graph_factor_sobolev_bound_of_primitive_grades`.
The original spatial support is supplied by the two-time symbol, the conic
support by the multiplier, and the two base supports by the physical masks.
The constructions are independent of elapsed time. No shell, including the
contracting shells and source shoulders, is removed.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry

variable {d q : ℕ}

/-- The physical frequency support retains the multiplier and the original
spatial symbol cutoff (`app:ch_regular_base:eq:fixed-time-representation`). -/
def elapsedFrequencyCarrier (β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d)) :
    Set (Euclidean (d + 1)) := tsupport β ∩ spatialPart ⁻¹' F

/-- Closedness includes the entire frequency shoulder
(`app:ch_regular:eq:chain-tail`). -/
theorem isClosed_elapsedFrequencyCarrier (β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F) : IsClosed (elapsedFrequencyCarrier β F) :=
  (isClosed_tsupport _).inter (hF.preimage spatialPartCLM.continuous)

/-- The fixed normalized support, before intersection with a comparable
annulus. Taking the closure keeps limiting shoulders as the input scale
varies (`app:ch_regular:eq:joint-kernel-phase`). -/
def elapsedNormalizedFrequencyCarrier (β : Euclidean (d + 1) → ℂ)
    (F : Set (Euclidean d)) : Set (Euclidean (d + 1)) :=
  closure {ξ | ∃ ρ : ℝ, 1 ≤ ρ ∧ ρ • ξ ∈ elapsedFrequencyCarrier β F}

/-- The compact normalized phase carrier for all comparable physical pairs.
Its frequency radii are exactly those proved by `comparableGraphCarrier_subset`
(`app:ch_regular:eq:joint-kernel-phase`). -/
def elapsedComparableCarrier (χout β : Euclidean (d + 1) → ℂ)
    (F : Set (Euclidean d)) (c C a b : ℝ) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  tsupport χout ×ˢ
    (frequencyAnnulus (a / (16 * annulusFactor c C))
      (4 * max 1 (4 * annulusFactor c C * b)) ∩ elapsedNormalizedFrequencyCarrier β F)

/-- Compact physical phase carrier at each independent graph index. This
includes the low branch, without replacing its shrinking annulus by a high
frequency annulus (`app:ch_regular:eq:chain-tail`). -/
def elapsedPhysicalPhaseCarrier (χout β : Euclidean (d + 1) → ℂ)
    (F : Set (Euclidean d)) (low : Bool) (j : ℕ) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  tsupport χout ×ˢ
    (frequencyAnnulus (graphLower low j) (graphUpper low j) ∩ elapsedFrequencyCarrier β F)

/-- Compactness of the common comparable carrier is uniform in elapsed time,
input scale and shell indices (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_elapsedComparableCarrier
    {χout : Euclidean (d + 1) → ℂ} (hout : HasCompactSupport χout)
    (β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d)) (c C a b : ℝ) :
    IsCompact (elapsedComparableCarrier χout β F c C a b) :=
  hout.prod ((isCompact_frequencyAnnulus _ _).inter_right isClosed_closure)

/-- Every physical graph shell has a compact supported phase carrier,
including bounded graph frequencies (`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_elapsedPhysicalPhaseCarrier
    {χout : Euclidean (d + 1) → ℂ} (hout : HasCompactSupport χout)
    (β : Euclidean (d + 1) → ℂ) {F : Set (Euclidean d)} (hF : IsClosed F)
    (low : Bool) (j : ℕ) :
    IsCompact (elapsedPhysicalPhaseCarrier χout β F low j) :=
  hout.prod ((isCompact_frequencyAnnulus _ _).inter_right
    (isClosed_elapsedFrequencyCarrier β hF))

/-- A nonzero elapsed amplitude retains both physical masks and both
frequency restrictions. The spatial input is precisely the original symbol's
support assertion (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedAmplitude_mem_carrier
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0)
    (r : ℝ) {u z ξ : Euclidean (d + 1)}
    (hA : elapsedAmplitude b χout χsource β r u z ξ ≠ 0) :
    (u, z) ∈ tsupport χout ×ˢ tsupport χsource ∧ ξ ∈ elapsedFrequencyCarrier β F :=
  tsupport_elapsedAmplitude_subset b χout χsource β hF hb r
    (subset_tsupport _ (show FourierIntegral.FullAmplitudePrimitiveBudget.Local.uncurry
      (elapsedAmplitude b χout χsource β r) ((u, z), ξ) ≠ 0 from hA))

/-- The actual comparable amplitude support lies in the fixed normalized
phase carrier. No input shoulder or original spatial cutoff is discarded
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem elapsedAmplitude_mem_comparableCarrier
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0)
    {c C a b₀ ρ : ℝ} (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (hpair : IsComparablePair c C a b₀ ρ low j k) (r : ℝ)
    (u z ξ : Euclidean (d + 1))
    (hA : elapsedAmplitude b χout χsource β r u z (ρ • ξ) ≠ 0)
    (hg : graphBranchCutoff low j (ρ • ξ) ≠ 0) :
    (u, ξ) ∈ elapsedComparableCarrier χout β F c C a b₀ := by
  have hs := elapsedAmplitude_mem_carrier b χout χsource β hF hb r hA
  refine ⟨hs.1.1, ?_, subset_closure ⟨ρ, hρ, hs.2⟩⟩
  apply comparableGraphCarrier_subset hρ hpair
  exact (mem_normalizedGraphCarrier_iff (zero_lt_one.trans_le hρ).ne' low j ξ).mpr
    (tsupport_graphBranchCutoff_subset low j (subset_tsupport _ hg))

/-- The constructed phase carrier and the full input annulus give the exact
closed joint-amplitude carrier consumed by the comparable estimate. The
input hypothesis is produced by `exists_elapsed_localizer_annular_carrier`
from the buffered localizer, including all its shoulders
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tsupport_elapsed_jointAmplitude_subset_comparableCarrier
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0)
    {c C a b₀ ρ : ℝ} (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (hpair : IsComparablePair c C a b₀ ρ low j k)
    (mi mo : LocalizerSymbol (d + 1)) {Ki : Set (Euclidean (d + 1))}
    (hi : tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a b₀) (r : ℝ)
    (x y : Euclidean (d + 1)) :
    tsupport (FiniteChain.Graph.jointAmplitude ρ (elapsedAmplitude b χout χsource β r)
      mi mo (graphBranchCutoff low j) (outputCutoff k) x y) ⊆
      Comparable.comparableJointCarrier c C a b₀ (elapsedComparableCarrier χout β F c C a b₀)
        (tsupport χout ×ˢ tsupport χsource) (frequencyAnnulus a b₀) := by
  apply Comparable.tsupport_jointAmplitude_subset_comparableJointCarrier hρ hpair
    (elapsedAmplitude b χout χsource β r) mi mo x y
    (isCompact_elapsedComparableCarrier hout β F c C a b₀) (hout.prod hsource)
    (isCompact_frequencyAnnulus a b₀)
    (elapsedAmplitude_eq_zero_off_physical_carrier b χout χsource β r)
  · apply closure_minimal _ (isCompact_frequencyAnnulus a b₀).isClosed
    intro η hη
    exact (hi (subset_tsupport mi hη)).2
  · exact elapsedAmplitude_mem_comparableCarrier b χout χsource β hF hb hρ hpair r

/-- Closed support of each physical amplitude slice supplies `hphysical` of
the primitive graph theorem. This holds for every positive scale and both
graph branches, independently of comparability
(`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_elapsedAmplitude_slice_subset_physicalPhaseCarrier
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0)
    {ρ : ℝ} (hρ : ρ ≠ 0) (r : ℝ) (low : Bool) (j : ℕ)
    (ξ : Euclidean (d + 1)) (hξ : ξ ∈ normalizedGraphCarrier ρ low j)
    (z : Euclidean (d + 1) × Euclidean (d + 1))
    (hz : z ∈ tsupport (fun z : Euclidean (d + 1) × Euclidean (d + 1) =>
      elapsedAmplitude b χout χsource β r z.1 z.2 (ρ • ξ))) :
    (z.1, ρ • ξ) ∈ elapsedPhysicalPhaseCarrier χout β F low j := by
  have hs : tsupport (fun z : Euclidean (d + 1) × Euclidean (d + 1) =>
      elapsedAmplitude b χout χsource β r z.1 z.2 (ρ • ξ)) ⊆
      {z | (z.1, z.2) ∈ tsupport χout ×ˢ tsupport χsource ∧
        ρ • ξ ∈ elapsedFrequencyCarrier β F} := by
    apply closure_minimal
    · intro p hp
      exact elapsedAmplitude_mem_carrier b χout χsource β hF hb r hp
    · exact ((isClosed_tsupport _).prod (isClosed_tsupport _)).inter
        ((isClosed_elapsedFrequencyCarrier β hF).preimage continuous_const)
  exact ⟨(hs hz).1.1, (mem_normalizedGraphCarrier_iff hρ low j ξ).mp hξ, (hs hz).2⟩

/-- The multiplier cone persists under normalization and closure. In
particular a nonzero comparable spacetime frequency has nonzero spatial
part for this reason, not merely because the spacetime frequency is nonzero
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedNormalizedFrequencyCarrier_subset_cone
    (β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d)) (B : ℝ)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ B * ‖spatialPart ξ‖) :
    elapsedNormalizedFrequencyCarrier β F ⊆ {ξ | |ξ 0| ≤ B * ‖spatialPart ξ‖} := by
  apply closure_minimal
  · rintro ξ ⟨ρ, hρ, hξ⟩
    have hρ0 := zero_lt_one.trans_le hρ
    have h := hcone (ρ • ξ) hξ.1
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, spatialPart_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos hρ0] at h
    rw [← mul_assoc, mul_comm B ρ, mul_assoc] at h
    exact (mul_le_mul_iff_right₀ hρ0).mp h
  · exact isClosed_le ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.abs)
      (continuous_const.mul spatialPartCLM.continuous.norm)

/-- Uniform positive spatial radius on the comparable carrier follows from
the actual multiplier cone (`app:ch_regular:eq:chain-tail`). -/
theorem elapsedComparableCarrier_spatial_lower_bound
    (χout β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d))
    {B : ℝ} (hB : 0 ≤ B)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ B * ‖spatialPart ξ‖)
    {c C a b : ℝ} {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p ∈ elapsedComparableCarrier χout β F c C a b) :
    (a / (16 * annulusFactor c C)) / (B + 1) ≤ ‖spatialPart p.2‖ := by
  apply (div_le_iff₀ (by linarith : 0 < B + 1)).mpr
  simpa only [mul_comm] using hp.2.1.1.trans (norm_le_spatial_of_cone
    (elapsedNormalizedFrequencyCarrier_subset_cone β F B hcone hp.2.2))

/-- Nonzero spatial frequency on the actual comparable carrier follows from
the positive input annulus and the multiplier cone. No inference from
nonzero spacetime frequency alone is used
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedComparableCarrier_spatialPart_ne_zero
    (χout β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d))
    {B : ℝ} (hB : 0 ≤ B)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ B * ‖spatialPart ξ‖)
    {c C a b : ℝ} (ha : 0 < a)
    {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p ∈ elapsedComparableCarrier χout β F c C a b) : spatialPart p.2 ≠ 0 := by
  have hfactor : 0 < annulusFactor c C :=
    lt_of_lt_of_le (by norm_num) (two_le_annulusFactor c C)
  apply norm_pos_iff.mp
  apply lt_of_lt_of_le _ (elapsedComparableCarrier_spatial_lower_bound χout β F hB hcone hp)
  exact div_pos (div_pos ha (mul_pos (by norm_num) hfactor)) (by linarith)

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
