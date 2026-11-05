module

public import JanetCartan.Analysis.Iteration.BandHistory.Conditional
public import JanetCartan.Analysis.Iteration.BandHistory.Norms
public import JanetCartan.Analysis.Fourier.Periodic.Bernstein
public import JanetCartan.Analysis.Fourier.Periodic.BernsteinL2

/-!
# Band-limited histories

The estimates of `main:lem:history`, with both Bernstein inputs discharged.
The baseline seminorms have a summable geometric majorant whose total tends to
zero. At every derivative order the actual finite history has the sharp
fixed-baseline profile, uniformly in its length and the initial scale.

`exists_periodic_history_profile` is uniform over initial maps with a given
seminorm bound. `exists_compact_family_periodic_history_profile` obtains that
bound from a compact smooth family. The physical domain may be any subset of
the compact set on which the initial maps are smooth. Codomains are
finite-dimensional real inner product spaces, including the chosen Euclidean and
Frobenius matrix spaces. The conditional reductions remain available separately.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped ContDiff

namespace JanetCartan

/-- The dimension and order constant in `main:eq:history-bernstein`. -/
def historyL2Constant (n r : ℕ) : ℝ := (r + 1 : ℝ) * Real.sqrt (2 * 5 ^ n)

/-- `main:eq:history-bernstein`: the explicit Bernstein constant is nonnegative. -/
theorem historyL2Constant_nonneg (n r : ℕ) : 0 ≤ historyL2Constant n r := by
  unfold historyL2Constant
  positivity

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- `main:eq:history-bernstein`: Fourier support and L² decay imply baseline
seminorm decay, with a constant independent of the stage and initial scale. -/
theorem periodic_history_increment_bound
    (r₀ : ℕ) {L R v b B k₀ : ℝ} {k : ℕ → ℝ} {u : ℕ → Torus n → F}
    (hR : 2 ≤ R) (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1))
    (hk : ∀ i, k₀ ≤ k i) (i : ℕ) :
    cNorm (fundamentalCell n) r₀ (periodicLift (u i)) ≤
      (historyL2Constant n r₀ * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)) *
        historyScale R v i ^ (-(k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)) :=
  periodic_history_increment_bound_of_bernstein r₀ hR hv hb hL
    (historyL2Constant_nonneg n r₀)
    (fun _ hM _ hf hs ↦ cNorm_periodicLift_le_of_hasFourierSupport hf hM hs r₀)
    hsmooth hsupport hL2 hk i

/-- `main:lem:history`: summability and the manuscript's explicit total bound,
from the actual Fourier support and L² hypotheses, with no analytic premises. -/
theorem periodic_history_summable
    (r₀ : ℕ) {L R v b B k₀ : ℝ} {k : ℕ → ℝ} {u : ℕ → Torus n → F}
    (hR : 2 ≤ R) (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)
    (hsmooth : ∀ i, IsSmoothPeriodic (u i))
    (hsupport : ∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i))
    (hL2 : ∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1))
    (hk : ∀ i, k₀ ≤ k i) :
    Summable (fun i ↦ cNorm (fundamentalCell n) r₀ (periodicLift (u i))) ∧
      (∑' i, cNorm (fundamentalCell n) r₀ (periodicLift (u i))) ≤
        historyBound (historyL2Constant n r₀ * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)) R v
          (k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) :=
  periodic_history_summable_of_bernstein r₀ hR hv hb hL
    (historyL2Constant_nonneg n r₀) hμ
    (fun _ hM _ hf hs ↦ cNorm_periodicLift_le_of_hasFourierSupport hf hM hs r₀)
    hsmooth hsupport hL2 hk

/-- `main:eq:total-small`: the total baseline displacement tends to zero as
`R₀ → ∞`, for any family of increments with the same history-data constants. -/
theorem tendsto_periodic_history_total
    (r₀ : ℕ) {L v b B k₀ : ℝ} {k : ℝ → ℕ → ℝ}
    {u : ℝ → ℕ → Torus n → F}
    (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1)
    (hsmooth : ∀ R, 2 ≤ R → ∀ i, IsSmoothPeriodic (u R i))
    (hsupport : ∀ R, 2 ≤ R → ∀ i,
      HasFourierSupport (L * historyScale R v i ^ b) (u R i))
    (hL2 : ∀ R, 2 ≤ R → ∀ i,
      periodicL2Norm (u R i) ≤ historyScale R v i ^ (-k R i + B + 1))
    (hk : ∀ R, 2 ≤ R → ∀ i, k₀ ≤ k R i) :
    Tendsto (fun R ↦ ∑' i, cNorm (fundamentalCell n) r₀ (periodicLift (u R i)))
      atTop (𝓝 0) :=
  tendsto_periodic_history_total_of_bernstein r₀ hv hb hL
    (historyL2Constant_nonneg n r₀) hμ
    (fun _ hM _ hf hs ↦ cNorm_periodicLift_le_of_hasFourierSupport hf hM hs r₀)
    hsmooth hsupport hL2 hk

/-- `main:eq:total-small`: one threshold makes the total displacement small for
all admissible histories simultaneously. In particular it is uniform over any
family of initial maps, since the threshold does not involve an initial map. -/
theorem exists_uniform_periodic_history_total_small
    (r₀ : ℕ) {L v b B k₀ ε : ℝ}
    (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L) (hε : 0 < ε)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R ≥ Rmin,
      ∀ (u : ℕ → Torus n → F) (k : ℕ → ℝ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1)) →
      (∀ i, k₀ ≤ k i) →
      (∑' i, cNorm (fundamentalCell n) r₀ (periodicLift (u i))) < ε := by
  obtain ⟨S, hS⟩ := eventually_atTop.1
    ((tendsto_historyBound
      (historyL2Constant n r₀ * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)) hv hμ).eventually
        (gt_mem_nhds hε))
  refine ⟨max 2 S, le_max_left _ _, ?_⟩
  intro R hR u k hsmooth hsupport hL2 hk
  exact (periodic_history_summable r₀ ((le_max_left _ _).trans hR) hv hb hL hμ
    hsmooth hsupport hL2 hk).2.trans_lt (hS R ((le_max_right _ _).trans hR))

/-- `main:eq:history-current`: a constant uniform in the initial scale, finite
history, and initial map (subject to its seminorm bound). The actual map is
estimated on every subset of the compact domain; natural subtraction gives the
positive-part exponent at all orders, including orders below the baseline. -/
theorem exists_periodic_history_profile
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (r₀ r : ℕ) {A L v b B k₀ : ℝ}
    (hA : 0 ≤ A) (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 2 ≤ R →
      ∀ (u : ℕ → Torus n → F) (k : ℕ → ℝ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1)) →
      (∀ i, k₀ ≤ k i) → ∀ f₀ : EuclideanSpace ℝ (Fin n) → F,
      (∀ x ∈ K, ContDiffAt ℝ r f₀ x) → cNorm K r f₀ ≤ A →
      ∀ W ⊆ K, ∀ j : ℕ,
        cNorm W r (currentHistoryMap f₀ (fun i ↦ periodicLift (u i)) j) ≤
          C * (historyScale R v j ^ (b / v)) ^ (r - r₀) := by
  obtain ⟨D, hD, hsharp⟩ := exists_periodic_cNorm_bernstein_bound_all_orders n r₀ r
  let C₀ := historyL2Constant n r₀ * L ^ ((r₀ : ℝ) + (n : ℝ) / 2)
  let μ := k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1
  have hC₀ : 0 ≤ C₀ := mul_nonneg (historyL2Constant_nonneg n r₀)
    (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hbound : 0 ≤ historyBound C₀ 2 v μ := by
    apply div_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (by norm_num) _))
    exact sub_nonneg.mpr (history_ratio_lt_one (by norm_num) hv hμ).le
  refine ⟨A + (D * L ^ (r - r₀)) * historyBound C₀ 2 v μ,
    add_nonneg hA (mul_nonneg (mul_nonneg hD (pow_nonneg (zero_le_one.trans hL) _))
      hbound), ?_⟩
  intro R hR u k hsmooth hsupport hL2 hk f₀ hf₀ hinit W hWK j
  have hT := one_le_pow₀
    (one_le_historyScale_profile (by linarith : 1 ≤ R) (by linarith : 0 ≤ v) hb j)
    (n := r - r₀)
  calc
    _ ≤ cNorm K r (currentHistoryMap f₀ (fun i ↦ periodicLift (u i)) j) :=
      cNorm_mono_set_of_contDiffAt hWK hK (fun x hx ↦ (hf₀ x hx).add
        (ContDiffAt.sum (fun i _ ↦ ((hsmooth i).2.of_le (by simp)).contDiffAt)))
    _ ≤ cNorm K r f₀ + ∑ i ∈ Finset.range j,
        cNorm (fundamentalCell n) r (periodicLift (u i)) :=
      BandHistory.cNorm_currentHistoryMap_le hK r hf₀ hsmooth j
    _ ≤ A * (historyScale R v j ^ (b / v)) ^ (r - r₀) +
        ((D * L ^ (r - r₀)) * historyBound C₀ 2 v μ) *
          (historyScale R v j ^ (b / v)) ^ (r - r₀) := by
      apply add_le_add (hinit.trans (le_mul_of_one_le_right hA hT))
      exact sum_periodic_history_high_norm_le_of_bernstein r₀ r hR hv hb hL
        (historyL2Constant_nonneg n r₀) hD hμ
        (fun _ hM _ hf hs ↦ cNorm_periodicLift_le_of_hasFourierSupport hf hM hs r₀)
        (fun _ hM _ hf hs ↦ hsharp hM hf hs) hsmooth hsupport hL2 hk j
    _ = _ := by ring

/-- `main:lem:history`: the map profile is uniform over a compact smooth family
of initial maps. Jointly continuous derivatives give the required initial bounds
by compactness; no history profile is assumed. The same theorem applies at each
natural derivative order, without changing the baseline or smallness threshold. -/
theorem exists_compact_family_periodic_history_profile
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsCompact S)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {f₀ : P → EuclideanSpace ℝ (Fin n) → F}
    (r₀ r : ℕ) {L v b B k₀ : ℝ}
    (hf₀ : ∀ p ∈ S, ∀ x ∈ K, ContDiffAt ℝ r (f₀ p) x)
    (hderiv : ∀ d ≤ r, ContinuousOn (fun px : P × EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ d (f₀ px.1) px.2) (S ×ˢ K))
    (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 2 ≤ R → ∀ p ∈ S,
      ∀ (u : ℕ → Torus n → F) (k : ℕ → ℝ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1)) →
      (∀ i, k₀ ≤ k i) → ∀ W ⊆ K, ∀ j : ℕ,
        cNorm W r (currentHistoryMap (f₀ p) (fun i ↦ periodicLift (u i)) j) ≤
          C * (historyScale R v j ^ (b / v)) ^ (r - r₀) := by
  obtain ⟨A, hA, hinit⟩ := BandHistory.exists_cNorm_bound_on_compact_family hS hK r hderiv
  obtain ⟨C, hC, hprofile⟩ := exists_periodic_history_profile (F := F) hK r₀ r
    hA hv hb hL hμ
  refine ⟨C, hC, ?_⟩
  intro R hR p hp u k hsmooth hsupport hL2 hk W hWK j
  exact hprofile R hR u k hsmooth hsupport hL2 hk (f₀ p) (hf₀ p hp)
    (hinit p hp) W hWK j

/-- `main:eq:history-current`: the all-orders derivative profile of a fixed
smooth initial map, using the shared profile and history-map definitions.
All constants precede the scale and history; the baseline stays fixed. -/
theorem exists_periodic_history_derivative_profile
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {f₀ : EuclideanSpace ℝ (Fin n) → F}
    (hf₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ f₀ x)
    (r₀ : ℕ) {L v b B k₀ : ℝ}
    (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧ ∀ R, 2 ≤ R →
      ∀ (u : ℕ → Torus n → F) (k : ℕ → ℝ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1)) →
      (∀ i, k₀ ≤ k i) → ∀ W ⊆ K, ∀ j : ℕ,
        HasDerivativeProfile W (currentHistoryMap f₀ (fun i ↦ periodicLift (u i)) j)
          r₀ (historyScale R v j ^ (b / v)) C := by
  choose C hC hprofile using fun r ↦ exists_periodic_history_profile (F := F) hK r₀ r
    (cNorm_nonneg K r f₀) hv hb hL hμ
  refine ⟨C, hC, ?_⟩
  intro R hR u k hsmooth hsupport hL2 hk W hWK j r
  exact hprofile r R hR u k hsmooth hsupport hL2 hk f₀
    (fun x hx ↦ (hf₀ x hx).of_le (by simp)) le_rfl W hWK j

/-- `main:lem:history`: one sequence of profile constants works for every
member of a compact smooth family and every admissible history, at every order.
Together with `exists_uniform_periodic_history_total_small` this gives both
uniform assertions of the lemma without additional analytic estimates. -/
theorem exists_compact_family_periodic_history_derivative_profile
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsCompact S)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {f₀ : P → EuclideanSpace ℝ (Fin n) → F}
    (hf₀ : ∀ p ∈ S, ∀ x ∈ K, ContDiffAt ℝ ∞ (f₀ p) x)
    (hderiv : ∀ d, ContinuousOn (fun px : P × EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ d (f₀ px.1) px.2) (S ×ˢ K))
    (r₀ : ℕ) {L v b B k₀ : ℝ}
    (hv : 1 < v) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hμ : 0 < k₀ - (B + b * ((r₀ : ℝ) + (n : ℝ) / 2)) - 1) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧ ∀ R, 2 ≤ R → ∀ p ∈ S,
      ∀ (u : ℕ → Torus n → F) (k : ℕ → ℝ),
      (∀ i, IsSmoothPeriodic (u i)) →
      (∀ i, HasFourierSupport (L * historyScale R v i ^ b) (u i)) →
      (∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1)) →
      (∀ i, k₀ ≤ k i) → ∀ W ⊆ K, ∀ j : ℕ,
        HasDerivativeProfile W
          (currentHistoryMap (f₀ p) (fun i ↦ periodicLift (u i)) j)
          r₀ (historyScale R v j ^ (b / v)) C := by
  choose C hC hprofile using fun r ↦ exists_compact_family_periodic_history_profile
    hS hK r₀ r (fun p hp x hx ↦ (hf₀ p hp x hx).of_le (by simp))
    (fun d _ ↦ hderiv d) hv hb hL hμ
  refine ⟨C, hC, ?_⟩
  intro R hR p hp u k hsmooth hsupport hL2 hk W hWK j r
  exact hprofile r R hR p hp u k hsmooth hsupport hL2 hk W hWK j

end JanetCartan
