module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ElapsedGeometry

/-!
# One joint smooth extension of the buffered two-time phase

The graph constructors require a globally continuous phase. A single smooth
extension in both times and spatial variables supplies that requirement for
all elapsed times simultaneously. It agrees with the constructed phase on
a neighborhood of the entire closed buffer. The full graph operator is
unchanged for amplitudes supported there, with both physical masks retained.
No homogeneity or estimates outside the original chart are asserted.
Source: `app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic
open FourierIntegral EvolutionIntegral
variable {d m : ℕ}

/-- Construct one smooth extension on the whole two-time space, agreeing as a
germ at every point of the closed phase buffer. Consumer: global continuity
and elapsed-time dependence in the retarded graph realization.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_smooth_twoTimePhase_extension
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {K : Set (TwoTimePoint (Euclidean d))} (hK : IsClosed K) (hKC : K ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target) :
    ∃ F : TwoTimePoint (Euclidean d) → ℝ, ContDiff ℝ ∞ F ∧
      ∀ q ∈ K, F =ᶠ[𝓝 q] twoTimePhase C := by
  obtain ⟨U, hU, hKU, hUC⟩ := normal_exists_closure_subset hK C.open_target hKC
  obtain ⟨V, hV, hUV, hVC⟩ := normal_exists_closure_subset isClosed_closure C.open_target hUC
  obtain ⟨χ, hχ, _, hsχ, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  refine ⟨fun q ↦ χ q * twoTimePhase C q, ?_, ?_⟩
  · apply Localization.contDiff_of_contDiffOn_support_neighborhood C.open_target
    · exact hχ.contDiffOn.mul hs
    · exact tsupport_mul_subset_left.trans (by simpa only [tsupport, hsχ] using hVC)
  · intro q hq
    filter_upwards [hU.mem_nhds (hKU hq)] with p hp
    rw [(hχone p).mp (subset_closure hp), one_mul]

/-- Joint smoothness of the extended phase includes the elapsed-time parameter.
It is a pointwise phase assertion and makes no operator-norm continuity claim.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem contDiff_elapsedPhase_of_joint_phase
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) ↦
      elapsedPhase (fun t s y η ↦ F (t, (s, (y, η)))) p.1 p.2.1 p.2.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) ↦
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1 - p.1) *
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.2 +
      F (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1,
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) p.2.1 - p.1,
          (spatialPartCLM p.2.1, spatialPartCLM p.2.2))))
  fun_prop

/-- The single joint extension agrees with the elapsed phase on a neighborhood
of every point of the buffered slab. Hence every supported phase jet, not
only its value, is preserved. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem elapsedPhase_eventuallyEq_of_twoTime_extension
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {F : TwoTimePoint (Euclidean d) → ℝ} {z : RootState (Euclidean d)} {ε r : ℝ}
    (hε : 0 < ε)
    (he : ∀ q ∈ closedBall (z.1, z) (2 * ε), F =ᶠ[𝓝 q] twoTimePhase C)
    (hr : r ∈ Icc 0 ε) {x ξ : Euclidean (d + 1)}
    (hx : x ∈ elapsedPhysicalBox z ε) (hξ : spatialPart ξ ∈ ball z.2.2 ε) :
    Function.uncurry (elapsedPhase (fun t s y η ↦ F (t, (s, (y, η)))) r) =ᶠ[𝓝 (x, ξ)]
      Function.uncurry (elapsedPhase (curriedTwoTimePhase C) r) := by
  have hq := he _ (elapsedPoint_mem_twoTime_buffer hε hr hx hξ)
  have hc : Continuous (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦
      (p.1 0, (p.1 0 - r, (spatialPart p.1, spatialPart p.2)))) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.comp continuous_fst).prodMk
      ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.comp
        continuous_fst).sub continuous_const).prodMk
        ((spatialPartCLM.continuous.comp continuous_fst).prodMk
          (spatialPartCLM.continuous.comp continuous_snd)))
  filter_upwards [hq.comp_tendsto (hc.tendsto (x, ξ))] with p hp
  change (p.1 0 - r) * p.2 0 + F _ = (p.1 0 - r) * p.2 0 + twoTimePhase C _
  dsimp only [Function.comp_apply] at hp
  rw [hp]

/-- The extended and original elapsed graphs are literally the same for any
amplitude with the prescribed physical and spatial-frequency masks. The
source mask is retained without restrictions or commutations. This identity
alone does not assert a bound for either graph realization.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_eq_of_twoTime_extension
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {F : TwoTimePoint (Euclidean d) → ℝ} {z : RootState (Euclidean d)} {ε r : ℝ}
    (hε : 0 < ε)
    (he : ∀ q ∈ closedBall (z.1, z) (2 * ε), F =ᶠ[𝓝 q] twoTimePhase C)
    (hr : r ∈ Icc 0 ε) (b : TwoTimeAmplitude d m)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχ : ∀ x, x ∉ elapsedPhysicalBox z ε → χout x = 0)
    (hβ : ∀ ξ, spatialPart ξ ∉ ball z.2.2 ε → β ξ = 0) :
    elapsedGraph (fun t s y η ↦ F (t, (s, (y, η)))) b χout χsource β r =
      elapsedGraph (curriedTwoTimePhase C) b χout χsource β r := by
  apply FullLowBounds.fullGraphOperator_phase_congr
  intro x y ξ hA
  have hx : x ∈ elapsedPhysicalBox z ε := by
    by_contra hn
    exact hA (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ (Or.inl (hχ x hn)))
  have hξ : spatialPart ξ ∈ ball z.2.2 ε := by
    by_contra hn
    exact hA (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ
      (Or.inr (Or.inr (hβ ξ hn))))
  exact (elapsedPhase_eventuallyEq_of_twoTime_extension C hε he hr hx hξ).eq_of_nhds

end JanetCartan.RegularSector.Characteristic
