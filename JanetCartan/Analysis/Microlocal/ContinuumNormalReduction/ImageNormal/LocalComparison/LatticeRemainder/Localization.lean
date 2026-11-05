module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.KernelDefinitions

/-!
# Support and localization of the Bessel lattice remainder

For `app:ch_background:prop:bg-frame`, Step 1, the two real cutoffs give
compact support to the literal remainder and every derivative. This does
not require convergence of its defining series. The regularity and finite
budget results below are explicitly conditional on smoothness of the
unlocalized lattice remainder in the open comparison cube. Their consuming
assembly must obtain that premise by differentiating the heat-integral series.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The open two-position cube on which nonzero translates avoid the
singularity, for `app:ch_background:prop:bg-frame`, Step 1. -/
def imageBesselComparisonDomain (d : ℕ) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | (∀ i, |p.1 i| < 1 / 2) ∧ ∀ i, |p.2 i| < 1 / 2}

/-- The comparison domain is open, as required to differentiate the
nonzero lattice series in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem isOpen_imageBesselComparisonDomain : IsOpen (imageBesselComparisonDomain d) := by
  have h : IsOpen {x : E | ∀ i, |x i| < 1 / 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_lt ((EuclideanSpace.proj i).continuous.abs) continuous_const
  exact (h.preimage continuous_fst).inter (h.preimage continuous_snd)

/-- Real cutoffs supported in a coordinate cube are compactly supported.
This derives the support premise used in `app:ch_background:prop:bg-frame`,
Step 1 directly from the coordinate bounds. -/
theorem hasCompactSupport_of_imageBessel_cube_support {r : ℝ} (χ : E → ℝ)
    (hχ : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r) : HasCompactSupport χ := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin d ↦ -r) (fun _ ↦ r))).image
      (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)))
  intro x hx
  refine ⟨WithLp.ofLp x, ?_, rfl⟩
  exact ⟨fun i ↦ (abs_le.mp (hχ x hx i)).1, fun i ↦ (abs_le.mp (hχ x hx i)).2⟩

/-- The closed support inherits the cube bounds. It thus stays strictly
inside the open comparison domain when `r < 1/2`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBessel_cube_bounds_of_mem_tsupport {r : ℝ} (χ : E → ℝ)
    (hχ : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r) {x : E} (hx : x ∈ tsupport χ) :
    ∀ i, |x i| ≤ r := by
  intro i
  exact closure_minimal (fun y hy ↦ hχ y hy i)
    (isClosed_le ((EuclideanSpace.proj i).continuous.abs) continuous_const) hx

/-- Localization confines the closed support to the product of cutoff
supports, independently of any series convergence assertion
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem tsupport_localizedImageBesselRemainder_subset (χ ψ : E → ℝ) :
    tsupport (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.1 p.2) ⊆
      tsupport χ ×ˢ tsupport ψ := by
  apply closure_minimal _ ((isClosed_tsupport χ).prod (isClosed_tsupport ψ))
  intro p hp
  have hχ : χ p.1 ≠ 0 := by
    intro h
    exact hp (by simp [localizedImageBesselRemainder, h])
  have hψ : ψ p.2 ≠ 0 := by
    intro h
    exact hp (by simp [localizedImageBesselRemainder, h])
  exact ⟨subset_closure hχ, subset_closure hψ⟩

/-- The actual localized remainder has compact support in both positions
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_localizedImageBesselRemainder (χ ψ : E → ℝ)
    (hχ : HasCompactSupport χ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.1 p.2) :=
  (hχ.isCompact.prod hψ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_localizedImageBesselRemainder_subset χ ψ)

/-- Every derivative retains the same compact support, including the
orders needed by the two normal factors in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem tsupport_iteratedFDeriv_localizedImageBesselRemainder_subset
    (χ ψ : E → ℝ) (n : ℕ) :
    tsupport (iteratedFDeriv ℝ n
      (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.1 p.2)) ⊆
      tsupport χ ×ˢ tsupport ψ :=
  (tsupport_iteratedFDeriv_subset n).trans (tsupport_localizedImageBesselRemainder_subset χ ψ)

/-- Smoothness on the open comparison cube implies global smoothness after
localization. The series-smoothness premise is still to be supplied by the
heat estimates; this is its downstream use in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem contDiff_localizedImageBesselRemainder_of_contDiffOn {r : ℝ} (hr : r < 1 / 2)
    (χ ψ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
    (hR : ContDiffOn ℝ ∞ (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
      (imageBesselComparisonDomain d)) :
    ContDiff ℝ ∞ (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport
      (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.1 q.2)
  · have hs := tsupport_localizedImageBesselRemainder_subset χ ψ hp
    have hmem : p ∈ imageBesselComparisonDomain d :=
      ⟨fun i ↦ (imageBessel_cube_bounds_of_mem_tsupport χ hχs hs.1 i).trans_lt hr,
       fun i ↦ (imageBessel_cube_bounds_of_mem_tsupport ψ hψs hs.2 i).trans_lt hr⟩
    exact ((hχ.comp contDiff_fst).contDiffAt.mul
      (hR.contDiffAt (isOpen_imageBesselComparisonDomain.mem_nhds hmem))).mul
      (hψ.comp contDiff_snd).contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hp)

/-- A common bound for every specified finite joint derivative reserve,
conditional only on the unlocalized series-smoothness input. In particular
the consumer can request `N + 2` before applying both normal factors in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_localizedImageBesselRemainder_jet_budget_of_contDiffOn
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
    (hR : ContDiffOn ℝ ∞ (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
      (imageBesselComparisonDomain d)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ p : E × E,
      ‖iteratedFDeriv ℝ n
        (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.1 q.2) p‖ ≤ C := by
  have hd := contDiff_localizedImageBesselRemainder_of_contDiffOn hr χ ψ hχ hψ hχs hψs hR
  have hc := hasCompactSupport_localizedImageBesselRemainder χ ψ
    (hasCompactSupport_of_imageBessel_cube_support χ hχs)
    (hasCompactSupport_of_imageBessel_cube_support ψ hψs)
  have hb (n : ℕ) := (hc.iteratedFDeriv n).exists_bound_of_continuous
    (hd.continuous_iteratedFDeriv (by simp))
  choose C hC using hb
  have hC₀ (n : ℕ) : 0 ≤ C n := (norm_nonneg _).trans (hC n 0)
  refine ⟨∑ j ∈ Finset.range (N + 1), C j,
    Finset.sum_nonneg (fun j _ ↦ hC₀ j), ?_⟩
  intro n hn p
  exact (hC n p).trans (Finset.single_le_sum (fun j _ ↦ hC₀ j)
    (Finset.mem_range.mpr (by omega)))

/-- Compact support of the literal reversed scalar kernel, as used for
the adjoint remainder in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem hasCompactSupport_localizedImageBesselRemainder_reverse (χ ψ : E → ℝ)
    (hχ : HasCompactSupport χ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.2 p.1) := by
  simpa only [localizedImageBesselRemainder_swap] using
    hasCompactSupport_localizedImageBesselRemainder ψ χ hψ hχ

/-- The reversed kernel is smooth under the same unlocalized series
premise (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_localizedImageBesselRemainder_reverse_of_contDiffOn
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
    (hR : ContDiffOn ℝ ∞ (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
      (imageBesselComparisonDomain d)) :
    ContDiff ℝ ∞ (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.2 p.1) := by
  simpa only [localizedImageBesselRemainder_swap] using
    contDiff_localizedImageBesselRemainder_of_contDiffOn hr ψ χ hψ hχ hψs hχs hR

/-- One constant bounds all joint derivatives through `N + 2`, for both
the kernel and its literal reverse. The two extra orders are the reserve
for the first-order normal factors in `app:ch_background:prop:bg-frame`,
Step 1. The series-smoothness premise remains an assembly obligation. -/
theorem exists_localizedImageBesselRemainder_two_factor_budget_of_contDiffOn
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
    (hR : ContDiffOn ℝ ∞ (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
      (imageBesselComparisonDomain d)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N + 2, ∀ p : E × E,
      ‖iteratedFDeriv ℝ n
        (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.1 q.2) p‖ ≤ C ∧
      ‖iteratedFDeriv ℝ n
        (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.2 q.1) p‖ ≤ C := by
  obtain ⟨C₁, hC₁₀, hC₁⟩ := exists_localizedImageBesselRemainder_jet_budget_of_contDiffOn
    hr χ ψ hχ hψ hχs hψs hR (N + 2)
  obtain ⟨C₂, _, hC₂⟩ := exists_localizedImageBesselRemainder_jet_budget_of_contDiffOn
    hr ψ χ hψ hχ hψs hχs hR (N + 2)
  refine ⟨max C₁ C₂, hC₁₀.trans (le_max_left _ _), ?_⟩
  intro n hn p
  refine ⟨(hC₁ n hn p).trans (le_max_left _ _), ?_⟩
  simpa only [localizedImageBesselRemainder_swap] using
    (hC₂ n hn p).trans (le_max_right C₁ C₂)

end JanetCartan.ContinuumNormalReduction.ImageNormal
