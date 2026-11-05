module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily

/-!
# The elliptic remainder of the selected angular partition

The determinant gap of the selected family is given on the protected compact,
not on the entire sphere. A compact tube in coefficient and angular variables
buffers the closed support of the missing part. This construction uses the
whole original coefficient ball and makes no choice of new characteristic charts.
Source: `app:ch_regular_base:sec:energy-construction`,
`app:ch_regular_base:prop:complete-residual`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open ActualCarriers FiniteMasks FiniteMasks.ActualFamily
open FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

include hK in
/-- A smooth angular remainder, equal to the missing part near the entire
protected compact. Its *closed* support is elliptic uniformly on the original
coefficient ball (`app:ch_regular_base:sec:energy-construction`). -/
theorem exists_ellipticAngularMask :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∀ η, b η ∈ Icc (0 : ℝ) (1 - ∑ p, f.angularMask p η)) ∧
      K ⊆ interior {η | (∑ p, f.angularMask p η) + b η = 1} ∧
      ∀ A ∈ closedBall A₀ f.coefficientRadius, ∀ η ∈ tsupport b,
        f.determinantGap / 2 < |determinant A η| := by
  classical
  let a : E → ℝ := fun η ↦ 1 - ∑ p, f.angularMask p η
  let J := K ∩ tsupport a
  let gap := {p : Coeff × E | f.determinantGap / 2 < |determinant p.1 p.2|}
  have hgap : IsOpen gap := isOpen_lt continuous_const contDiff_determinant.continuous.abs
  have hproduct : closedBall A₀ f.coefficientRadius ×ˢ J ⊆ gap := by
    rintro ⟨A, η⟩ ⟨hA, hη⟩
    have h := (f.stable_pencil_masks (fun _ ↦ A) univ
      (fun _ _ ↦ by simpa only [mem_closedBall, dist_eq_norm] using hA)).1
      x (mem_univ _) η hη
    exact lt_of_lt_of_le (half_lt_self f.determinantGap_pos) h
  have hJ : IsCompact J := hK.inter_right (isClosed_tsupport _)
  obtain ⟨_, V, _, hV, hA, hJV, hprod⟩ := generalized_tube_lemma
    (isCompact_closedBall A₀ f.coefficientRadius) hJ hgap hproduct
  obtain ⟨χ, hχ, hr, hc, hs, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hJ hV hJV
  have ha : ContDiff ℝ ∞ a := contDiff_const.sub (ContDiff.sum fun p _ ↦ f.angularMask_smooth p)
  refine ⟨χ * a, hχ.mul ha, hc.mul_right, ?_, ?_, ?_⟩
  · intro η
    have hnon : 0 ≤ a η := sub_nonneg.mpr (f.angularMask_sum_le_one η)
    exact ⟨mul_nonneg (hr η).1 hnon, mul_le_of_le_one_left hnon (hr η).2⟩
  · intro η hη
    apply mem_interior_iff_mem_nhds.mpr
    by_cases h : η ∈ tsupport a
    · filter_upwards [isOpen_interior.mem_nhds (hp ⟨hη, h⟩)] with ζ hζ
      have he : χ ζ = 1 := interior_subset (s := {ζ | χ ζ = 1}) hζ
      simp only [Pi.mul_apply, he, one_mul, a]
      ring
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h] with ζ hζ
      change a ζ = 0 at hζ
      change (∑ p, f.angularMask p ζ) + χ ζ * a ζ = 1
      rw [hζ, mul_zero, add_zero]
      exact (sub_eq_zero.mp hζ).symm
  · intro A hAb η hη
    exact hprod (show (A, η) ∈ _ ×ˢ V from ⟨hA hAb, hs (tsupport_mul_subset_left hη)⟩)

/-- The fixed elliptic angular mask of this family
(`app:ch_regular_base:sec:energy-construction`). -/
def ellipticAngularMask : E → ℝ := (exists_ellipticAngularMask f hK).choose

/-- The original family, the angular plateau and the uniform determinant gap
for the *same* chosen mask (`app:ch_regular_base:thm:sector`). -/
theorem ellipticAngularMask_spec :
    ContDiff ℝ ∞ (ellipticAngularMask f hK) ∧ HasCompactSupport (ellipticAngularMask f hK) ∧
    (∀ η, ellipticAngularMask f hK η ∈ Icc (0 : ℝ) (1 - ∑ p, f.angularMask p η)) ∧
    K ⊆ interior {η | (∑ p, f.angularMask p η) + ellipticAngularMask f hK η = 1} ∧
    ∀ A ∈ closedBall A₀ f.coefficientRadius, ∀ η ∈ tsupport (ellipticAngularMask f hK),
      f.determinantGap / 2 < |determinant A η| :=
  (exists_ellipticAngularMask f hK).choose_spec

/-- The complementary physical Fourier source at the characteristic solver's
exact threshold `2*L` (`app:ch_regular_base:prop:complete-residual`). -/
def ellipticSourceMask (L : ℝ) : E → ℝ :=
  dilatedConicMask (ellipticAngularMask f hK) (2 * L)

/-- At every frequency the elliptic multiplier stays between zero and one,
and is globally smooth including the collar (`energy-construction`). -/
theorem ellipticSourceMask_properties (L : ℝ) :
    ContDiff ℝ ∞ (ellipticSourceMask f hK L) ∧
      ∀ ξ, ellipticSourceMask f hK L ξ ∈ Icc (0 : ℝ) 1 := by
  have hb := ellipticAngularMask_spec f hK
  refine ⟨contDiff_dilatedConicMask hb.1 _, fun ξ ↦ conicMask_mem_Icc (fun η ↦ ?_) _⟩
  exact ⟨(hb.2.2.1 η).1, (hb.2.2.1 η).2.trans (sub_le_self _ (Finset.sum_nonneg
    fun p _ ↦ (f.angularMask_range p η).1))⟩

/-- The full closed multiplier support stays above `2*L` and in the buffered
elliptic angular support (`app:ch_regular_base:sec:energy-construction`). -/
theorem ellipticSourceMask_support {L : ℝ} (hL : 0 < L) {ξ : E}
    (hξ : ξ ∈ tsupport (ellipticSourceMask f hK L)) :
    2 * L ≤ ‖ξ‖ ∧ NormedSpace.normalize ξ ∈ tsupport (ellipticAngularMask f hK) := by
  have ht : 0 < 2 * L := by positivity
  have h := conicMask_tsupport_subset _ (tsupport_comp_subset_preimage
    (conicMask (ellipticAngularMask f hK)) (continuous_id.const_smul (2*L)⁻¹) hξ)
  change 1 ≤ ‖(2 * L)⁻¹ • ξ‖ ∧
    NormedSpace.normalize ((2*L)⁻¹ • ξ) ∈ tsupport (ellipticAngularMask f hK) at h
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] at h
  exact ⟨(one_le_inv_mul₀ ht).mp h.1, by
    simpa only [NormedSpace.normalize_smul_of_pos (inv_pos.mpr ht)] using h.2⟩

/-- The two source contributions and the original low-frequency term form
an exact partition on a fixed angular neighborhood of `K`. In particular
their high-frequency sum is one there (`app:ch_regular_base:thm:sector`). -/
theorem exists_ellipticSourceMask_partition_near :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      ∀ L > (0 : ℝ), ∀ ξ : E, NormedSpace.normalize ξ ∈ V →
      ((∑ p, dilatedConicMask (f.angularMask p) (2*L) ξ) + ellipticSourceMask f hK L ξ +
        physicalCutoff 0 ((2*L)⁻¹ • ξ) = 1) ∧
      (4 * L ≤ ‖ξ‖ →
        (∑ p, dilatedConicMask (f.angularMask p) (2*L) ξ) + ellipticSourceMask f hK L ξ = 1) := by
  refine ⟨_, isOpen_interior, (ellipticAngularMask_spec f hK).2.2.2.1, ?_⟩
  intro L hL ξ hξ
  have ht : 0 < 2 * L := by positivity
  have he : (∑ p, f.angularMask p (NormedSpace.normalize ξ)) +
      ellipticAngularMask f hK (NormedSpace.normalize ξ) = 1 :=
    interior_subset (s := {η | (∑ p, f.angularMask p η) + ellipticAngularMask f hK η = 1}) hξ
  have hpart := dilatedConicMask_complete_partition f.angularMask (2*L) ξ
  have hsame : ellipticSourceMask f hK L ξ =
      dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ξ := by
    simp only [ellipticSourceMask, dilatedConicMask, conicMask, CompatibleResponse.radialSourceCutoff,
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr ht)]
    congr 1
    linarith
  rw [← hsame] at hpart
  refine ⟨hpart, fun hhi ↦ ?_⟩
  have hrad : 2 ≤ ‖(2*L)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ ht).mpr (by linarith)
  have hz : physicalCutoff 0 ((2*L)⁻¹ • ξ) = 0 :=
    physicalCutoff_eq_zero 0 (by simpa [radius] using hrad)
  simpa only [hz, add_zero] using hpart

end JanetCartan.RegularSector.EllipticComplement
