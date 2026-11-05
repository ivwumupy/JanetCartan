module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.QuotientProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# The fixed cutoff estimate for joint quotient coefficients

A single cutoff is chosen before the input and the derivative order. The actual
full/transverse buffer constructions supply its regularity premises.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open FullPhaseCharts.InverseEstimates

-- The actual buffer producers discharge all local regularity premises.
private theorem cutoff_properties {A B : Type}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {χ : A → ℝ} (hχ : ContDiff ℝ ∞ χ) {J : Set A}
    (hχJ : tsupport χ ⊆ J) {f : A → B}
    (hf : ∀ x ∈ J, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x ↦ χ x • f x) ∧ tsupport (fun x ↦ χ x • f x) ⊆ tsupport χ := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x ↦ ?_), ?_⟩
  · by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul (hf x (hχJ hx))
    · apply (contDiffAt_const (c := (0 : B))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  · apply closure_mono
    intro x hx
    by_contra hh
    have hz : χ x = 0 := by simpa only [Function.mem_support, not_not] using hh
    exact hx (by simp [hz])

private theorem cutoff_cNorm_le {A B : Type}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {χ : A → ℝ} (hχ : ContDiff ℝ ∞ χ) {J O : Set A}
    (hJ : IsCompact J) (hO : IsOpen O) (hOJ : O ⊆ J)
    (hc : HasCompactSupport χ) (hχO : tsupport χ ⊆ O) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f : A → B), (∀ x ∈ J, ContDiffAt ℝ ∞ f x) →
      cNorm univ m (fun x ↦ χ x • f x) ≤ C * cNorm J m f := by
  let S := tsupport χ
  let B₀ := (∑ j ∈ Finset.range (m + 1),
    ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] B →L[ℝ] B)‖ *
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * cNorm S m χ
  have hB : 0 ≤ B₀ := mul_nonneg (Finset.sum_nonneg
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))))
    (cNorm_nonneg _ _ _)
  refine ⟨(m + 1 : ℝ) * (1 + B₀), by positivity, ?_⟩
  intro f hf
  have hsm := (cutoff_properties hχ (hχO.trans hOJ) hf).1
  have hsupp := (cutoff_properties hχ (hχO.trans hOJ) hf).2
  have hloc := cNorm_bilinear_le_on
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] B →L[ℝ] B)
    hc hO hχO hχ.contDiffOn
    (fun x hx ↦ (hf x (hOJ hx)).contDiffWithinAt) m
  have hmono : cNorm S m f ≤ cNorm J m f :=
    cNorm_mono_set_of_contDiffAt (hχO.trans hOJ) hJ
      (fun x hx ↦ (hf x hx).of_le (by simp))
  have hb : cNorm S m (fun x ↦ χ x • f x) ≤ B₀ * cNorm J m f :=
    hloc.trans (mul_le_mul_of_nonneg_left hmono hB)
  have hh : cNorm univ m (fun x ↦ χ x • f x) ≤
      (m + 1 : ℝ) * cNorm S m (fun x ↦ χ x • f x) := by
    apply (cNorm_le_sum_of_bounds (f := fun x ↦ χ x • f x)
      (C := fun _ ↦ cNorm S m (fun x ↦ χ x • f x))
      (fun _ _ ↦ cNorm_nonneg S m (fun x ↦ χ x • f x)) ?_).trans_eq
    · simp
    · intro j hj x _
      by_cases hx : x ∈ S
      · exact norm_iteratedFDeriv_le_cNorm hc (hsm.of_le (by simp)) hx hj
      · have hz : iteratedFDeriv ℝ j (fun x ↦ χ x • f x) x = 0 := by
          by_contra hn
          exact hx (hsupp (support_iteratedFDeriv_subset j hn))
        simpa only [hz, norm_zero] using cNorm_nonneg S m (fun x ↦ χ x • f x)
  apply (hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (cNorm_nonneg _ _ _)

/-- Fixed multiplication cutoff for the eight literal quotient coefficients in
`exists_actual_quotient_extensions` (`app:eq:uniform-high-coeff`). Compactness
and ambient regularity supply bounded derivative images at every order. -/
theorem exists_quotient_coefficient_cutoff {A B : Type}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {K O J : Set A} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hJ : IsCompact J) (hOJ : O ⊆ J) :
    ∃ χ : A → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      K ⊆ interior {x | χ x = 1} ∧
      (∀ f : A → B, (∀ x ∈ J, ContDiffAt ℝ ∞ f x) →
        ContDiff ℝ ∞ (fun x ↦ χ x • f x) ∧
        EqOn (fun x ↦ χ x • f x) f K ∧
        tsupport (fun x ↦ χ x • f x) ⊆ tsupport χ) ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
        ∀ m (f : A → B), (∀ x ∈ J, ContDiffAt ℝ ∞ f x) →
          cNorm univ m (fun x ↦ χ x • f x) ≤ C m * cNorm J m f := by
  obtain ⟨χ, hχ, _, hc, hχO, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK hO hKO
  refine ⟨χ, hχ, hc, hχO, hp, ?_, ?_⟩
  · intro f hf
    have hh := cutoff_properties hχ (hχO.trans hOJ) hf
    refine ⟨hh.1, ?_, hh.2⟩
    intro x hx
    have hx' : x ∈ {x | χ x = 1} := interior_subset (hp hx)
    change χ x = 1 at hx'
    simp [hx']
  · choose C hC hb using fun m ↦ cutoff_cNorm_le (B := B) hχ hJ hO hOJ hc hχO m
    exact ⟨C, hC, hb⟩


end JanetCartan.CurrentCoefficientProfiles.JointExtensions
