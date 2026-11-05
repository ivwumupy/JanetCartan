module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.SourceSum

/-!
# The normalized complete angular source

Average the actual completed angular mask with its reflection. The family,
elliptic cutoff and enlarged radial collar are unchanged. The plateau theorem
accepts any symmetric protected terminal set contained in the original `K`;
the no-return selector remains responsible for that inclusion.
Consumers: the normalized fixed inverse and the signed Fourier source tail.
Sources: `sector-theorem-identity`, `resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks FiniteMasks.ActualFamily EllipticComplement
open FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The corrected real angular symbol from the SAME characteristic and
elliptic source, with external half-normalization (`sector-theorem-identity`). -/
def gammaTotal (η : E) : ℝ :=
  (fullSourceAngularMask f hK η + fullSourceAngularMask f hK (-η)) / 2

/-- Smoothness of the actual normalized mask (`resolved-angular-tail`). -/
theorem contDiff_gammaTotal : ContDiff ℝ ∞ (gammaTotal f hK) :=
  ((fullSourceAngularMask_properties f hK).1.add
    ((fullSourceAngularMask_properties f hK).1.comp contDiff_neg)).div_const 2

/-- Compactness is retained by reflection and averaging of the original
completed angular mask (`resolved-angular-tail`). -/
theorem hasCompactSupport_gammaTotal : HasCompactSupport (gammaTotal f hK) := by
  have hg := hasCompactSupport_fullSourceAngularMask f hK
  have hc : HasCompactSupport (fun η ↦
      (fullSourceAngularMask f hK η + fullSourceAngularMask f hK (-η)) * (2 : ℝ)⁻¹) :=
    (hg.add (hg.comp_homeomorph (Homeomorph.neg E))).mul_right
  change HasCompactSupport (fun η ↦
    (fullSourceAngularMask f hK η + fullSourceAngularMask f hK (-η)) / 2)
  simpa only [div_eq_mul_inv] using hc

/-- The normalized full source is even, without requiring any symmetry of
the individual characteristic masks (`sector-theorem-identity`). -/
theorem gammaTotal_neg (η : E) : gammaTotal f hK (-η) = gammaTotal f hK η := by
  simp only [gammaTotal, neg_neg, add_comm]

/-- The real normalized source takes values in `[0,1]`, including every
angular shoulder (`resolved-angular-tail`). -/
theorem gammaTotal_mem_Icc (η : E) : gammaTotal f hK η ∈ Icc (0 : ℝ) 1 := by
  have hp := (fullSourceAngularMask_properties f hK).2.1 η
  have hn := (fullSourceAngularMask_properties f hK).2.1 (-η)
  dsimp only [gammaTotal, mem_Icc]
  constructor <;> linarith [hp.1, hp.2, hn.1, hn.2]

/-- A symmetric protected TERMINAL set contained in the original compact
has a fixed symmetric open unit plateau for the actual normalized mask.
The terminal inclusion is supplied by the original no-return selection,
never inferred from protection of initial directions (`resolved-angular-tail`). -/
theorem exists_gammaTotal_plateau {T : Set E} (hTK : T ⊆ K)
    (hTneg : ∀ η ∈ T, -η ∈ T) :
    ∃ V : Set E, IsOpen V ∧ T ⊆ V ∧ (∀ η ∈ V, -η ∈ V) ∧
      ∀ η ∈ V, gammaTotal f hK η = 1 := by
  let U := interior {η | fullSourceAngularMask f hK η = 1}
  have hKU : K ⊆ U := (fullSourceAngularMask_properties f hK).2.2
  refine ⟨U ∩ (fun η : E ↦ -η) ⁻¹' U,
    isOpen_interior.inter (isOpen_interior.preimage continuous_neg),
    fun η hη ↦ ⟨hKU (hTK hη), hKU (hTK (hTneg η hη))⟩,
    fun η hη ↦ ⟨hη.2, by simpa only [mem_preimage, neg_neg] using hη.1⟩, ?_⟩
  intro η hη
  have hp : fullSourceAngularMask f hK η = 1 :=
    interior_subset (s := {η | fullSourceAngularMask f hK η = 1}) hη.1
  have hn : fullSourceAngularMask f hK (-η) = 1 :=
    interior_subset (s := {η | fullSourceAngularMask f hK η = 1}) hη.2
  norm_num [gammaTotal, hp, hn]

/-- The normalized scalar physical symbol at the original final `2*L`
collar, before physical masking (`sector-theorem-identity`). -/
def normalizedSourceMask (L : ℝ) : E → ℝ :=
  dilatedConicMask (gammaTotal f hK) (2*L)

/-- The normalized source remains smooth and bounded across the entire
low-frequency collar (`resolved-angular-tail`). -/
theorem normalizedSourceMask_properties (L : ℝ) :
    ContDiff ℝ ∞ (normalizedSourceMask f hK L) ∧
      ∀ ξ, normalizedSourceMask f hK L ξ ∈ Icc (0 : ℝ) 1 :=
  ⟨contDiff_dilatedConicMask (contDiff_gammaTotal f hK) _,
    fun ξ ↦ conicMask_mem_Icc (gammaTotal_mem_Icc f hK) ((2*L)⁻¹ • ξ)⟩

/-- Averaging the full physical symbols is EXACTLY dilation of the averaged
angular symbol, at every frequency, including zero and the low shoulder.
The same radial cutoff is reflected, not replaced (`sector-theorem-identity`). -/
theorem normalizedSourceMask_eq_average (L : ℝ) (ξ : E) :
    normalizedSourceMask f hK L ξ =
      (dilatedConicMask (fullSourceAngularMask f hK) (2*L) ξ +
        dilatedConicMask (fullSourceAngularMask f hK) (2*L) (-ξ)) / 2 := by
  have hcut : physicalCutoff 0 (-((2*L)⁻¹ • ξ)) = physicalCutoff 0 ((2*L)⁻¹ • ξ) := by
    simpa only [physicalCutoff, smul_neg] using profile.neg ((radius 0)⁻¹ • ((2*L)⁻¹ • ξ))
  simp only [normalizedSourceMask, dilatedConicMask, conicMask,
    CompatibleResponse.radialSourceCutoff, gammaTotal, smul_neg, hcut,
    NormedSpace.normalize_neg]
  ring

/-- The normalized source symbol itself is even with the unchanged collar
(`sector-theorem-identity`). -/
theorem normalizedSourceMask_neg (L : ℝ) (ξ : E) :
    normalizedSourceMask f hK L (-ξ) = normalizedSourceMask f hK L ξ := by
  simpa only [normalizedSourceMask, dilatedConicMask, smul_neg] using
    conicMask_neg (gammaTotal_neg f hK) ((2*L)⁻¹ • ξ)

/-- The complete angular/low-frequency defect is `1-D gammaTotal`.
It is kept separate from the gain-one analytic residual (`resolved-angular-tail`). -/
def normalizedComplementMask (L : ℝ) (ξ : E) : ℝ := 1 - normalizedSourceMask f hK L ξ

/-- The exact complementary mask is smooth, even and `[0,1]`-valued on
all frequencies (`resolved-angular-tail`). -/
theorem normalizedComplementMask_properties (L : ℝ) :
    ContDiff ℝ ∞ (normalizedComplementMask f hK L) ∧
      (∀ ξ, normalizedComplementMask f hK L ξ ∈ Icc (0 : ℝ) 1) ∧
      ∀ ξ, normalizedComplementMask f hK L (-ξ) = normalizedComplementMask f hK L ξ := by
  refine ⟨contDiff_const.sub (normalizedSourceMask_properties f hK L).1, ?_, ?_⟩
  · intro ξ
    have h := (normalizedSourceMask_properties f hK L).2 ξ
    change 0 ≤ 1 - normalizedSourceMask f hK L ξ ∧ 1 - normalizedSourceMask f hK L ξ ≤ 1
    constructor <;> linarith [h.1, h.2]
  · intro ξ
    rw [normalizedComplementMask, normalizedComplementMask, normalizedSourceMask_neg]

/-- Exact complementary mask, retaining both reflected low shoulders
(`resolved-angular-tail`). -/
theorem normalizedComplementMask_eq (L : ℝ) (ξ : E) :
    normalizedComplementMask f hK L ξ = 1 -
      (dilatedConicMask (fullSourceAngularMask f hK) (2*L) ξ +
        dilatedConicMask (fullSourceAngularMask f hK) (2*L) (-ξ)) / 2 := by
  rw [normalizedComplementMask, normalizedSourceMask_eq_average]

/-- On the same symmetric terminal neighborhood the only source defect is
the original radial low cutoff. Above `4*L` it vanishes exactly
(`resolved-angular-tail`, `sector-theorem-identity`). -/
theorem exists_normalizedSourceMask_partition_near {T : Set E} (hTK : T ⊆ K)
    (hTneg : ∀ η ∈ T, -η ∈ T) :
    ∃ V : Set E, IsOpen V ∧ T ⊆ V ∧ (∀ η ∈ V, -η ∈ V) ∧
      ∀ L > (0 : ℝ), ∀ ξ : E, NormedSpace.normalize ξ ∈ V →
        normalizedSourceMask f hK L ξ + physicalCutoff 0 ((2*L)⁻¹ • ξ) = 1 ∧
        (4*L ≤ ‖ξ‖ → normalizedSourceMask f hK L ξ = 1) := by
  obtain ⟨V, hV, hTV, hn, hp⟩ := exists_gammaTotal_plateau f hK hTK hTneg
  refine ⟨V, hV, hTV, hn, ?_⟩
  intro L hL ξ hξ
  have ht : 0 < 2*L := by positivity
  have he : normalizedSourceMask f hK L ξ = 1 - physicalCutoff 0 ((2*L)⁻¹ • ξ) := by
    simp only [normalizedSourceMask, dilatedConicMask, conicMask,
      CompatibleResponse.radialSourceCutoff, NormedSpace.normalize_smul_of_pos (inv_pos.mpr ht),
      hp _ hξ, mul_one]
  refine ⟨by rw [he]; ring, fun hhi ↦ ?_⟩
  have hrad : 2 ≤ ‖(2*L)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ ht).mpr (by linarith)
  rw [he, physicalCutoff_eq_zero 0 (by simpa [radius] using hrad), sub_zero]

end JanetCartan.RegularSector.NormalizedSolver
