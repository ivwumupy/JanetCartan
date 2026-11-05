module

public import JanetCartan.Analysis.Sobolev.Local.Basic
public import JanetCartan.Analysis.Sobolev.Local.Scale.WeakJet

/-!
# Algebra of restriction Sobolev norms

The auxiliary restriction norm of `app:not:fourier` is subadditive and
absolutely homogeneous, by taking infima over genuine weak-jet extensions.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))} {s : ℕ} {u v : LocalL2 U F}

namespace SobolevExtension

/-- The zero extension with its zero weak jet (`app:not:fourier`). -/
def zero (U : Set (EuclideanSpace ℝ (Fin n))) (s : ℕ) :
    SobolevExtension U s (0 : LocalL2 U F) where
  toFun := fun _ ↦ 0
  jet := fun _ _ ↦ 0
  weakJet := Mollification.hasWeakJetOn_zero _ _
  memLp_fun := MemLp.zero'
  memLp_jet := fun j _ ↦ MemLp.zero'
    (ε := (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
  restrict_eq := (Lp.coeFn_zero F 2 (volume.restrict U)).symm

/-- Add actual weak extensions componentwise (`app:not:fourier`). -/
def add (e : SobolevExtension U s u) (f : SobolevExtension U s v) :
    SobolevExtension U s (u + v) where
  toFun := fun x ↦ e.toFun x + f.toFun x
  jet := fun j x ↦ e.jet j x + f.jet j x
  weakJet := e.weakJet.add_univ f.weakJet
  memLp_fun := e.memLp_fun.add f.memLp_fun
  memLp_jet := fun j hj ↦ (e.memLp_jet j hj).add (f.memLp_jet j hj)
  restrict_eq := by
    filter_upwards [e.restrict_eq, f.restrict_eq, Lp.coeFn_add u v] with x he hf ha
    simp only [he, hf, ha, Pi.add_apply]

/-- Scale an actual weak extension and its jet (`app:not:fourier`). -/
def smul (c : ℝ) (e : SobolevExtension U s u) : SobolevExtension U s (c • u) where
  toFun := fun x ↦ c • e.toFun x
  jet := fun j x ↦ c • e.jet j x
  weakJet := e.weakJet.smul c
  memLp_fun := e.memLp_fun.const_smul c
  memLp_jet := fun j hj ↦ (e.memLp_jet j hj).const_smul c
  restrict_eq := by
    filter_upwards [e.restrict_eq, Lp.coeFn_smul c u] with x he hc
    simp only [he, hc, Pi.smul_apply]

/-- The zero weak jet has zero auxiliary norm (`app:not:fourier`). -/
@[simp] theorem jetNorm_zero_extension : (zero U s (F := F)).jetNorm = 0 := by
  change (∑ j ∈ Finset.range (s + 1),
    (eLpNorm (0 : EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) 2 volume).toReal) = 0
  apply Finset.sum_eq_zero
  intro j _
  rw [eLpNorm_zero (ε := (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F), ENNReal.toReal_zero]

/-- Triangle inequality for actual extension norms (`app:not:fourier`). -/
theorem jetNorm_add_le (e : SobolevExtension U s u) (f : SobolevExtension U s v) :
    (e.add f).jetNorm ≤ e.jetNorm + f.jetNorm := by
  unfold jetNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have he := (e.memLp_jet j (by simpa using Finset.mem_range.mp hj)).eLpNorm_ne_top
  have hf := (f.memLp_jet j (by simpa using Finset.mem_range.mp hj)).eLpNorm_ne_top
  change (eLpNorm (fun x ↦ e.jet j x + f.jet j x) 2 volume).toReal ≤ _
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨he, hf⟩)
    (eLpNorm_add_le (by norm_num))).trans_eq (ENNReal.toReal_add he hf)

/-- Absolute homogeneity of actual extension norms (`app:not:fourier`). -/
theorem jetNorm_smul (c : ℝ) (e : SobolevExtension U s u) :
    (e.smul c).jetNorm = |c| * e.jetNorm := by
  unfold jetNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (eLpNorm (c • e.jet j) 2 volume).toReal = _
  rw [eLpNorm_const_smul c (e.jet j) 2 volume]
  simp [ENNReal.toReal_mul, Real.norm_eq_abs]


end SobolevExtension

/-- Zero belongs to every restriction Sobolev level (`app:not:fourier`). -/
theorem memRestrictionSobolev_zero_element : MemRestrictionSobolev U s (0 : LocalL2 U F) :=
  ⟨SobolevExtension.zero U s⟩

/-- Restriction Sobolev membership is closed under addition (`app:not:fourier`). -/
theorem MemRestrictionSobolev.add (hu : MemRestrictionSobolev U s u)
    (hv : MemRestrictionSobolev U s v) : MemRestrictionSobolev U s (u + v) :=
  ⟨hu.some.add hv.some⟩

/-- Restriction Sobolev membership is closed under real scalars (`app:not:fourier`). -/
theorem MemRestrictionSobolev.smul (hu : MemRestrictionSobolev U s u) (c : ℝ) :
    MemRestrictionSobolev U s (c • u) := ⟨hu.some.smul c⟩

/-- The restriction norm of zero vanishes at every order (`app:not:fourier`). -/
@[simp] theorem restrictionSobolevNorm_zero_element :
    restrictionSobolevNorm U s (0 : LocalL2 U F) = 0 := by
  apply le_antisymm _ restrictionSobolevNorm_nonneg
  simpa using restrictionSobolevNorm_le (SobolevExtension.zero U s (F := F))

/-- Extension norms approach the defining infimum (`app:not:fourier`). -/
theorem exists_extension_jetNorm_lt (hu : MemRestrictionSobolev U s u)
    {a : ℝ} (ha : restrictionSobolevNorm U s u < a) :
    ∃ e : SobolevExtension U s u, e.jetNorm < a := by
  obtain ⟨_, ⟨e, rfl⟩, he⟩ := exists_lt_of_csInf_lt
    (show (Set.range (SobolevExtension.jetNorm (U := U) (s := s) (u := u))).Nonempty from
      ⟨hu.some.jetNorm, hu.some, rfl⟩) ha
  exact ⟨e, he⟩

/-- Triangle inequality for the infimum restriction norm (`app:not:fourier`). -/
theorem restrictionSobolevNorm_add_le (hu : MemRestrictionSobolev U s u)
    (hv : MemRestrictionSobolev U s v) :
    restrictionSobolevNorm U s (u + v) ≤
      restrictionSobolevNorm U s u + restrictionSobolevNorm U s v := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he⟩ := exists_extension_jetNorm_lt hu
    (show restrictionSobolevNorm U s u < restrictionSobolevNorm U s u + ε / 2 by linarith)
  obtain ⟨f, hf⟩ := exists_extension_jetNorm_lt hv
    (show restrictionSobolevNorm U s v < restrictionSobolevNorm U s v + ε / 2 by linarith)
  have h := (restrictionSobolevNorm_le (e.add f)).trans (e.jetNorm_add_le f)
  linarith

/-- Scaling extensions gives one direction of absolute homogeneity
(`app:not:fourier`). -/
theorem restrictionSobolevNorm_smul_le (hu : MemRestrictionSobolev U s u) (c : ℝ) :
    restrictionSobolevNorm U s (c • u) ≤ |c| * restrictionSobolevNorm U s u := by
  by_cases hc : c = 0
  · simp [hc]
  have hcpos : 0 < |c| := abs_pos.mpr hc
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he⟩ := exists_extension_jetNorm_lt hu
    (lt_add_of_pos_right _ (div_pos hε hcpos))
  have h := restrictionSobolevNorm_le (e.smul c)
  rw [e.jetNorm_smul] at h
  have he' := mul_lt_mul_of_pos_left he hcpos
  rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hcpos)] at he'
  linarith

/-- Exact absolute homogeneity of the restriction norm (`app:not:fourier`). -/
theorem restrictionSobolevNorm_smul (hu : MemRestrictionSobolev U s u) (c : ℝ) :
    restrictionSobolevNorm U s (c • u) = |c| * restrictionSobolevNorm U s u := by
  apply le_antisymm (restrictionSobolevNorm_smul_le hu c)
  by_cases hc : c = 0
  · simp [hc]
  have h := restrictionSobolevNorm_smul_le (hu.smul c) c⁻¹
  rw [inv_smul_smul₀ hc, abs_inv] at h
  calc
    |c| * restrictionSobolevNorm U s u ≤
        |c| * (|c|⁻¹ * restrictionSobolevNorm U s (c • u)) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg c)
    _ = restrictionSobolevNorm U s (c • u) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]

end JanetCartan.LocalSobolev
