module

public import JanetCartan.Analysis.Sobolev.Local.Scale.Graded

/-!
# Normed restriction Sobolev spaces

A type copy carries the infimum restriction norm, while the underlying
submodule retains its ambient L² norm. This separates the two norm instances
in `app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The restriction Sobolev space with its own norm (`app:not:fourier`). -/
def RestrictionSobolevSpace (U : Set (EuclideanSpace ℝ (Fin n))) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : ℕ) : Type _ :=
  restrictionSobolevLevel U F s

namespace RestrictionSobolevSpace

instance (s : ℕ) : AddCommGroup (RestrictionSobolevSpace U F s) :=
  inferInstanceAs (AddCommGroup (restrictionSobolevLevel U F s))

instance (s : ℕ) : Module ℝ (RestrictionSobolevSpace U F s) :=
  inferInstanceAs (Module ℝ (restrictionSobolevLevel U F s))

/-- Forget the normed-space type copy (`app:not:fourier`). -/
def toLevel (s : ℕ) : RestrictionSobolevSpace U F s ≃ₗ[ℝ] restrictionSobolevLevel U F s :=
  LinearEquiv.refl ℝ _

/-- The restriction seminorm on the type copy (`app:not:fourier`). -/
def seminorm (s : ℕ) : Seminorm ℝ (RestrictionSobolevSpace U F s) :=
  (restrictionSobolevSeminorm U s).comp (toLevel s).toLinearMap

/-- The restriction seminorm is definite because it dominates L²
(`app:not:fourier`). -/
theorem seminorm_eq_zero_iff (s : ℕ) (u : RestrictionSobolevSpace U F s) :
    seminorm s u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hn := norm_le_restrictionSobolevNorm (toLevel s u).property
    change restrictionSobolevNorm U s (toLevel s u).val = 0 at h
    rw [h] at hn
    apply (toLevel s).injective
    apply Subtype.ext
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · rintro rfl
    exact map_zero _

instance (s : ℕ) : NormedAddCommGroup (RestrictionSobolevSpace U F s) :=
  AddGroupNorm.toNormedAddCommGroup
    { (seminorm s).toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun u ↦ (seminorm_eq_zero_iff s u).mp }

instance (s : ℕ) : NormedSpace ℝ (RestrictionSobolevSpace U F s) where
  norm_smul_le c u := le_of_eq ((seminorm s).smul' c u)

/-- The norm on the type copy is the infimum over weak extensions
(`app:not:fourier`). -/
theorem norm_eq (s : ℕ) (u : RestrictionSobolevSpace U F s) :
    ‖u‖ = restrictionSobolevNorm U s (toLevel s u).val := rfl

/-- The bounded linear inclusion into actual local L²
(`app:ch_regular:thm:exact-correction`). -/
def toL2 (s : ℕ) : RestrictionSobolevSpace U F s →L[ℝ] LocalL2 U F :=
  ((restrictionSobolevLevel U F s).subtype.comp (toLevel s).toLinearMap).mkContinuous 1
    (by
      intro u
      rw [one_mul, norm_eq]
      exact norm_le_restrictionSobolevNorm (toLevel s u).property)

/-- The inclusion evaluates to the underlying L² class (`app:not:fourier`). -/
@[simp] theorem toL2_apply (s : ℕ) (u : RestrictionSobolevSpace U F s) :
    toL2 s u = (toLevel s u).val := rfl

/-- The L² inclusion is injective (`app:not:fourier`). -/
theorem toL2_injective (s : ℕ) : Function.Injective (toL2 (U := U) (F := F) s) :=
  Subtype.val_injective

/-- The inclusion takes values in precisely the required Sobolev level
(`app:not:fourier`). -/
theorem toL2_mem (s : ℕ) (u : RestrictionSobolevSpace U F s) :
    MemRestrictionSobolev U s (toL2 s u) := (toLevel s u).property

/-- The L² norm is bounded by the Sobolev norm (`app:not:fourier`). -/
theorem norm_toL2_le (s : ℕ) (u : RestrictionSobolevSpace U F s) :
    ‖toL2 s u‖ ≤ ‖u‖ := norm_le_restrictionSobolevNorm (toLevel s u).property

/-- The inclusion has operator norm at most one (`app:not:fourier`). -/
theorem toL2_norm_le (s : ℕ) : ‖toL2 (U := U) (F := F) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using norm_toL2_le (U := U) (F := F) s)

/-- A local L² element with a genuine extension gives a Sobolev element
(`app:not:fourier`). -/
def ofL2 (s : ℕ) (u : LocalL2 U F) (hu : MemRestrictionSobolev U s u) :
    RestrictionSobolevSpace U F s := (toLevel s).symm ⟨u, hu⟩

/-- Inclusion recovers the chosen L² element (`app:not:fourier`). -/
@[simp] theorem toL2_ofL2 (s : ℕ) (u : LocalL2 U F) (hu : MemRestrictionSobolev U s u) :
    toL2 s (ofL2 s u hu) = u := rfl

/-- Reconstruction from the underlying L² class (`app:not:fourier`). -/
@[simp] theorem ofL2_toL2 (s : ℕ) (u : RestrictionSobolevSpace U F s) :
    ofL2 s (toL2 s u) (toL2_mem s u) = u := rfl

/-- Every higher restriction Sobolev space includes continuously into each
lower one (`app:ch_regular:thm:exact-correction`). -/
def inclusion {s t : ℕ} (h : s ≤ t) :
    RestrictionSobolevSpace U F t →L[ℝ] RestrictionSobolevSpace U F s :=
  ((toLevel s).symm.toLinearMap.comp
    ((Submodule.inclusion (antitone_restrictionSobolevLevel h)).comp
      (toLevel t).toLinearMap)).mkContinuous 1 (by
        intro u
        rw [one_mul]
        exact restrictionSobolevNorm_mono (toLevel t u).property h)

/-- The zeroth restriction Sobolev space is isometric to actual local L²
(`app:not:fourier`). -/
def zeroEquivL2 (hU : MeasurableSet U) : RestrictionSobolevSpace U F 0 ≃ₗᵢ[ℝ] LocalL2 U F where
  toFun := toL2 0
  invFun := fun u ↦ ofL2 0 u (memRestrictionSobolev_zero hU u)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := (toL2 0).map_add
  map_smul' := (toL2 0).map_smul
  norm_map' u := (restrictionSobolevNorm_zero hU (toL2 0 u)).symm

end RestrictionSobolevSpace
end JanetCartan.LocalSobolev
