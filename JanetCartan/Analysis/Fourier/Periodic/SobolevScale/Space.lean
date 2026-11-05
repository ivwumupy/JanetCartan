module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Scale
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Normed Sobolev spaces on the unit torus

The type synonym here equips each Fourier Sobolev level with its Sobolev norm,
as distinct from the ambient L² subspace norm. These are the spaces used in
`app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The L² norm is dominated by the weighted analysis norm
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_le_periodicSobolevAnalysis (s : ℕ) (u : periodicSobolevLevel n F s) :
    ‖u.val‖ ≤ ‖periodicSobolevAnalysis s u‖ := by
  have h := (periodicSobolevScale n F).norm_le_gradeNorm u.property
  rwa [(periodicSobolevScale n F).gradeNorm_eq u.property] at h

/-- The weighted Fourier map is injective, by Parseval
(`app:not:fourier`). -/
theorem periodicSobolevAnalysis_injective (s : ℕ) :
    Function.Injective (periodicSobolevAnalysis (n := n) (F := F) s) := by
  intro u v h
  have hz : periodicSobolevAnalysis s (u - v) = 0 := by rw [map_sub, h, sub_self]
  have hn := norm_le_periodicSobolevAnalysis s (u - v)
  rw [hz, norm_zero] at hn
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

/-- The actual Sobolev space, equipped below with its Fourier norm
(`app:ch_background:prop:bg-inverse`). -/
def PeriodicSobolevSpace (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (s : ℕ) : Type _ :=
  periodicSobolevLevel n F s

namespace PeriodicSobolevSpace

instance (s : ℕ) : AddCommGroup (PeriodicSobolevSpace n F s) :=
  inferInstanceAs (AddCommGroup (periodicSobolevLevel n F s))

instance (s : ℕ) : Module ℝ (PeriodicSobolevSpace n F s) :=
  inferInstanceAs (Module ℝ (periodicSobolevLevel n F s))

/-- Forget the normed-space type synonym (`app:ch_background:prop:bg-inverse`). -/
def toLevel (s : ℕ) : PeriodicSobolevSpace n F s ≃ₗ[ℝ] periodicSobolevLevel n F s :=
  LinearEquiv.refl ℝ _

/-- Weighted analysis on the Sobolev normed-space type
(`app:not:fourier`). -/
def analysis (s : ℕ) : PeriodicSobolevSpace n F s →ₗ[ℝ] PeriodicFourierL2 n F :=
  (periodicSobolevAnalysis s).comp (toLevel s).toLinearMap

instance (s : ℕ) : NormedAddCommGroup (PeriodicSobolevSpace n F s) :=
  NormedAddCommGroup.induced _ _ (analysis s)
    ((periodicSobolevAnalysis_injective s).comp (toLevel s).injective)

instance (s : ℕ) : NormedSpace ℝ (PeriodicSobolevSpace n F s) :=
  NormedSpace.induced ℝ _ _ (analysis s)

instance (s : ℕ) : InnerProductSpace ℝ (PeriodicSobolevSpace n F s) :=
  InnerProductSpace.induced (analysis s)

/-- Weighted analysis is an isometry for the Sobolev norm
(`app:not:fourier`). -/
def analysisIsometry (s : ℕ) : PeriodicSobolevSpace n F s →ₗᵢ[ℝ] PeriodicFourierL2 n F where
  toLinearMap := analysis s
  norm_map' _ := rfl

/-- Sobolev elements as actual L² elements (`app:ch_background:prop:bg-inverse`). -/
def toL2 (s : ℕ) : PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F :=
  ((periodicSobolevLevel n F s).subtype.comp (toLevel s).toLinearMap).mkContinuous 1
    (by
      intro u
      rw [one_mul]
      exact norm_le_periodicSobolevAnalysis s (toLevel s u))

/-- The L² inclusion evaluates to the underlying subspace element
(`app:ch_background:prop:bg-inverse`). -/
theorem toL2_apply (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    toL2 s u = (toLevel s u).val := rfl

/-- Inclusion into L² is injective (`app:ch_background:prop:bg-inverse`). -/
theorem toL2_injective (s : ℕ) : Function.Injective (toL2 (n := n) (F := F) s) :=
  Subtype.val_injective

/-- Every element of the Sobolev space belongs to the corresponding L² subspace
(`app:ch_background:prop:bg-inverse`). -/
theorem toL2_mem (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    toL2 s u ∈ periodicSobolevLevel n F s :=
  (toLevel s u).property

/-- The Sobolev norm is exactly the Fourier norm, with convergent series
(`app:not:fourier`). -/
theorem norm_eq (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    ‖u‖ = periodicSobolevNorm s (toL2 s u) :=
  periodicSobolevSeminorm_eq s (toLevel s u)

/-- Inclusion into L² has norm at most one
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_toL2_le (s : ℕ) (u : PeriodicSobolevSpace n F s) : ‖toL2 s u‖ ≤ ‖u‖ :=
  norm_le_periodicSobolevAnalysis s (toLevel s u)

/-- Coefficient evaluation commutes with the inclusion into L²
(`app:not:fourier`). -/
theorem analysis_apply (s : ℕ) (u : PeriodicSobolevSpace n F s) (k : Fin n → ℤ) :
    analysis s u k = periodicSobolevWeight s k • periodicL2FourierCoeff k (toL2 s u) := rfl

/-- Regard an L² element with proved Sobolev membership as a Sobolev element
(`app:ch_background:prop:bg-inverse`). -/
def ofL2 (s : ℕ) (u : PeriodicL2 n F) (hu : u ∈ periodicSobolevLevel n F s) :
    PeriodicSobolevSpace n F s := (toLevel s).symm ⟨u, hu⟩

/-- The inclusion recovers the underlying L² element (`app:not:fourier`). -/
@[simp] theorem toL2_ofL2 (s : ℕ) (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F s) : toL2 s (ofL2 s u hu) = u := rfl

/-- Reconstruction from the underlying L² element (`app:not:fourier`). -/
@[simp] theorem ofL2_toL2 (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    ofL2 s (toL2 s u) (toL2_mem s u) = u := rfl

/-- A smooth representative as an element of the actual Sobolev space
(`app:ch_background:prop:bg-inverse`). -/
def ofSmooth (s : ℕ) (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    PeriodicSobolevSpace n F s :=
  let hLp : MeasureTheory.MemLp f 2 MeasureTheory.volume :=
    hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  ofL2 s (hLp.toLp f) (hf.toLp_mem_periodicSobolevLevel s hLp)

/-- The algebraic inclusion between Sobolev levels
(`app:ch_background:prop:bg-inverse`). -/
def inclusionLinear {s t : ℕ} (h : s ≤ t) :
    PeriodicSobolevSpace n F t →ₗ[ℝ] PeriodicSobolevSpace n F s :=
  (toLevel s).symm.toLinearMap.comp
    ((Submodule.inclusion (antitone_periodicSobolevLevel h)).comp (toLevel t).toLinearMap)

/-- A higher Sobolev space includes continuously into each lower level
(`app:ch_background:prop:bg-inverse`). -/
def inclusion {s t : ℕ} (h : s ≤ t) :
    PeriodicSobolevSpace n F t →L[ℝ] PeriodicSobolevSpace n F s :=
  (inclusionLinear h).mkContinuous 1 (by
    intro u
    rw [one_mul]
    exact periodicSobolevSeminorm_mono h (toLevel t u))

/-- The zeroth Sobolev space is linearly isometric to the original real L²
(`app:not:fourier`). -/
def zeroEquivL2 : PeriodicSobolevSpace n F 0 ≃ₗᵢ[ℝ] PeriodicL2 n F where
  toFun := toL2 0
  invFun := fun u ↦ ofL2 0 u (by rw [periodicSobolevLevel_zero]; trivial)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := (toL2 0).map_add
  map_smul' := (toL2 0).map_smul
  norm_map' u := (periodicSobolevSeminorm_zero (toLevel 0 u)).symm

end PeriodicSobolevSpace
end JanetCartan
