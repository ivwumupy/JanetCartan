module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.DirectSum

/-!
# Dense tests and the full initial input scale

The complete direct-sum Hilbert spaces give actual nested subspaces of the
published augmented L² input for `app:ch_background:prop:bg-inverse`.
Their norms are exposed to the existing `GradedScale` inverse interface.
Compact smooth physical carrier tests and smooth periodic auxiliary tests
are dense in every level; Euclidean and periodic measures remain distinct.
-/

@[expose] public noncomputable section

namespace JanetCartan.CarrierSobolev
open ContinuumRow

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The full input norm is exactly the Hilbert sum of the two auxiliary norms
and all full raw carrier norms (`app:ch_background:eq:bg-r-inverse`). -/
theorem augmentedInputSobolev_norm_sq (s : ℕ) (u : AugmentedInputSobolevSpace n ι s) :
    ‖u‖ ^ 2 =
      periodicSobolevNorm s (PeriodicSobolevSpace.toL2 s u.fst.fst) ^ 2 +
      (∑ i, rawSobolevNorm s (RawSobolevSpace.toRawL2 s (u.fst.snd i)) ^ 2) +
      periodicSobolevNorm s (PeriodicSobolevSpace.toL2 s u.snd) ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    carrierFamilySobolev_norm_sq, PeriodicSobolevSpace.norm_eq, PeriodicSobolevSpace.norm_eq]

/-- Test data for the image auxiliary component (`app:ch_background:prop:bg-adjoint`). -/
abbrev AuxiliaryInputTest (n : ℕ) := {f : Torus n → Euclidean n // IsSmoothPeriodic f}

/-- Full smooth test input, using compact physical carrier tests and periodic
auxiliary tests (`app:ch_background:prop:bg-adjoint`). -/
abbrev AugmentedInputTest (n : ℕ) (ι : Type*) :=
  (AuxiliaryInputTest n × (ι → carrierInitialTestSpace n)) × AuxiliaryInputTest n

/-- Realization of the finite family of compact physical carrier tests
(`app:ch_background:prop:bg-adjoint`). -/
def carrierTestRealization (s : ℕ) (φ : ι → carrierInitialTestSpace n) :
    CarrierFamilySobolevSpace n ι s :=
  WithLp.toLp 2 (fun i ↦ PhysicalSobolevSpace.compactSmooth s
    (φ i).val (φ i).property.1 (φ i).property.2)

/-- Carrier test families are dense for the full Sobolev norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem denseRange_carrierTestRealization (s : ℕ) :
    DenseRange (carrierTestRealization (n := n) (ι := ι) s) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ RawSobolevSpace n s)).symm.surjective.denseRange.comp
    (DenseRange.piMap fun _ ↦ PhysicalSobolevSpace.denseRange_compactSmooth s)
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ RawSobolevSpace n s)).symm.continuous

/-- Physical row realization of actual smooth tests
(`app:ch_background:prop:bg-adjoint`). -/
def physicalTestRealization (s : ℕ)
    (φ : AuxiliaryInputTest n × (ι → carrierInitialTestSpace n)) : PhysicalInputSobolevSpace n ι s :=
  WithLp.toLp 2 (PeriodicSobolevSpace.ofSmooth s φ.1.val φ.1.property, carrierTestRealization s φ.2)

/-- Physical row tests are dense in the Hilbert sum norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem denseRange_physicalTestRealization (s : ℕ) :
    DenseRange (physicalTestRealization (n := n) (ι := ι) s) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.surjective.denseRange.comp
    ((PeriodicSobolevSpace.denseRange_ofSmooth s).prodMap (denseRange_carrierTestRealization s))
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous

/-- Full realization before physical cutoffs, including the exterior component
(`app:ch_background:prop:bg-adjoint`). -/
def augmentedTestRealization (s : ℕ) (φ : AugmentedInputTest n ι) : AugmentedInputSobolevSpace n ι s :=
  WithLp.toLp 2 (physicalTestRealization s φ.1, PeriodicSobolevSpace.ofSmooth s φ.2.val φ.2.property)

/-- Actual tests are dense in the full initial `X^s` norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem denseRange_augmentedTestRealization (s : ℕ) :
    DenseRange (augmentedTestRealization (n := n) (ι := ι) s) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.surjective.denseRange.comp
    ((denseRange_physicalTestRealization s).prodMap (PeriodicSobolevSpace.denseRange_ofSmooth s))
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous

/-- Carrier tests represent the same datum under every level inclusion
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem carrierFamilyInclusion_test {s t : ℕ} (hst : s ≤ t)
    (φ : ι → carrierInitialTestSpace n) :
    carrierFamilyInclusion hst (carrierTestRealization t φ) = carrierTestRealization s φ := by
  apply PiLp.ext
  intro i
  exact PhysicalSobolevSpace.inclusion_compactSmooth hst
    (φ i).val (φ i).property.1 (φ i).property.2

/-- Physical tests represent the same datum under every level inclusion
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem physicalInputInclusion_test {s t : ℕ} (hst : s ≤ t)
    (φ : AuxiliaryInputTest n × (ι → carrierInitialTestSpace n)) :
    physicalInputInclusion hst (physicalTestRealization t φ) = physicalTestRealization s φ := by
  simp only [physicalInputInclusion_apply, physicalTestRealization]
  apply congrArg (WithLp.toLp 2)
  exact Prod.ext (auxiliaryInclusion_ofSmooth hst φ.1.val φ.1.property)
    (carrierFamilyInclusion_test hst φ.2)

/-- Tests represent the same datum under every level inclusion
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem augmentedInputInclusion_test {s t : ℕ} (hst : s ≤ t) (φ : AugmentedInputTest n ι) :
    augmentedInputInclusion hst (augmentedTestRealization t φ) = augmentedTestRealization s φ := by
  simp only [augmentedInputInclusion_apply, augmentedTestRealization]
  apply congrArg (WithLp.toLp 2)
  exact Prod.ext (physicalInputInclusion_test hst φ.1)
    (auxiliaryInclusion_ofSmooth hst φ.2.val φ.2.property)

/-- Every higher full input level is dense in each lower one
(`app:ch_background:prop:bg-inverse`). -/
theorem denseRange_augmentedInputInclusion {s t : ℕ} (hst : s ≤ t) :
    DenseRange (augmentedInputInclusion (n := n) (ι := ι) hst) := by
  apply (denseRange_augmentedTestRealization (n := n) (ι := ι) s).mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨augmentedTestRealization t φ, augmentedInputInclusion_test hst φ⟩

/-- Every full input level has dense image in the original augmented L² space
(`app:ch_background:prop:bg-inverse`). -/
theorem denseRange_augmentedInputToL2 (s : ℕ) :
    DenseRange (augmentedInputToL2 (n := n) (ι := ι) s) := by
  have h := (augmentedInputZeroEquivL2 (n := n) (ι := ι)).surjective.denseRange.comp
    (denseRange_augmentedInputInclusion (n := n) (ι := ι) (Nat.zero_le s))
    (augmentedInputZeroEquivL2 (n := n) (ι := ι)).continuous
  have he (u : AugmentedInputSobolevSpace n ι s) :
      augmentedInputZeroEquivL2 (augmentedInputInclusion (Nat.zero_le s) u) =
        augmentedInputToL2 s u := by
    rw [augmentedInputZeroEquivL2_apply, augmentedInputToL2_inclusion]
  simpa only [Function.comp_def, he] using h

/-- Actual full initial subspaces of the original augmented L² input
(`app:ch_background:prop:bg-inverse`). The range is of the concrete, faithful
injection, whose component spaces were constructed with their full norms. -/
def augmentedInputLevel (n : ℕ) (ι : Type*) [Fintype ι] (s : ℕ) : Submodule ℝ (AugmentedInput n ι) :=
  (augmentedInputToL2 s).range

/-- Faithful parametrization of an actual subspace by its complete Hilbert level
(`app:ch_background:prop:bg-inverse`). -/
def augmentedInputLevelEquiv (s : ℕ) : AugmentedInputSobolevSpace n ι s ≃ₗ[ℝ] augmentedInputLevel n ι s :=
  LinearEquiv.ofInjective (augmentedInputToL2 s).toLinearMap (augmentedInputToL2_injective s)

/-- Reconstructing from a level subtype retains its raw datum
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem augmentedInputToL2_levelEquiv_symm (s : ℕ) (u : augmentedInputLevel n ι s) :
    augmentedInputToL2 s ((augmentedInputLevelEquiv s).symm u) = u.val :=
  congrArg Subtype.val ((augmentedInputLevelEquiv s).apply_symm_apply u)

/-- Full initial level zero is the entire original input
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem augmentedInputLevel_zero (n : ℕ) (ι : Type*) [Fintype ι] :
    augmentedInputLevel n ι 0 = ⊤ := by
  apply top_unique
  intro u _
  obtain ⟨v, hv⟩ := (augmentedInputZeroEquivL2 (n := n) (ι := ι)).surjective u
  exact ⟨v, hv⟩

/-- All full initial subspaces are nested (`app:ch_background:prop:bg-inverse`). -/
theorem antitone_augmentedInputLevel : Antitone (augmentedInputLevel n ι) := by
  intro s t hst u hu
  obtain ⟨v, rfl⟩ := hu
  exact ⟨augmentedInputInclusion hst v, augmentedInputToL2_inclusion hst v⟩

/-- The Hilbert norm on the actual subspace, consumed by the inverse bootstrap
(`app:ch_background:eq:bg-r-inverse`). -/
def augmentedInputSeminorm (s : ℕ) : Seminorm ℝ (augmentedInputLevel n ι s) :=
  (normSeminorm ℝ (AugmentedInputSobolevSpace n ι s)).comp
    (augmentedInputLevelEquiv s).symm.toLinearMap

/-- Subspace norms have the exact original zeroth normalization
(`app:ch_background:prop:bg-inverse`). -/
theorem augmentedInputSeminorm_zero (u : augmentedInputLevel n ι 0) :
    augmentedInputSeminorm 0 u = ‖u.val‖ := by
  change ‖(augmentedInputLevelEquiv 0).symm u‖ = ‖u.val‖
  rw [← (augmentedInputZeroEquivL2 (n := n) (ι := ι)).norm_map]
  exact congrArg norm (augmentedInputToL2_levelEquiv_symm 0 u)

/-- Full initial norms increase with the order on their actual domains
(`app:ch_background:prop:bg-inverse`). -/
theorem augmentedInputSeminorm_mono {s t : ℕ} (hst : s ≤ t) (u : augmentedInputLevel n ι t) :
    augmentedInputSeminorm s ⟨u.val, antitone_augmentedInputLevel hst u.property⟩ ≤
      augmentedInputSeminorm t u := by
  change ‖(augmentedInputLevelEquiv (n := n) (ι := ι) s).symm
    ⟨u.val, antitone_augmentedInputLevel hst u.property⟩‖ ≤
      ‖(augmentedInputLevelEquiv t).symm u‖
  have he : (augmentedInputLevelEquiv s).symm
        ⟨u.val, antitone_augmentedInputLevel hst u.property⟩ =
      augmentedInputInclusion hst ((augmentedInputLevelEquiv t).symm u) := by
    apply augmentedInputToL2_injective s
    simp only [augmentedInputToL2_levelEquiv_symm, augmentedInputToL2_inclusion]
  rw [he]
  exact norm_augmentedInputInclusion_le hst _

/-- The full initial scale `X^s` on the published real augmented input,
ready for the canonical inverse and initial-adjoint consumers
(`app:ch_background:prop:bg-inverse`, `app:ch_background:prop:bg-adjoint`). -/
def augmentedInputSobolevScale (n : ℕ) (ι : Type*) [Fintype ι] : GradedScale (AugmentedInput n ι) where
  level := augmentedInputLevel n ι
  level_zero := augmentedInputLevel_zero n ι
  antitone_level := antitone_augmentedInputLevel
  seminorm := augmentedInputSeminorm
  seminorm_zero := augmentedInputSeminorm_zero
  monotone_seminorm := augmentedInputSeminorm_mono

/-- The grade norm agrees with the complete Hilbert norm on every included
full initial datum (`app:ch_background:eq:bg-r-inverse`). -/
theorem augmentedInputSobolevScale_gradeNorm (s : ℕ) (u : AugmentedInputSobolevSpace n ι s) :
    (augmentedInputSobolevScale n ι).gradeNorm s (augmentedInputToL2 s u) = ‖u‖ := by
  rw [GradedScale.gradeNorm_eq _ (show augmentedInputToL2 s u ∈ augmentedInputLevel n ι s from ⟨u, rfl⟩)]
  change ‖(augmentedInputLevelEquiv s).symm (augmentedInputLevelEquiv s u)‖ = ‖u‖
  rw [LinearEquiv.symm_apply_apply]

/-- Exact componentwise finite-energy membership for the full initial input
of `app:ch_background:prop:bg-inverse`. Each carrier has all physical `z,y`
Sobolev derivatives; the auxiliary components retain their periodic measure. -/
theorem mem_augmentedInputLevel_iff (s : ℕ) (u : AugmentedInput n ι) :
    u ∈ augmentedInputLevel n ι s ↔
      u.fst.fst ∈ periodicSobolevLevel n (Euclidean n) s ∧
      (∀ i, MemRawSobolev s (u.fst.snd i)) ∧
      u.snd ∈ periodicSobolevLevel n (Euclidean n) s := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨PeriodicSobolevSpace.toL2_mem s v.fst.fst,
      fun i ↦ RawSobolevSpace.toRawL2_mem s (v.fst.snd i),
      PeriodicSobolevSpace.toL2_mem s v.snd⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2
      (PeriodicSobolevSpace.ofL2 s u.fst.fst h₁,
        WithLp.toLp 2 (fun i ↦ RawSobolevSpace.ofRawL2 s (u.fst.snd i) (h₂ i))),
      PeriodicSobolevSpace.ofL2 s u.snd h₃), ?_⟩
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply WithLp.ofLp_injective
      apply Prod.ext
      · exact PeriodicSobolevSpace.toL2_ofL2 s _ h₁
      · apply PiLp.ext
        intro i
        exact RawSobolevSpace.toRawL2_ofRawL2 s _ (h₂ i)
    · exact PeriodicSobolevSpace.toL2_ofL2 s _ h₃

/-- The scale norm is exactly the Hilbert sum of the auxiliary norms and
full raw carrier norms on its domain (`app:ch_background:eq:bg-r-inverse`). -/
theorem augmentedInputSobolevScale_gradeNorm_sq {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) :
    (augmentedInputSobolevScale n ι).gradeNorm s u ^ 2 =
      periodicSobolevNorm s u.fst.fst ^ 2 +
      (∑ i, rawSobolevNorm s (u.fst.snd i) ^ 2) + periodicSobolevNorm s u.snd ^ 2 := by
  obtain ⟨v, rfl⟩ := hu
  exact (congrArg (fun a : ℝ ↦ a ^ 2) (augmentedInputSobolevScale_gradeNorm s v)).trans
    (augmentedInputSobolev_norm_sq s v)

end JanetCartan.CarrierSobolev
