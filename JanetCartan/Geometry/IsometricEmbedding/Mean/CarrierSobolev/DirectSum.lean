module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.RawSpace
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale

/-!
# The auxiliary and carrier direct sums

Concrete complete real Hilbert levels for the input `X^s` in
`app:ch_background:prop:bg-inverse` and `app:ch_background:prop:bg-adjoint`.
The periodic components use the published normalized torus space; only the
carrier components use the literal Euclidean initial measure. All product
and finite-family norms below are Hilbert sum norms.
-/

@[expose] public noncomputable section

namespace JanetCartan.CarrierSobolev
open ContinuumRow

/-- Finite Hilbert sum of contractions, used by the carrier inclusions in
`app:ch_background:prop:bg-inverse`. -/
def finiteContractionMap {ι : Type*} [Fintype ι]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) :
    PiLp 2 (fun _ : ι ↦ E) →L[ℝ] PiLp 2 (fun _ : ι ↦ F) :=
  ((LinearMap.pi fun i ↦ L.toLinearMap.comp (LinearMap.proj i)).withLpMap 2).mkContinuous 1
    (by
      intro x
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
      simp only [PiLp.norm_sq_eq_of_L2]
      exact Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hL (x i)) 2)

/-- Componentwise action of the carrier sum map
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem finiteContractionMap_apply {ι : Type*} [Fintype ι]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) (x : PiLp 2 (fun _ : ι ↦ E)) (i : ι) :
    finiteContractionMap L hL x i = L (x i) := rfl

/-- Contractivity survives the finite carrier sum
(`app:ch_background:prop:bg-inverse`). -/
theorem finiteContractionMap_norm_le {ι : Type*} [Fintype ι]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) (x : PiLp 2 (fun _ : ι ↦ E)) :
    ‖finiteContractionMap L hL x‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hL (x i)) 2

/-- Hilbert pair of contractions, used for auxiliary/carrier assembly in
`app:ch_background:prop:bg-inverse`. -/
def hilbertPairContractionMap {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : E →L[ℝ] E') (M : F →L[ℝ] F')
    (hL : ∀ x, ‖L x‖ ≤ ‖x‖) (hM : ∀ y, ‖M y‖ ≤ ‖y‖) :
    WithLp 2 (E × F) →L[ℝ] WithLp 2 (E' × F') :=
  ((L.toLinearMap.prodMap M.toLinearMap).withLpMap 2).mkContinuous 1 (by
    intro x
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [WithLp.prod_norm_sq_eq_of_L2]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hL x.fst) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hM x.snd) 2))

/-- Componentwise action of the auxiliary/carrier pair map
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem hilbertPairContractionMap_apply {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : E →L[ℝ] E') (M : F →L[ℝ] F')
    (hL : ∀ x, ‖L x‖ ≤ ‖x‖) (hM : ∀ y, ‖M y‖ ≤ ‖y‖) (x : WithLp 2 (E × F)) :
    hilbertPairContractionMap L M hL hM x = WithLp.toLp 2 (L x.fst, M x.snd) := rfl

/-- Contractivity survives auxiliary/carrier assembly
(`app:ch_background:prop:bg-inverse`). -/
theorem hilbertPairContractionMap_norm_le {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : E →L[ℝ] E') (M : F →L[ℝ] F')
    (hL : ∀ x, ‖L x‖ ≤ ‖x‖) (hM : ∀ y, ‖M y‖ ≤ ‖y‖) (x : WithLp 2 (E × F)) :
    ‖hilbertPairContractionMap L M hL hM x‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [WithLp.prod_norm_sq_eq_of_L2]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hL x.fst) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (hM x.snd) 2)

/-- Finite carrier family with the full physical `z,y` Sobolev Hilbert norm
(`app:ch_background:prop:bg-adjoint`). -/
abbrev CarrierFamilySobolevSpace (n : ℕ) (ι : Type*) [Fintype ι] (s : ℕ) :=
  PiLp 2 (fun _ : ι ↦ RawSobolevSpace n s)

/-- Image auxiliary input and all carriers, with their Hilbert sum norm
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-inverse`). -/
abbrev PhysicalInputSobolevSpace (n : ℕ) (ι : Type*) [Fintype ι] (s : ℕ) :=
  WithLp 2 (PeriodicSobolevSpace n (Euclidean n) s × CarrierFamilySobolevSpace n ι s)

/-- Full augmented `X^s`, including the exterior auxiliary summand
(`app:ch_background:prop:bg-inverse`). -/
abbrev AugmentedInputSobolevSpace (n : ℕ) (ι : Type*) [Fintype ι] (s : ℕ) :=
  WithLp 2 (PhysicalInputSobolevSpace n ι s × PeriodicSobolevSpace n (Euclidean n) s)

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The family norm is exactly the square sum of full raw norms
(`app:ch_background:eq:bg-r-inverse`). -/
theorem carrierFamilySobolev_norm_sq (s : ℕ) (u : CarrierFamilySobolevSpace n ι s) :
    ‖u‖ ^ 2 = ∑ i, rawSobolevNorm s (RawSobolevSpace.toRawL2 s (u i)) ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, RawSobolevSpace.norm_eq]

/-- Literal carrier family injection (`app:ch_background:defn:bg-row`). -/
def carrierFamilyToL2 (s : ℕ) : CarrierFamilySobolevSpace n ι s →L[ℝ] CarrierFamilyL2 n ι :=
  finiteContractionMap ((RawSobolevSpace.toRawL2 s).restrictScalars ℝ) (RawSobolevSpace.norm_toRawL2_le s)

/-- The family injection is componentwise the raw partial Fourier pullback
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem carrierFamilyToL2_apply (s : ℕ) (u : CarrierFamilySobolevSpace n ι s) (i : ι) :
    carrierFamilyToL2 s u i = RawSobolevSpace.toRawL2 s (u i) := rfl

/-- Carrier family injection is contractive (`app:ch_background:prop:bg-inverse`). -/
theorem norm_carrierFamilyToL2_le (s : ℕ) (u : CarrierFamilySobolevSpace n ι s) :
    ‖carrierFamilyToL2 s u‖ ≤ ‖u‖ := finiteContractionMap_norm_le _ _ u

/-- Actual physical row injection (`app:ch_background:defn:bg-row`). -/
def physicalInputToL2 (s : ℕ) : PhysicalInputSobolevSpace n ι s →L[ℝ] PhysicalInput n ι :=
  hilbertPairContractionMap (PeriodicSobolevSpace.toL2 s) (carrierFamilyToL2 s)
    (PeriodicSobolevSpace.norm_toL2_le s) (norm_carrierFamilyToL2_le s)

/-- Component formula for the physical injection (`app:ch_background:defn:bg-row`). -/
theorem physicalInputToL2_apply (s : ℕ) (u : PhysicalInputSobolevSpace n ι s) :
    physicalInputToL2 s u =
      WithLp.toLp 2 (PeriodicSobolevSpace.toL2 s u.fst, carrierFamilyToL2 s u.snd) := rfl

/-- Physical row injection is contractive (`app:ch_background:prop:bg-inverse`). -/
theorem norm_physicalInputToL2_le (s : ℕ) (u : PhysicalInputSobolevSpace n ι s) :
    ‖physicalInputToL2 s u‖ ≤ ‖u‖ := hilbertPairContractionMap_norm_le _ _ _ _ u

/-- Actual augmented row injection (`app:ch_background:defn:bg-row`). -/
def augmentedInputToL2 (s : ℕ) : AugmentedInputSobolevSpace n ι s →L[ℝ] AugmentedInput n ι :=
  hilbertPairContractionMap (physicalInputToL2 s) (PeriodicSobolevSpace.toL2 s)
    (norm_physicalInputToL2_le s) (PeriodicSobolevSpace.norm_toL2_le s)

/-- Component formula for the full injection (`app:ch_background:defn:bg-row`). -/
theorem augmentedInputToL2_apply (s : ℕ) (u : AugmentedInputSobolevSpace n ι s) :
    augmentedInputToL2 s u =
      WithLp.toLp 2 (physicalInputToL2 s u.fst, PeriodicSobolevSpace.toL2 s u.snd) := rfl

/-- Full row injection is contractive (`app:ch_background:prop:bg-inverse`). -/
theorem norm_augmentedInputToL2_le (s : ℕ) (u : AugmentedInputSobolevSpace n ι s) :
    ‖augmentedInputToL2 s u‖ ≤ ‖u‖ := hilbertPairContractionMap_norm_le _ _ _ _ u

/-- The carrier family injection retains every channel
(`app:ch_background:defn:bg-row`). -/
theorem carrierFamilyToL2_injective (s : ℕ) :
    Function.Injective (carrierFamilyToL2 (n := n) (ι := ι) s) := by
  intro u v h
  apply PiLp.ext
  intro i
  exact RawSobolevSpace.toRawL2_injective s (congrArg (fun f ↦ f i) h)

/-- The physical row injection is faithful (`app:ch_background:defn:bg-row`). -/
theorem physicalInputToL2_injective (s : ℕ) :
    Function.Injective (physicalInputToL2 (n := n) (ι := ι) s) := by
  intro u v h
  apply WithLp.ofLp_injective
  exact Prod.ext (PeriodicSobolevSpace.toL2_injective s (congrArg WithLp.fst h))
    (carrierFamilyToL2_injective s (congrArg WithLp.snd h))

/-- The full row injection is faithful (`app:ch_background:defn:bg-row`). -/
theorem augmentedInputToL2_injective (s : ℕ) :
    Function.Injective (augmentedInputToL2 (n := n) (ι := ι) s) := by
  intro u v h
  apply WithLp.ofLp_injective
  exact Prod.ext (physicalInputToL2_injective s (congrArg WithLp.fst h))
    (PeriodicSobolevSpace.toL2_injective s (congrArg WithLp.snd h))

/-- All raw carrier channels at zero have exactly their original L² norm
(`app:ch_background:prop:bg-inverse`). -/
def carrierFamilyZeroEquivL2 : CarrierFamilySobolevSpace n ι 0 ≃ₗᵢ[ℝ] CarrierFamilyL2 n ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ ↦
    { toLinearEquiv := RawSobolevSpace.zeroEquivL2.toLinearEquiv.restrictScalars ℝ
      norm_map' := RawSobolevSpace.zeroEquivL2.norm_map })

/-- Level zero is the original physical row input, isometrically
(`app:ch_background:defn:bg-row`). -/
def physicalInputZeroEquivL2 : PhysicalInputSobolevSpace n ι 0 ≃ₗᵢ[ℝ] PhysicalInput n ι :=
  LinearIsometryEquiv.withLpProdCongr 2 PeriodicSobolevSpace.zeroEquivL2 carrierFamilyZeroEquivL2

/-- Level zero is the original augmented row input, isometrically
(`app:ch_background:prop:bg-inverse`). -/
def augmentedInputZeroEquivL2 : AugmentedInputSobolevSpace n ι 0 ≃ₗᵢ[ℝ] AugmentedInput n ι :=
  LinearIsometryEquiv.withLpProdCongr 2 physicalInputZeroEquivL2 PeriodicSobolevSpace.zeroEquivL2

/-- The level-zero isometry is the actual full input injection
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem augmentedInputZeroEquivL2_apply (u : AugmentedInputSobolevSpace n ι 0) :
    augmentedInputZeroEquivL2 u = augmentedInputToL2 0 u := rfl

/-- Contractive compatible carrier inclusions (`app:ch_background:prop:bg-inverse`). -/
def carrierFamilyInclusion {s t : ℕ} (hst : s ≤ t) :
    CarrierFamilySobolevSpace n ι t →L[ℝ] CarrierFamilySobolevSpace n ι s :=
  finiteContractionMap ((RawSobolevSpace.inclusion hst).restrictScalars ℝ)
    (PhysicalSobolevSpace.norm_inclusion_le hst)

/-- Higher physical row levels include contractively in lower ones
(`app:ch_background:prop:bg-inverse`). -/
def physicalInputInclusion {s t : ℕ} (hst : s ≤ t) :
    PhysicalInputSobolevSpace n ι t →L[ℝ] PhysicalInputSobolevSpace n ι s :=
  hilbertPairContractionMap (PeriodicSobolevSpace.inclusion hst) (carrierFamilyInclusion hst)
    (fun u ↦ periodicSobolevSeminorm_mono hst (PeriodicSobolevSpace.toLevel t u))
    (finiteContractionMap_norm_le _ _)

/-- Component formula for physical level inclusions
(`app:ch_background:prop:bg-inverse`). -/
theorem physicalInputInclusion_apply {s t : ℕ} (hst : s ≤ t)
    (u : PhysicalInputSobolevSpace n ι t) :
    physicalInputInclusion hst u = WithLp.toLp 2
      (PeriodicSobolevSpace.inclusion hst u.fst, carrierFamilyInclusion hst u.snd) := rfl

/-- Higher full row levels include contractively in lower ones
(`app:ch_background:prop:bg-inverse`). -/
def augmentedInputInclusion {s t : ℕ} (hst : s ≤ t) :
    AugmentedInputSobolevSpace n ι t →L[ℝ] AugmentedInputSobolevSpace n ι s :=
  hilbertPairContractionMap (physicalInputInclusion hst) (PeriodicSobolevSpace.inclusion hst)
    (hilbertPairContractionMap_norm_le _ _ _ _)
    (fun u ↦ periodicSobolevSeminorm_mono hst (PeriodicSobolevSpace.toLevel t u))

/-- Component formula for augmented level inclusions
(`app:ch_background:prop:bg-inverse`). -/
theorem augmentedInputInclusion_apply {s t : ℕ} (hst : s ≤ t)
    (u : AugmentedInputSobolevSpace n ι t) :
    augmentedInputInclusion hst u = WithLp.toLp 2
      (physicalInputInclusion hst u.fst, PeriodicSobolevSpace.inclusion hst u.snd) := rfl

/-- Full row inclusions are contractive (`app:ch_background:prop:bg-inverse`). -/
theorem norm_augmentedInputInclusion_le {s t : ℕ} (hst : s ≤ t)
    (u : AugmentedInputSobolevSpace n ι t) : ‖augmentedInputInclusion hst u‖ ≤ ‖u‖ :=
  hilbertPairContractionMap_norm_le _ _ _ _ u

/-- Carrier inclusions retain every raw component
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem carrierFamilyToL2_inclusion {s t : ℕ} (hst : s ≤ t)
    (u : CarrierFamilySobolevSpace n ι t) :
    carrierFamilyToL2 s (carrierFamilyInclusion hst u) = carrierFamilyToL2 t u := by
  apply PiLp.ext
  intro i
  exact RawSobolevSpace.toRawL2_inclusion hst (u i)

private theorem periodic_inclusion_apply {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {s t : ℕ} (hst : s ≤ t)
    (u : PeriodicSobolevSpace n F t) :
    PeriodicSobolevSpace.inclusion hst u = (PeriodicSobolevSpace.toLevel s).symm
      ⟨(PeriodicSobolevSpace.toLevel t u).val,
        antitone_periodicSobolevLevel hst (PeriodicSobolevSpace.toLevel t u).property⟩ := rfl

private theorem periodic_toL2_inclusion {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {s t : ℕ} (hst : s ≤ t)
    (u : PeriodicSobolevSpace n F t) :
    PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.inclusion hst u) =
      PeriodicSobolevSpace.toL2 t u := by
  rw [PeriodicSobolevSpace.toL2_apply, periodic_inclusion_apply,
    LinearEquiv.apply_symm_apply, PeriodicSobolevSpace.toL2_apply]

/-- Physical row inclusions retain both the auxiliary and carrier data
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem physicalInputToL2_inclusion {s t : ℕ} (hst : s ≤ t)
    (u : PhysicalInputSobolevSpace n ι t) :
    physicalInputToL2 s (physicalInputInclusion hst u) = physicalInputToL2 t u := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact periodic_toL2_inclusion hst u.fst
  · exact carrierFamilyToL2_inclusion hst u.snd

/-- Inclusions retain the same literal full raw datum
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem augmentedInputToL2_inclusion {s t : ℕ} (hst : s ≤ t)
    (u : AugmentedInputSobolevSpace n ι t) :
    augmentedInputToL2 s (augmentedInputInclusion hst u) = augmentedInputToL2 t u := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact physicalInputToL2_inclusion hst u.fst
  · exact periodic_toL2_inclusion hst u.snd

/-- Full row inclusions compose compatibly (`app:ch_background:prop:bg-inverse`). -/
theorem augmentedInputInclusion_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t)
    (u : AugmentedInputSobolevSpace n ι t) :
    augmentedInputInclusion hrs (augmentedInputInclusion hst u) =
      augmentedInputInclusion (hrs.trans hst) u := by
  apply augmentedInputToL2_injective r
  simp only [augmentedInputToL2_inclusion]

/-- A level's self-inclusion is the identity (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem augmentedInputInclusion_refl (s : ℕ) (u : AugmentedInputSobolevSpace n ι s) :
    augmentedInputInclusion (le_refl s) u = u := by
  apply augmentedInputToL2_injective s
  exact augmentedInputToL2_inclusion (le_refl s) u

/-- Smooth auxiliary functions represent the same datum at every level
(`app:ch_background:prop:bg-adjoint`). -/
theorem auxiliaryInclusion_ofSmooth {s t : ℕ} (hst : s ≤ t)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    PeriodicSobolevSpace.inclusion hst (PeriodicSobolevSpace.ofSmooth t f hf) =
      PeriodicSobolevSpace.ofSmooth s f hf := by
  rw [periodic_inclusion_apply]
  rfl

end JanetCartan.CarrierSobolev
