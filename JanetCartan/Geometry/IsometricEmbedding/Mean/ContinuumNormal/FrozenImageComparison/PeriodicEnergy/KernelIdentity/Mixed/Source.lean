module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Mixed.Integrability

/-!
# Smooth representatives of the mixed source

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the lattice adjoint
applied to an arbitrary L² input is compact and smooth. Differentiating
its source-masked representative differentiates the actual compact source
kernel, including both source masks. The consumers are the Schwartz action
of the Euclidean channel and the mixed Bessel/Fubini contraction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

namespace KernelIdentity

private theorem weightedKernel_majorant {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : E × E → F} (hc : Continuous K) (hs : HasCompactSupport K)
    (u : R²) (j : Fin n) :
    ∃ b : E → ℝ, Integrable b ∧ ∀ x y, ‖u y j • K (x, y)‖ ≤ b y := by
  let S := Prod.snd '' tsupport K
  have hS : IsCompact S := hs.image continuous_snd
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  have hu := (Lp.memLp u).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
  refine ⟨fun y ↦ ‖S.indicator (fun z ↦ u z j) y‖ * C, ?_, ?_⟩
  · exact ((hu.locallyIntegrable (by norm_num)).integrableOn_isCompact hS
      |>.integrable_indicator hS.measurableSet).norm.mul_const C
  · intro x y
    by_cases hy : y ∈ S
    · simpa only [Set.indicator_of_mem hy, norm_smul] using
        mul_le_mul_of_nonneg_left (hC (x, y)) (norm_nonneg (u y j))
    · have hz : K (x, y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp ↦ hy ⟨(x, y), hp, rfl⟩)
      simp [hz, Set.indicator_of_notMem hy]

private theorem integrable_weightedKernel {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : E × E → F} (hc : Continuous K) (hs : HasCompactSupport K)
    (u : R²) (j : Fin n) (x : E) :
    Integrable (fun y ↦ u y j • K (x, y)) := by
  obtain ⟨b, hb, hbound⟩ := weightedKernel_majorant hc hs u j
  exact hb.mono'
    (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).smul
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (hbound x))

private theorem outputDerivative_regular {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : E × E → F} (hc : ContDiff ℝ ∞ K) (hs : HasCompactSupport K) :
    ContDiff ℝ ∞ (fun p ↦ (fderiv ℝ K p).comp (ContinuousLinearMap.inl ℝ E E)) ∧
    HasCompactSupport (fun p ↦ (fderiv ℝ K p).comp (ContinuousLinearMap.inl ℝ E E)) := by
  refine ⟨(hc.fderiv_right (by simp)).clm_comp contDiff_const, ?_⟩
  exact (hs.fderiv ℝ).comp_left
    (g := fun L : E × E →L[ℝ] F ↦ L.comp (ContinuousLinearMap.inl ℝ E E)) (by simp)

private theorem hasFDerivAt_weightedKernel {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {K : E × E → F} (hc : ContDiff ℝ ∞ K) (hs : HasCompactSupport K)
    (u : R²) (j : Fin n) (x : E) :
    HasFDerivAt (fun z ↦ ∫ y, u y j • K (z, y))
      (∫ y, u y j • (fderiv ℝ K (x, y)).comp (ContinuousLinearMap.inl ℝ E E)) x := by
  obtain ⟨hd, hds⟩ := outputDerivative_regular hc hs
  obtain ⟨b, hb, hbound⟩ := weightedKernel_majorant hd.continuous hds u j
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := univ) (bound := b) (F' := fun z y ↦
      u y j • (fderiv ℝ K (z, y)).comp (ContinuousLinearMap.inl ℝ E E)) univ_mem
  · exact Eventually.of_forall fun z ↦ (integrable_weightedKernel hc.continuous hs u j z).aestronglyMeasurable
  · exact integrable_weightedKernel hc.continuous hs u j x
  · exact (integrable_weightedKernel hd.continuous hds u j x).aestronglyMeasurable
  · exact Eventually.of_forall fun y z _ ↦ hbound z y
  · exact hb
  · exact Eventually.of_forall fun y z _ ↦
      (((hc.differentiable (by simp) (z, y)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).prodMk (hasFDerivAt_const y z))).const_smul (u y j))

private theorem contDiff_weightedKernel_nat {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (m : ℕ)
    {K : E × E → F} (hc : ContDiff ℝ ∞ K) (hs : HasCompactSupport K)
    (u : R²) (j : Fin n) :
    ContDiff ℝ m (fun x ↦ ∫ y, u y j • K (x, y)) := by
  induction m generalizing F with
  | zero =>
    simp only [Nat.cast_zero, contDiff_zero]
    obtain ⟨b, hb, hbound⟩ := weightedKernel_majorant hc.continuous hs u j
    apply continuous_of_dominated (bound := b)
    · exact fun x ↦ (integrable_weightedKernel hc.continuous hs u j x).aestronglyMeasurable
    · exact fun x ↦ Eventually.of_forall (hbound x)
    · exact hb
    · exact Eventually.of_forall fun y ↦
        (hc.continuous.comp (continuous_id.prodMk continuous_const)).const_smul (u y j)
  | succ m ih =>
    obtain ⟨hd, hds⟩ := outputDerivative_regular hc hs
    rw [show ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp,
      contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ih hd hds, fun x ↦ hasFDerivAt_weightedKernel hc hs u j x⟩

/-- The continuous compact scalar entries of the mixed adjoint define L²
representatives. Consumer: Hilbert adjunction of the forward mixed formula
in `app:ch_background:prop:bg-frame`. -/
theorem memLp_scalarKernel_integral {K : E × E → ℝ}
    (hc : Continuous K) (hs : HasCompactSupport K) (u : R²) (j : Fin n) :
    MemLp (fun x ↦ ∫ y, K (x, y) * u y j) 2 := by
  have hcont : Continuous (fun x ↦ ∫ y, u y j • K (x, y)) := by
    obtain ⟨b, hb, hbound⟩ := weightedKernel_majorant hc hs u j
    apply continuous_of_dominated (bound := b)
    · exact fun x ↦ (integrable_weightedKernel hc hs u j x).aestronglyMeasurable
    · exact fun x ↦ Eventually.of_forall (hbound x)
    · exact hb
    · exact Eventually.of_forall fun y ↦
        (hc.comp (continuous_id.prodMk continuous_const)).const_smul (u y j)
  have hsupp : HasCompactSupport (fun x ↦ ∫ y, u y j • K (x, y)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
    intro x hx
    by_contra hn
    apply hx
    have hz (y : E) : K (x, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hp ↦ hn ⟨(x, y), hp, rfl⟩)
    simp [hz]
  simpa only [smul_eq_mul, mul_comm] using hcont.memLp_of_hasCompactSupport hsupp

/-- Compact smooth scalar kernels give compact smooth representatives on
arbitrary L² inputs. This is used only for the lattice-adjoint sections and
their source mask in `app:ch_background:prop:bg-frame`. -/
theorem scalarKernel_integral_regular {K : E × E → ℝ}
    (hc : ContDiff ℝ ∞ K) (hs : HasCompactSupport K) (u : R²) (j : Fin n) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, K (x, y) * u y j) ∧
    HasCompactSupport (fun x ↦ ∫ y, K (x, y) * u y j) := by
  constructor
  · apply contDiff_iff_forall_nat_le.mpr
    intro m _
    simpa only [smul_eq_mul, mul_comm] using contDiff_weightedKernel_nat m hc hs u j
  · apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
    intro x hx
    by_contra hn
    apply hx
    have hz (y : E) : K (x, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hp ↦ hn ⟨(x, y), hp, rfl⟩)
    simp [hz]

/-- The literal lattice adjoint has a smooth compact coordinate representative
on every L² input. Consumer: the Euclidean channel's Schwartz action, in
`app:ch_background:prop:bg-frame`. -/
theorem latticeAdjoint_coordinate_regular (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (k : Fin n) :
    ContDiff ℝ ∞ (fun z ↦ ∑ j, ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j) ∧
    HasCompactSupport (fun z ↦ ∑ j, ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j) := by
  have h (j : Fin n) := scalarKernel_integral_regular
    ((contDiff_fixedLatticeKernel hR hcell A j k).comp (contDiff_snd.prodMk contDiff_fst))
    ((hasCompactSupport_fixedLatticeKernel hR A j k).comp_homeomorph
      (Homeomorph.prodComm E E)) u j
  refine ⟨ContDiff.sum fun j _ ↦ (h j).1, ?_⟩
  convert HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦ (h j).2) using 1
  ext z
  simp only [Finset.sum_apply, Function.comp_apply]

/-- Source differentiation passes through the actual compact mixed section
on every L² input. This supplies the derivative in `B D*`, with both source
masks retained, for `app:ch_background:prop:bg-frame`. -/
theorem fderiv_mixedSource_integral (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (j k a : Fin n) (x : E) :
    fderiv ℝ (fun z ↦ ∫ y, fixedMixedSourceKernel hR A j k (z, y) * u y j) x
      (EuclideanSpace.single a 1) =
      ∫ y, fderiv ℝ (fixedMixedSourceKernel hR A j k) (x, y)
        (EuclideanSpace.single a 1, 0) * u y j := by
  have hc := contDiff_fixedMixedSourceKernel hR hcell A j k
  have hs := hasCompactSupport_fixedMixedSourceKernel hR A j k
  have hd := hasFDerivAt_weightedKernel hc hs u j x
  have hi := integrable_weightedKernel (outputDerivative_regular hc hs).1.continuous
    (outputDerivative_regular hc hs).2 u j x
  simp only [smul_eq_mul, mul_comm (u _ j)] at hd
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul, mul_comm (u _ j)]

/-- Source multiplication of the literal adjoint representative retains
the original mixed source section (`app:ch_background:prop:bg-frame`). -/
theorem source_mul_latticeAdjoint_integral (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (k : Fin n) (z : E) :
    FixedCutoffs.physical hR 2 z *
      (∑ j, ∫ y, fixedLatticeKernel hR A j k (y, z) * u y j) =
      ∑ j, ∫ y, fixedMixedSourceKernel hR A j k (z, y) * u y j := by
  simp only [fixedMixedSourceKernel, Prod.swap_prod_mk, mul_assoc,
    integral_const_mul, Finset.mul_sum]

/-- The differential factor in `B D*` acts on the whole compact source
section, including the source multiplier. Consumer: the Bessel derivative
transfer of `app:ch_background:prop:bg-frame`. -/
theorem fderiv_source_mul_latticeAdjoint_integral (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (u : R²) (k a : Fin n) (z : E) :
    fderiv ℝ (fun x ↦ FixedCutoffs.physical hR 2 x *
      (∑ j, ∫ y, fixedLatticeKernel hR A j k (y, x) * u y j)) z
        (EuclideanSpace.single a 1) =
      ∑ j, ∫ y, fderiv ℝ (fixedMixedSourceKernel hR A j k) (z, y)
        (EuclideanSpace.single a 1, 0) * u y j := by
  simp_rw [source_mul_latticeAdjoint_integral]
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ fderiv_mixedSource_integral hR hcell A u j k a z
  · intro j _
    exact (scalarKernel_integral_regular (contDiff_fixedMixedSourceKernel hR hcell A j k)
      (hasCompactSupport_fixedMixedSourceKernel hR A j k) u j).1.differentiable (by simp) z

end KernelIdentity

end JanetCartan.ContinuumNormal.FrozenImageComparison
