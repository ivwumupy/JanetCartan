module

public import JanetCartan.Iteration.PhysicalMean.CanonicalForcingProfiles

/-!
# Original quadrature forcing from weighted joint smoothness

Consumer: `PhysicalMean.originalBackgroundQuadratureForcing_source_profile`,
`new:eq:mean-source` and `app:ch_mean_pairs:eq:comparison-input`. The original
positive-baseline kernel need only be smooth after multiplication by the FULL
original outer carrier weight. All original weights, samples, colors, masks,
mesh and shifts remain unchanged. In particular no inner native cutoff or
amplitude rescaling is introduced, and no division by a carrier weight occurs.

This is an independent implication from weighted joint smoothness and weighted
joint derivative bounds. It does not instantiate the original-data producers.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open CurrentMean SmoothPeriodicFamily SeparatedSampling LatticeQuadrature
  Sampling.Realization Sampling.BackgroundQuadrature Sampling.ColoredNormalComparison
  FiniteChain.Retarded.KernelDecay RawPrimary.AmplitudeGrades

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Algebraic factoring of the literal original sample weight, valid also at
zero weights. Used to obtain sample smoothness without smoothness of the
unweighted positive-baseline kernel (`new:eq:mean-source`). -/
theorem originalWeight_smul_eq_weighted (ψ : Point → ℝ) (window : ℝ → ℝ)
    (h : ℝ) (U : Lattice → Point) (a : Sample) (v : V) :
    weight ψ window h U a • v =
      (h^3 * blockWeight window h a.1 (node h U a)) • (ψ (node h U a) • v) := by
  rw [smul_smul]
  congr 1
  unfold weight
  ring

private theorem contDiff_originalWeightedCarrierIntegral [CompleteSpace V]
    {ψ ρ : Point → ℝ} (hψc : HasCompactSupport ψ) (hρ : ContDiff ℝ ∞ ρ)
    {H : Euclidean n × Point → V}
    (hweighted : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ ψ w.2 • H w)) :
    ContDiff ℝ ∞ (fun y ↦ ∫ z, ρ z • (ψ z • H (y,z))) := by
  apply contDiff_integral_commonCarrier ((hρ.comp contDiff_snd).smul hweighted) hψc
  intro y z hz
  change ρ z • (ψ z • H (y,z)) = 0
  rw [image_eq_zero_of_notMem_tsupport hz, zero_smul, smul_zero]

/-- Smoothness of the literal original sampled-minus-colored-integral field
requires only joint smoothness of `ψᵢ • Hᵢ,c`. Samples factor the literal `μ`;
the integral uses compact original `tsupport ψᵢ`. Zero carrier weights are
allowed (`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_originalBackgroundError_of_weighted [CompleteSpace V]
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψc : ∀ i, HasCompactSupport (ψ i))
    (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hweighted : ∀ i c, ContDiff ℝ ∞
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w)) :
    ContDiff ℝ ∞ (fun x ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (x,z))) := by
  classical
  let window := convolvedBoxWindow κ p
  let mask := coloredBlockMask p (integerCube (blockCutoff p B h)) window h
  have hsample (i : I) (a : Sample) : ContDiff ℝ ∞ (fun y ↦
      weight (ψ i) window h (U i) a • H i (color p a.1) (y,node h (U i) a)) := by
    simp_rw [originalWeight_smul_eq_weighted]
    exact ((hweighted i (color p a.1)).comp
      (contDiff_id.prodMk contDiff_const)).const_smul _
  have hint (i : I) (c : Fin 3 → Fin (p+1)) : ContDiff ℝ ∞
      (fun y ↦ ∫ z, mask c z • (ψ i z • H i c (y,z))) :=
    contDiff_originalWeightedCarrierIntegral (hψc i)
      (contDiff_coloredBlockMask hκc hκ p _ h c) (hweighted i c)
  exact ContDiff.sum fun i _ ↦
    (ContDiff.sum fun a _ ↦ hsample i a).sub (ContDiff.sum fun c _ ↦ hint i c)

/-- Weighted-only smooth periodicity for the SAME original error. No
positive-dimension assumption is imposed (`new:eq:mean-source`). -/
theorem isSmoothPeriodic_originalBackgroundError_of_weighted
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψc : ∀ i, HasCompactSupport (ψ i))
    (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hweighted : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ i w.2 • H i c (torusQuotient w.1,w.2))) :
    IsSmoothPeriodic (fun x ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (x,z))) := by
  have hsmooth := contDiff_originalBackgroundError_of_weighted hκc hκ p B h ψ hψc U
    (fun i c w ↦ H i c (torusQuotient w.1,w.2)) hweighted
  have hquot : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hquot.isQuotientMap.continuous_iff.mpr hsmooth.continuous, hsmooth⟩

/-- The original CONTINUUM MINUS SAMPLE source, constructed from weighted
joint smoothness alone. Its value retains the full original positive baseline,
not an inner-cutoff or amplitude-scaled version (`new:eq:mean-source`). -/
def weightedOriginalBackgroundQuadratureForcing
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψc : ∀ i, HasCompactSupport (ψ i))
    (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hweighted : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ i w.2 • H i c (torusQuotient w.1,w.2))) : SmoothResidual n :=
  -⟨fun x _ ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (x,z)),
    fun _ ↦ isSmoothPeriodic_originalBackgroundError_of_weighted
      hκc hκ p B h ψ hψc U H hweighted⟩

/-- Exact original source value at every torus point, by construction
(`new:eq:mean-source`). -/
theorem weightedOriginalBackgroundQuadratureForcing_apply
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψc : ∀ i, HasCompactSupport (ψ i))
    (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hweighted : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ i w.2 • H i c (torusQuotient w.1,w.2))) (x : Torus n) :
    (weightedOriginalBackgroundQuadratureForcing hκc hκ p B h ψ hψc U H hweighted).val x () =
      -familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
        (fun i c z ↦ H i c (x,z)) := rfl

/-- Compatibility with the previous globally-unweighted-smooth API: the
sources themselves, not just their norms, are equal (`new:eq:mean-source`). -/
theorem weightedOriginalBackgroundQuadratureForcing_eq_original
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hweighted : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ i w.2 • H i c (torusQuotient w.1,w.2)))
    (hH : ∀ i c, ContDiff ℝ ∞
      (fun w : Euclidean n × Point ↦ H i c (torusQuotient w.1,w.2))) :
    weightedOriginalBackgroundQuadratureForcing hκc hκ p B h ψ hψc U H hweighted =
      originalBackgroundQuadratureForcing hκc hκ p B h ψ hψ hψc U H hH := by
  rfl

private theorem weighted_norm_jointPhysicalJet_le {F : Euclidean n × Point → V}
    (hF : ContDiff ℝ ∞ F) (q j : ℕ) (w : Euclidean n × Point) :
    ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Point ↦
      iteratedFDeriv ℝ q (fun x ↦ F (x,t.2)) t.1) w‖ ≤
        ‖iteratedFDeriv ℝ (j+q) F w‖ := by
  induction q generalizing j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Prod.mk.eta, Nat.add_zero] using
      (continuousMultilinearCurryFin0 ℝ (Euclidean n) V).symm.norm_iteratedFDeriv_comp_left F w j |>.le
  | succ q ih =>
    let J : Euclidean n × Point → (Euclidean n [×q]→L[ℝ] V) :=
      fun t ↦ iteratedFDeriv ℝ q (fun x ↦ F (x,t.2)) t.1
    have hJ : ContDiff ℝ ∞ J := contDiff_outputJet hF q
    let L : (Euclidean n →L[ℝ] (Euclidean n [×q]→L[ℝ] V)) ≃ₗᵢ[ℝ]
        (Euclidean n [×(q+1)]→L[ℝ] V) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q+1) ↦ Euclidean n) V).symm
    let B : Euclidean n →L[ℝ] Euclidean n × Point := ContinuousLinearMap.inl ℝ _ _
    have he : (fun t : Euclidean n × Point ↦ iteratedFDeriv ℝ (q+1)
        (fun x ↦ F (x,t.2)) t.1) = L ∘ (fun t ↦ (fderiv ℝ J t).comp B) := by
      funext t
      have hd : fderiv ℝ (fun x ↦ J (x,t.2)) t.1 = (fderiv ℝ J t).comp B :=
        ((hJ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp t.1
          ((hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _))).fderiv
      change L (fderiv ℝ (fun x ↦ J (x,t.2)) t.1) = _
      rw [hd, Function.comp_apply]
    rw [he, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (G := Euclidean n [×(q+1)]→L[ℝ] V) L (fun t ↦ (fderiv ℝ J t).comp B) w j]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (j+1) J w‖ :=
        norm_iteratedFDeriv_restricted_fderiv_le hJ.contDiffAt B
          (ContinuousLinearMap.norm_inl_le_one ..) j
      _ ≤ ‖iteratedFDeriv ℝ ((j+1)+q) F w‖ := ih (j+1)
      _ = _ := by rw [show (j+1)+q = j+(q+1) by omega]

private theorem weighted_norm_parameterPhysicalJet_le {F : Euclidean n × Point → V}
    (hF : ContDiff ℝ ∞ F) (q p : ℕ) (x : Euclidean n) (z : Point) :
    ‖iteratedFDeriv ℝ p (fun t ↦ iteratedFDeriv ℝ q (fun y ↦ F (y,t)) x) z‖ ≤
      ‖iteratedFDeriv ℝ (p+q) F (x,z)‖ := by
  let J : Euclidean n × Point → (Euclidean n [×q]→L[ℝ] V) :=
    fun w ↦ iteratedFDeriv ℝ q (fun y ↦ F (y,w.2)) w.1
  have hJ : ContDiff ℝ ∞ J := contDiff_outputJet hF q
  let L : Point →L[ℝ] Euclidean n × Point := ContinuousLinearMap.inr ℝ _ _
  let G : Euclidean n × Point → (Euclidean n [×q]→L[ℝ] V) := fun w ↦ J ((x,0)+w)
  have hG : ContDiff ℝ ∞ G := hJ.comp (contDiff_const.add contDiff_id)
  have he : (fun t ↦ iteratedFDeriv ℝ q (fun y ↦ F (y,t)) x) = G ∘ L := by
    funext t
    simp only [G, L, J, Function.comp_apply, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [he, L.iteratedFDeriv_comp_right hG z (by simp : (p : ℕ∞ω) ≤ ∞)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ p G (L z)) (fun _ : Fin p ↦ L)
  have hb' : ‖(iteratedFDeriv ℝ p G (L z)).compContinuousLinearMap (fun _ : Fin p ↦ L)‖ ≤
      ‖iteratedFDeriv ℝ p G (L z)‖ := by
    apply hb.trans
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ..))
  have heval : ‖iteratedFDeriv ℝ p G (L z)‖ = ‖iteratedFDeriv ℝ p J (x,z)‖ := by
    simp only [G, L, iteratedFDeriv_comp_add_left, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [heval] at hb'
  exact hb'.trans (weighted_norm_jointPhysicalJet_le hF q p (x,z))

private theorem contDiff_originalCarrierBlock (p : ℕ) (window : ℝ → ℝ)
    (h : ℝ) (U : Lattice → Point) (b : Lattice)
    {F : Euclidean n × Point → V} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y ↦ carrierBlock p window h (fun z ↦ F (y,z)) U b) :=
  ContDiff.sum fun _ _ ↦ (hF.comp (contDiff_id.prodMk contDiff_const)).const_smul _

private theorem iteratedFDeriv_originalCarrierBlock (p : ℕ) (window : ℝ → ℝ)
    (h : ℝ) (U : Lattice → Point) (b : Lattice)
    {F : Euclidean n × Point → V} (hF : ContDiff ℝ ∞ F) (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (fun y ↦ carrierBlock p window h (fun z ↦ F (y,z)) U b) x =
      carrierBlock p window h (fun z ↦ iteratedFDeriv ℝ q (fun y ↦ F (y,z)) x) U b := by
  unfold carrierBlock
  erw [iteratedFDeriv_fun_sum_apply (fun _ _ ↦
    ((hF.comp (contDiff_id.prodMk contDiff_const)).const_smul _).of_le (by simp) |>.contDiffAt)]
  apply Finset.sum_congr rfl
  intro m _
  exact iteratedFDeriv_const_smul_apply'
    ((hF.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt

private theorem iteratedFDeriv_originalWeightedCarrierIntegral
    {ψ ρ : Point → ℝ} (hψc : HasCompactSupport ψ) (hρ : ContDiff ℝ ∞ ρ)
    {H : Euclidean n × Point → V}
    (hweighted : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ ψ w.2 • H w))
    (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (fun y ↦ ∫ z, ρ z • (ψ z • H (y,z))) x =
      ∫ z, ρ z • iteratedFDeriv ℝ q (fun y ↦ ψ z • H (y,z)) x := by
  have hs (y : Euclidean n) (z : Point) (hz : z ∉ tsupport ψ) :
      ρ z • (ψ z • H (y,z)) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul, smul_zero]
  erw [iteratedFDeriv_integral_commonCarrier (μ := volume)
    ((hρ.comp contDiff_snd).smul hweighted) hψc hs q x]
  apply integral_congr_ae
  filter_upwards [] with z
  change iteratedFDeriv ℝ q (fun y ↦ ρ z • (ψ z • H (y,z))) x =
    ρ z • iteratedFDeriv ℝ q (fun y ↦ ψ z • H (y,z)) x
  have hslice : ContDiff ℝ ∞ (fun y : Euclidean n ↦ ψ z • H (y,z)) :=
    hweighted.comp (contDiff_id.prodMk contDiff_const)
  exact iteratedFDeriv_const_smul_apply' (a := ρ z) (f := fun y ↦ ψ z • H (y,z))
    (hslice.of_le (by simp)).contDiffAt

private theorem originalBackgroundError_eq_blocks_of_weighted
    {I : Type} [Fintype I] {p : ℕ} {window : ℝ → ℝ} {W : ℝ}
    (hw : WindowBounds p window W) (hwindow : Continuous window)
    (B : ℝ) {h : ℝ} (hh : h ≠ 0) (ψ : I → Point → ℝ)
    (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Point → V)
    (hweighted : ∀ i c, Continuous (fun z ↦ ψ i z • H i c z)) :
    familyBackgroundError p B ψ window h U H =
      ∑ i, ∑ b ∈ integerCube (blockCutoff p B h),
        (carrierBlock p window h (fun z ↦ ψ i z • H i (color p b) z) (U i) b -
          ∫ z, blockWeight window h b z • (ψ i z • H i (color p b) z)) := by
  unfold familyBackgroundError
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_carrierBlock_eq_samples,
    ← sum_blockIntegrals_eq_sum_coloredMask_integrals _ hw hwindow hh _ (hweighted i),
    ← Finset.sum_sub_distrib]

/-- Physical differentiation of the original error as the SAME finite block
quadrature of the already-weighted amplitude. This identity is derived from
the literal original sample enumeration, not from unweighted kernel jets;
all compact domination is internal (`app:ch_waves:eq:background-quadrature`). -/
theorem iteratedFDeriv_originalBackgroundError_blocks_of_weighted [CompleteSpace V]
    {I : Type} [Fintype I] {p : ℕ} {window : ℝ → ℝ} {W : ℝ}
    (hw : WindowBounds p window W) (hwindow : ContDiff ℝ ∞ window)
    (B : ℝ) {h : ℝ} (hh : h ≠ 0) (ψ : I → Point → ℝ)
    (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hweighted : ∀ i c, ContDiff ℝ ∞
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w)) (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (fun y ↦ familyBackgroundError p B ψ window h U
      (fun i c z ↦ H i c (y,z))) x =
      ∑ i, ∑ b ∈ integerCube (blockCutoff p B h),
        (carrierBlock p window h
          (fun z ↦ iteratedFDeriv ℝ q (fun y ↦ ψ i z • H i (color p b) (y,z)) x) (U i) b -
        ∫ z, blockWeight window h b z •
          iteratedFDeriv ℝ q (fun y ↦ ψ i z • H i (color p b) (y,z)) x) := by
  have he : (fun y ↦ familyBackgroundError p B ψ window h U (fun i c z ↦ H i c (y,z))) =
      fun y ↦ ∑ i, ∑ b ∈ integerCube (blockCutoff p B h),
        (carrierBlock p window h (fun z ↦ ψ i z • H i (color p b) (y,z)) (U i) b -
        ∫ z, blockWeight window h b z • (ψ i z • H i (color p b) (y,z))) := by
    funext y
    exact originalBackgroundError_eq_blocks_of_weighted hw hwindow.continuous B hh ψ U
      (fun i c z ↦ H i c (y,z)) (fun i c ↦ (hweighted i c).continuous.comp
        (continuous_const.prodMk continuous_id))
  have hs (i : I) (b : Lattice) : ContDiff ℝ ∞ (fun y ↦
      carrierBlock p window h (fun z ↦ ψ i z • H i (color p b) (y,z)) (U i) b) :=
    contDiff_originalCarrierBlock p window h (U i) b (hweighted i (color p b))
  have hi (i : I) (b : Lattice) : ContDiff ℝ ∞ (fun y ↦
      ∫ z, blockWeight window h b z • (ψ i z • H i (color p b) (y,z))) :=
    contDiff_originalWeightedCarrierIntegral (hψc i)
      (contDiff_blockWeight hwindow h b) (hweighted i (color p b))
  rw [he, iteratedFDeriv_fun_sum_apply (fun i _ ↦
    (ContDiff.sum fun b _ ↦ (hs i b).sub (hi i b)).of_le (by simp) |>.contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_fun_sum_apply (fun b _ ↦ ((hs i b).sub (hi i b)).of_le (by simp) |>.contDiffAt)]
  apply Finset.sum_congr rfl
  intro b _
  erw [iteratedFDeriv_sub_apply ((hs i b).of_le (by simp)).contDiffAt
    ((hi i b).of_le (by simp)).contDiffAt,
    iteratedFDeriv_originalCarrierBlock p window h (U i) b (hweighted i (color p b)),
    iteratedFDeriv_originalWeightedCarrierIntegral (hψc i)
      (contDiff_blockWeight hwindow h b) (hweighted i (color p b))]

private theorem norm_originalWeightedBlockErrors_le [CompleteSpace V]
    {κ : ℝ → ℝ} (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hκint : ∫ t, κ t = 1) {p : ℕ} (hp : 0 < p) {W : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) W) {B : ℝ} (hB : 0 ≤ B)
    (F : (Fin 3 → Fin (p+1)) → Point → V) (hF : ∀ c, ContDiff ℝ p (F c))
    {A : ℝ} (hA : 0 ≤ A) (hD : ∀ c z, ‖iteratedFDeriv ℝ p (F c) z‖ ≤ A)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : Lattice → Point)
    (hU : ∀ b j, 0 ≤ U b j ∧ U b j < h) :
    ‖∑ b ∈ integerCube (blockCutoff p B h),
      (carrierBlock p (convolvedBoxWindow κ p) h (F (color p b)) U b -
        ∫ z, blockWeight (convolvedBoxWindow κ p) h b z • F (color p b) z)‖ ≤
      backgroundQuadratureConstant p B * A * h^p := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ integerCube (blockCutoff p B h),
        h^3 * (2*A*(h*windowRadius p)^p) :=
      Finset.sum_le_sum fun b _ ↦ norm_carrierBlock_error_le hκc hκ hκint hp hw
        (hF (color p b)) hA (hD (color p b)) hh U b (hU b)
    _ = (((integerCube (blockCutoff p B h)).card : ℝ)*h^3) *
        (2*A*(h*windowRadius p)^p) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ blockCountConstant p B * (2*A*(h*windowRadius p)^p) :=
      mul_le_mul_of_nonneg_right (card_blocks_mul_cube_le hB hh hh₁)
        (by dsimp [windowRadius]; positivity)
    _ = backgroundQuadratureConstant p B * A * h^p := by
      unfold backgroundQuadratureConstant
      rw [mul_pow]
      ring

/-- The exact original physical-jet quadrature bound from WEIGHTED joint
smoothness alone. The only quantitative premise is the `p+q` derivative of
`ψᵢ • Hᵢ,c`; no desired error bound or unweighted derivative is assumed
(`app:ch_mean_pairs:eq:comparison-input`). -/
theorem originalBackgroundError_physicalJet_le_of_weighted [CompleteSpace V]
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hweighted : ∀ i c, ContDiff ℝ ∞
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w)) (q : ℕ) (x : Euclidean n)
    (D : I → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hjoint : ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w) (x,z)‖ ≤ D i)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    ‖iteratedFDeriv ℝ q (fun y ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (y,z))) x‖ ≤
        backgroundQuadratureConstant p B * (∑ i, D i) * h^p := by
  have hw := convolvedBoxWindow_bounds (hκ.continuous.integrable_of_hasCompactSupport hκc)
    hκint hκ0 hκsupp hp
  rw [iteratedFDeriv_originalBackgroundError_blocks_of_weighted hw
    (contDiff_convolvedBoxWindow hκc hκ p) B hh.ne' ψ hψc U H hweighted]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, backgroundQuadratureConstant p B * D i * h^p := by
      apply Finset.sum_le_sum
      intro i _
      apply norm_originalWeightedBlockErrors_le hκc hκ hκint hp hw (hpatch i).radius_nonneg
        (fun c z ↦ iteratedFDeriv ℝ q (fun y ↦ ψ i z • H i c (y,z)) x) _ (hD i) _ hh hh₁ (U i) (hU i)
      · intro c
        exact ((contDiff_outputJet (hweighted i c) q).comp
          (contDiff_const.prodMk contDiff_id)).of_le (by simp)
      · intro c z
        exact (weighted_norm_parameterPhysicalJet_le (hweighted i c) q p x z).trans (hjoint i c z)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- All physical orders on the SAME original shifts, with exactly the
original quadrature constant and `p` carrier derivatives. The input is only
weighted joint smoothness and weighted jets
(`app:ch_waves:eq:background-quadrature`). -/
theorem originalBackgroundError_cNorm_le_of_weighted [CompleteSpace V]
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hweighted : ∀ i c, ContDiff ℝ ∞
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w)) (s : ℕ) (K : Set (Euclidean n))
    (D : ℕ → I → ℝ) (hD : ∀ q ≤ s, ∀ i, 0 ≤ D q i)
    (hjoint : ∀ q ≤ s, ∀ x ∈ K, ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w) (x,z)‖ ≤ D q i)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    cNorm K s (fun y ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (y,z))) ≤
        backgroundQuadratureConstant p B * (∑ q ∈ Finset.range (s+1), ∑ i, D q i) * h^p := by
  have hC := (backgroundQuadratureConstant_pos p hB).le
  calc
    _ ≤ ∑ q ∈ Finset.range (s+1), backgroundQuadratureConstant p B * (∑ i, D q i) * h^p := by
      apply cNorm_le_sum_of_bounds
        (fun q hq ↦ mul_nonneg (mul_nonneg hC (Finset.sum_nonneg (fun i _ ↦ hD q hq i)))
          (pow_nonneg hh.le p))
      intro q hq x hx
      exact originalBackgroundError_physicalJet_le_of_weighted hκc hκ hκint hκ0 hκsupp hp
        hpatch hψc H hweighted q x (D q) (hD q hq) (hjoint q hq x hx) hh hh₁ U hU
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The weighted-only original error profile spends exactly the reserve
`r₀ ≥ s₀+p`, retains every `Cᵢ(p+q)`, and has the original `h*T^(s-s₀)` grade.
No replacement sample, carrier weight, or profile premise is introduced
(`app:ch_mean_pairs:eq:comparison-input`). -/
theorem originalBackgroundError_cNorm_source_profile_of_weighted [CompleteSpace V]
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (C : I → ℕ → ℝ) (hC : ∀ i q, 0 ≤ C i q)
    (s₀ r₀ : ℕ) (hr : s₀+p ≤ r₀)
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hweighted : ∀ i c, ContDiff ℝ ∞
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w)) (s : ℕ) (K : Set (Euclidean n))
    {T : ℝ} (hT : 1 ≤ T)
    (hjoint : ∀ q ≤ s, ∀ x ∈ K, ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w) (x,z)‖ ≤ C i (p+q)*T^(p+q-r₀))
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    cNorm K s (fun y ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (y,z))) ≤
        (backgroundQuadratureConstant p B * (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q))) *
          h * T^(s-s₀) := by
  have hT0 := zero_le_one.trans hT
  have hquad := (backgroundQuadratureConstant_pos p hB).le
  have hsum : (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q)*T^(p+q-r₀)) ≤
      (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q))*T^(s-s₀) := by
    calc
      _ ≤ ∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q)*T^(s-s₀) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqs : q ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
        exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (show p+q-r₀ ≤ s-s₀ by omega)) (hC i (p+q))
      _ = _ := by simp only [Finset.sum_mul]
  have hbudget : 0 ≤ ∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q) :=
    Finset.sum_nonneg fun q _ ↦ Finset.sum_nonneg fun i _ ↦ hC i (p+q)
  calc
    _ ≤ backgroundQuadratureConstant p B *
        (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q)*T^(p+q-r₀)) * h^p :=
      originalBackgroundError_cNorm_le_of_weighted hκc hκ hκint hκ0 hκsupp hp hB hpatch hψc
        H hweighted s K (fun q i ↦ C i (p+q)*T^(p+q-r₀))
        (fun q _ i ↦ mul_nonneg (hC i (p+q)) (pow_nonneg hT0 _)) hjoint hh hh₁ U hU
    _ ≤ backgroundQuadratureConstant p B *
        ((∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q))*T^(s-s₀)) * h^p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hquad) (pow_nonneg hh.le p)
    _ ≤ backgroundQuadratureConstant p B *
        ((∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q))*T^(s-s₀)) * h :=
      mul_le_mul_of_nonneg_left (pow_le_of_le_one hh.le hh₁ (Nat.ne_of_gt hp))
        (mul_nonneg hquad (mul_nonneg hbudget (pow_nonneg hT0 _)))
    _ = _ := by ring

private theorem weightedForcingSobolev_le_physicalCNorm
    {f : Torus n → Euclidean n} (hf : IsSmoothPeriodic f) (s : ℕ) :
    periodicSobolevNorm s f ≤ sobolevPeriodicJetConstant n s * (s+1) *
      cNorm (fundamentalCell n) s (periodicLift f) := by
  apply (periodicSobolevNorm_le_sum_periodicJet_uniform s hf).trans
  calc
    _ ≤ sobolevPeriodicJetConstant n s *
        ∑ _q ∈ Finset.range (s+1), cNorm (fundamentalCell n) s (periodicLift f) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s))
      apply Finset.sum_le_sum
      intro q hq
      exact periodicL2Norm_le_of_bound _ (cNorm_nonneg _ _ _) (fun x ↦
        (norm_periodicJet_le_cNorm hf q x).trans
          (cNorm_mono_order (Nat.le_of_lt_succ (Finset.mem_range.mp hq))))
    _ = _ := by simp [mul_assoc]

/-- Weighted-only counterpart of
`originalBackgroundQuadratureForcing_source_profile`, with EXACTLY the same
source-profile right-hand side and the same original continuum-minus-sample
value. Weighted joint smoothness is sufficient; `hjoint` bounds the actual
`p+q` derivative of `ψᵢ • Hᵢ,c`, not the desired source. The full positive
baseline is untouched. This implication leaves the actual weighted-kernel
producer and its grades explicit (`app:ch_mean_pairs:eq:comparison-input`). -/
theorem weightedOriginalBackgroundQuadratureForcing_source_profile
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (C : I → ℕ → ℝ) (hC : ∀ i q, 0 ≤ C i q)
    (s₀ r₀ : ℕ) (hr : s₀+p ≤ r₀)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hweighted : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ i w.2 • H i c (torusQuotient w.1,w.2)))
    (s : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hjoint : ∀ q ≤ s, ∀ x ∈ fundamentalCell n, ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c (torusQuotient w.1,w.2)) (x,z)‖ ≤
        C i (p+q)*T^(p+q-r₀))
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    residualSobolevSeminorm n s
      (weightedOriginalBackgroundQuadratureForcing hκc hκ p B h ψ hψc U H hweighted) ≤
        (sobolevPeriodicJetConstant n s * (s+1) *
          (backgroundQuadratureConstant p B * (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q)))) *
            h * T^(s-s₀) := by
  let f : Torus n → Euclidean n := fun x ↦ familyBackgroundError p B ψ
    (convolvedBoxWindow κ p) h U (fun i c z ↦ H i c (x,z))
  have hf : IsSmoothPeriodic f :=
    isSmoothPeriodic_originalBackgroundError_of_weighted hκc hκ p B h ψ hψc U H hweighted
  have hpref : 0 ≤ sobolevPeriodicJetConstant n s * (s+1) :=
    mul_nonneg (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s)) (by positivity)
  have hquad := originalBackgroundError_cNorm_source_profile_of_weighted hκc hκ hκint hκ0 hκsupp
    hp hB hpatch hψc C hC s₀ r₀ hr
    (fun i c w ↦ H i c (torusQuotient w.1,w.2)) hweighted s (fundamentalCell n)
    hT hjoint hh hh₁ U hU
  unfold weightedOriginalBackgroundQuadratureForcing
  rw [map_neg_eq_map (residualSobolevSeminorm n s), residualSobolevSeminorm,
    DensityDiscrepancy.densitySobolevSeminorm_eq_norm, DensityDiscrepancy.norm_densitySobolevRealization]
  change periodicSobolevNorm s f ≤ _
  exact (weightedForcingSobolev_le_physicalCNorm hf s).trans
    ((mul_le_mul_of_nonneg_left hquad hpref).trans_eq (by ring))

end JanetCartan.PhysicalMean
