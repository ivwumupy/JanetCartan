module

public import JanetCartan.Iteration.PhysicalMean.PhysicalBackgroundQuadrature
public import JanetCartan.Iteration.PhysicalMean.LinearProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Hilbert

/-!
# Actual same-sample quadrature source and Sobolev profiles

Consumer: the quadrature part of `r_init` in new:eq:mean-source. Its sign is
CONTINUUM MINUS SAMPLE. The literal original colored integrals, weights,
nodes and shifts are retained, and smoothness and all-high Sobolev profiles
are proved from genuine joint full-kernel jets. No replacement sample,
initializer or continuum cancellation is selected here. The remaining
continuum/leading/corrected comparison and positive-background cancellation
must still be instantiated from the same original 13/24/26 tuple.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily SeparatedSampling LatticeQuadrature
  Sampling.Realization Sampling.BackgroundQuadrature Sampling.ColoredNormalComparison
  Sampling.RetainedBackground

/-- The original sampled-minus-colored-integral field is genuinely smooth
periodic. This derives the smooth representative required by the source
iteration from its original joint kernel (`new:eq:mean-source`). -/
theorem isSmoothPeriodic_originalBackgroundError
    {n : ℕ} {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ H i c (torusQuotient w.1,w.2))) :
    IsSmoothPeriodic (fun x ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (x,z))) := by
  classical
  let window := convolvedBoxWindow κ p
  let mask := coloredBlockMask p (integerCube (blockCutoff p B h)) window h
  have hslice (i) (c) (z : Point) : ContDiff ℝ ∞ (fun y ↦ H i c (torusQuotient y,z)) :=
    (hH i c).comp (contDiff_id.prodMk contDiff_const)
  have hmask (c) : ContDiff ℝ ∞ (mask c) := contDiff_coloredBlockMask hκc hκ p _ h c
  have hint (i) (c) : ContDiff ℝ ∞ (fun y ↦ ∫ z, mask c z • (ψ i z • H i c (torusQuotient y,z))) := by
    simpa only [smul_smul] using contDiff_weightedCarrierIntegral
      ((hmask c).mul (hψ i)) (hψc i).mul_left (hH i c)
  have hsmooth : ContDiff ℝ ∞ (periodicLift (fun x ↦ familyBackgroundError p B ψ window h U
      (fun i c z ↦ H i c (x,z)))) := by
    change ContDiff ℝ ∞ (fun y ↦ ∑ i, ((∑ a ∈ samples p B (ψ i) window h (U i),
      weight (ψ i) window h (U i) a • H i (color p a.1) (torusQuotient y,node h (U i) a)) -
        ∑ c, ∫ z, mask c z • (ψ i z • H i c (torusQuotient y,z))))
    exact ContDiff.sum fun i _ ↦
      (ContDiff.sum fun a _ ↦ (hslice i (color p a.1) (node h (U i) a)).const_smul _).sub
        (ContDiff.sum fun c _ ↦ hint i c)
  have hquot : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hquot.isQuotientMap.continuous_iff.mpr hsmooth.continuous, hsmooth⟩

/-- The actual quadrature contribution to `r_init`, with sign CONTINUUM
MINUS SAMPLE. It uses the literal full measured kernel, original smooth
representatives and original quadrature; it is not an assumed forcing source
(`new:eq:mean-source`). -/
def originalBackgroundQuadratureForcing
    {n : ℕ} {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ H i c (torusQuotient w.1,w.2))) :
    SmoothResidual n :=
  -⟨fun x _ ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U (fun i c z ↦ H i c (x,z)),
    fun _ ↦ isSmoothPeriodic_originalBackgroundError hκc hκ p B h ψ hψ hψc U H hH⟩

/-- The source has exactly the original continuum-minus-sample value
(`new:eq:mean-source`). -/
theorem originalBackgroundQuadratureForcing_apply
    {n : ℕ} {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ H i c (torusQuotient w.1,w.2)))
    (x : Torus n) :
    (originalBackgroundQuadratureForcing hκc hκ p B h ψ hψ hψc U H hH).val x () =
      -familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U (fun i c z ↦ H i c (x,z)) := rfl

/-- The same-order Sobolev comparison costs no extra physical derivatives.
Only a fixed order/dimension constant enters (`new:eq:source-bound`). -/
private theorem forcingSobolev_le_physicalCNorm {n : ℕ}
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

/-- The constructed quadrature source has the faithful `h*T^(s-s₀)` profile
in the SAME source Sobolev seminorm used by the actual fixed-cutoff Picard
iteration. The `p` carrier reserve is paid explicitly; source smoothness,
Banach quadrature and Sobolev transfer are all proved internally. Original
full-kernel joint grades remain the explicit 13/24 input, not a desired source
bound (`app:ch_mean_pairs:eq:comparison-input`). -/
theorem originalBackgroundQuadratureForcing_source_profile
    {n : ℕ} {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
    (C : I → ℕ → ℝ) (hC : ∀ i q, 0 ≤ C i q)
    (s₀ r₀ : ℕ) (hr : s₀+p ≤ r₀)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ H i c (torusQuotient w.1,w.2)))
    (s : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hjoint : ∀ q ≤ s, ∀ x ∈ fundamentalCell n, ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c (torusQuotient w.1,w.2)) (x,z)‖ ≤
        C i (p+q)*T^(p+q-r₀))
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    residualSobolevSeminorm n s
      (originalBackgroundQuadratureForcing hκc hκ p B h ψ hψ hψc U H hH) ≤
        (sobolevPeriodicJetConstant n s * (s+1) *
          (backgroundQuadratureConstant p B * (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q)))) *
            h * T^(s-s₀) := by
  let f : Torus n → Euclidean n := fun x ↦ familyBackgroundError p B ψ
    (convolvedBoxWindow κ p) h U (fun i c z ↦ H i c (x,z))
  have hf : IsSmoothPeriodic f := isSmoothPeriodic_originalBackgroundError hκc hκ p B h ψ hψ hψc U H hH
  have hpref : 0 ≤ sobolevPeriodicJetConstant n s * (s+1) :=
    mul_nonneg (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s)) (by positivity)
  have hquad := originalBackgroundError_cNorm_source_profile hκc hκ hκint hκ0 hκsupp hp hB
    hpatch hψ hψc C hC s₀ r₀ hr
    (fun i c w ↦ H i c (torusQuotient w.1,w.2)) hH s (fundamentalCell n)
    hT hjoint hh hh₁ U hU
  unfold originalBackgroundQuadratureForcing
  rw [map_neg_eq_map (residualSobolevSeminorm n s), residualSobolevSeminorm,
    DensityDiscrepancy.densitySobolevSeminorm_eq_norm, DensityDiscrepancy.norm_densitySobolevRealization]
  change periodicSobolevNorm s f ≤ _
  exact (forcingSobolev_le_physicalCNorm hf s).trans
    ((mul_le_mul_of_nonneg_left hquad hpref).trans_eq (by ring))

/-- The fixed complementary derivative budget for one joint product. Only
physical/carrier derivative orders occur, never sample or annular counts
(`app:ch_mean_pairs:eq:comparison-input`). -/
def backgroundJointBilinearBudget (A B : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q+1), (q.choose j : ℝ)*A j*B (q-j)

private theorem backgroundJointBilinearBudget_nonneg (A B : ℕ → ℝ)
    (hA : ∀ q, 0 ≤ A q) (hB : ∀ q, 0 ≤ B q) (q : ℕ) :
    0 ≤ backgroundJointBilinearBudget A B q :=
  Finset.sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB _)

private theorem backgroundJoint_bilinear_profile
    {X E F G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (f : X → E) (g : X → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (A B : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q) (hB : ∀ q, 0 ≤ B q)
    (r₀ q : ℕ) {T : ℝ} (hT : 1 ≤ T) (w : X)
    (hfj : ∀ j ≤ q, ‖iteratedFDeriv ℝ j f w‖ ≤ A j*T^(j-r₀))
    (hgj : ∀ j ≤ q, ‖iteratedFDeriv ℝ j g w‖ ≤ B j*T^(j-r₀)) :
    ‖iteratedFDeriv ℝ q (fun z ↦ L (f z) (g z)) w‖ ≤
      backgroundJointBilinearBudget A B q*T^(q-r₀) := by
  have hT0 := zero_le_one.trans hT
  have hb := L.norm_iteratedFDeriv_le_of_bilinear (hf.of_le (by simp : (q : ℕ∞ω) ≤ ∞))
    (hg.of_le (by simp : (q : ℕ∞ω) ≤ ∞)) w (le_refl (q : ℕ∞ω))
  apply hb.trans
  calc
    _ ≤ 1 * (∑ j ∈ Finset.range (q+1), (q.choose j : ℝ)*‖iteratedFDeriv ℝ j f w‖*
        ‖iteratedFDeriv ℝ (q-j) g w‖) :=
      mul_le_mul_of_nonneg_right hL (Finset.sum_nonneg fun _ _ ↦ by positivity)
    _ = _ := one_mul _
    _ ≤ backgroundJointBilinearBudget A B q*T^(q-r₀) := by
      unfold backgroundJointBilinearBudget
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        _ ≤ (q.choose j : ℝ)*(A j*T^(j-r₀))*(B (q-j)*T^(q-j-r₀)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hfj j hjq) (Nat.cast_nonneg _))
            (hgj (q-j) (Nat.sub_le _ _)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA j) (pow_nonneg hT0 _)))
        _ = ((q.choose j : ℝ)*A j*B (q-j))*(T^(j-r₀)*T^(q-j-r₀)) := by ring
        _ ≤ ((q.choose j : ℝ)*A j*B (q-j))*T^(q-r₀) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB _))
          rw [← pow_add]
          exact pow_le_pow_right₀ hT (show (j-r₀)+(q-j-r₀) ≤ q-r₀ by omega)

/-- Actual full measured Hermitian joint jets, with ALL terms of the supplied
full corrected derivative B retained before squaring. The three primitive
profiles are the fixed patch weight, SAME preparation measurement and SAME
full positive corrected B. This proves the kernel-jet input of the original
quadrature source theorem, retaining the exact reserve and factor-one self
normalization (`app:ch_mean_pairs:eq:comparison-input`). -/
theorem norm_jointFullMeasuredHermitian_kernel_source_profile
    {n N : ℕ} (φ : Euclidean n × Point → ℝ)
    (M : Euclidean n × Point → MetricTensor n →L[ℝ] Euclidean n)
    (B : Euclidean n × Point → Matrix (Fin N) (Fin n) ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hM : ContDiff ℝ ∞ M) (hB : ContDiff ℝ ∞ B)
    (Cφ CM CB : ℕ → ℝ) (hCφ : ∀ j, 0 ≤ Cφ j) (hCM : ∀ j, 0 ≤ CM j) (hCB : ∀ j, 0 ≤ CB j)
    (r₀ q : ℕ) {T : ℝ} (hT : 1 ≤ T) (w : Euclidean n × Point)
    (hφj : ∀ j ≤ q, ‖iteratedFDeriv ℝ j φ w‖ ≤ Cφ j)
    (hMj : ∀ j ≤ q, ‖iteratedFDeriv ℝ j M w‖ ≤ CM j*T^(j-r₀))
    (hBj : ∀ j ≤ q, ‖iteratedFDeriv ℝ j B w‖ ≤ CB j*T^(j-r₀)) :
    ‖iteratedFDeriv ℝ q (fun z ↦ φ z • M z (hermitianTensor (B z))) w‖ ≤
      backgroundJointBilinearBudget Cφ
        (backgroundJointBilinearBudget CM (backgroundJointBilinearBudget CB CB)) q*T^(q-r₀) := by
  let HB : Euclidean n × Point → MetricTensor n := fun z ↦ hermitianTensor (B z)
  have hHB : ContDiff ℝ ∞ HB := by
    simpa only [HB, Function.comp_def, hermitianContinuousBilinear_apply, mixedHermitianTensor_self] using
      (hermitianContinuousBilinear (m := Fin N) (n := Fin n)).isBoundedBilinearMap.contDiff.comp
        (hB.prodMk hB)
  have hHBj (j : ℕ) (hj : j ≤ q) : ‖iteratedFDeriv ℝ j HB w‖ ≤
      backgroundJointBilinearBudget CB CB j*T^(j-r₀) := by
    simpa only [HB, hermitianContinuousBilinear_apply, mixedHermitianTensor_self] using
      backgroundJoint_bilinear_profile (hermitianContinuousBilinear (m := Fin N) (n := Fin n))
        norm_hermitianContinuousBilinear_le B B hB hB CB CB hCB hCB r₀ j hT w
        (fun k hk ↦ hBj k (hk.trans hj)) (fun k hk ↦ hBj k (hk.trans hj))
  let MH : Euclidean n × Point → Euclidean n := fun z ↦ M z (HB z)
  have hMH : ContDiff ℝ ∞ MH := hM.clm_apply hHB
  have hMHj (j : ℕ) (hj : j ≤ q) : ‖iteratedFDeriv ℝ j MH w‖ ≤
      backgroundJointBilinearBudget CM (backgroundJointBilinearBudget CB CB) j*T^(j-r₀) :=
    backgroundJoint_bilinear_profile (ContinuousLinearMap.id ℝ (MetricTensor n →L[ℝ] Euclidean n))
      ContinuousLinearMap.norm_id_le M HB hM hHB CM (backgroundJointBilinearBudget CB CB) hCM
      (backgroundJointBilinearBudget_nonneg CB CB hCB hCB) r₀ j hT w
      (fun k hk ↦ hMj k (hk.trans hj)) (fun k hk ↦ hHBj k (hk.trans hj))
  apply backgroundJoint_bilinear_profile (ContinuousLinearMap.lsmul ℝ ℝ (E := Euclidean n))
    ContinuousLinearMap.opNorm_lsmul_le φ MH hφ hMH Cφ
    (backgroundJointBilinearBudget CM (backgroundJointBilinearBudget CB CB)) hCφ
    (backgroundJointBilinearBudget_nonneg CM (backgroundJointBilinearBudget CB CB) hCM
      (backgroundJointBilinearBudget_nonneg CB CB hCB hCB)) r₀ q hT w _ hMHj
  intro j hj
  exact (hφj j hj).trans (le_mul_of_one_le_right (hCφ j) (one_le_pow₀ hT))

end JanetCartan.PhysicalMean
