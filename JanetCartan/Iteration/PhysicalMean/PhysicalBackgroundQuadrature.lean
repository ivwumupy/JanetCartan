module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Integration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# All-order physical quadrature on the original sample

Consumer: the actual initial forcing in new:eq:mean-source and
app:ch_mean_pairs:eq:comparison-input. The same original patch weights,
window, shifts, colors, nodes and colored integrals are retained. Physical
derivatives commute with the genuine integral, and each physical jet is a
Banach-valued instance of the deterministic original quadrature theorem.
Joint order p+s costs exactly p carrier derivatives, with no extra physical
Sobolev loss. The joint full corrected Hermitian profiles are produced by
13/24; selecting the one original event is 26, not this deduction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped ContDiff

namespace JanetCartan.PhysicalMean
open SeparatedSampling LatticeQuadrature Sampling.Realization Sampling.BackgroundQuadrature
  Sampling.ColoredNormalComparison Sampling.RetainedBackground
  FiniteChain.Retarded.KernelDecay RawPrimary.AmplitudeGrades

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
private theorem norm_jointPhysicalJet_le {H : Euclidean n × Point → V}
    (hH : ContDiff ℝ ∞ H) (q j : ℕ) (w : Euclidean n × Point) :
    ‖iteratedFDeriv ℝ j (fun p : Euclidean n × Point ↦
      iteratedFDeriv ℝ q (fun x ↦ H (x,p.2)) p.1) w‖ ≤
      ‖iteratedFDeriv ℝ (j+q) H w‖ := by
  induction q generalizing j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Prod.mk.eta, Nat.add_zero] using
      (continuousMultilinearCurryFin0 ℝ (Euclidean n) V).symm.norm_iteratedFDeriv_comp_left H w j |>.le
  | succ q ih =>
    let J : Euclidean n × Point → (Euclidean n [×q]→L[ℝ] V) :=
      fun p ↦ iteratedFDeriv ℝ q (fun x ↦ H (x,p.2)) p.1
    have hJ : ContDiff ℝ ∞ J := contDiff_outputJet hH q
    let L : (Euclidean n →L[ℝ] (Euclidean n [×q]→L[ℝ] V)) ≃ₗᵢ[ℝ]
        (Euclidean n [×(q+1)]→L[ℝ] V) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q+1) ↦ Euclidean n) V).symm
    let B : Euclidean n →L[ℝ] Euclidean n × Point := ContinuousLinearMap.inl ℝ _ _
    have he : (fun p : Euclidean n × Point ↦ iteratedFDeriv ℝ (q+1)
        (fun x ↦ H (x,p.2)) p.1) = L ∘ (fun p ↦ (fderiv ℝ J p).comp B) := by
      funext p
      have hd : fderiv ℝ (fun x ↦ J (x,p.2)) p.1 = (fderiv ℝ J p).comp B :=
        ((hJ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp p.1
          ((hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _))).fderiv
      change L (fderiv ℝ (fun x ↦ J (x,p.2)) p.1) = _
      rw [hd, Function.comp_apply]
    rw [he, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (G := Euclidean n [×(q+1)]→L[ℝ] V) L (fun p ↦ (fderiv ℝ J p).comp B) w j]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (j+1) J w‖ :=
        norm_iteratedFDeriv_restricted_fderiv_le hJ.contDiffAt B
          (ContinuousLinearMap.norm_inl_le_one ..) j
      _ ≤ ‖iteratedFDeriv ℝ ((j+1)+q) H w‖ := ih (j+1)
      _ = _ := by rw [show (j+1)+q = j+(q+1) by omega]

omit [CompleteSpace V] in
private theorem norm_parameterPhysicalJet_le {H : Euclidean n × Point → V}
    (hH : ContDiff ℝ ∞ H) (q p : ℕ) (x : Euclidean n) (z : Point) :
    ‖iteratedFDeriv ℝ p (fun t ↦ iteratedFDeriv ℝ q (fun y ↦ H (y,t)) x) z‖ ≤
      ‖iteratedFDeriv ℝ (p+q) H (x,z)‖ := by
  let J : Euclidean n × Point → (Euclidean n [×q]→L[ℝ] V) :=
    fun w ↦ iteratedFDeriv ℝ q (fun y ↦ H (y,w.2)) w.1
  have hJ : ContDiff ℝ ∞ J := contDiff_outputJet hH q
  let L : Point →L[ℝ] Euclidean n × Point := ContinuousLinearMap.inr ℝ _ _
  let F : Euclidean n × Point → (Euclidean n [×q]→L[ℝ] V) := fun w ↦ J ((x,0)+w)
  have hF : ContDiff ℝ ∞ F := hJ.comp (contDiff_const.add contDiff_id)
  have he : (fun t ↦ iteratedFDeriv ℝ q (fun y ↦ H (y,t)) x) = F ∘ L := by
    funext t
    simp only [F, L, J, Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [he, L.iteratedFDeriv_comp_right hF z (by simp : (p : ℕ∞ω) ≤ ∞)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ p F (L z)) (fun _ : Fin p ↦ L)
  have hb' : ‖(iteratedFDeriv ℝ p F (L z)).compContinuousLinearMap (fun _ : Fin p ↦ L)‖ ≤
      ‖iteratedFDeriv ℝ p F (L z)‖ := by
    apply hb.trans
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ..))
  have heval : ‖iteratedFDeriv ℝ p F (L z)‖ = ‖iteratedFDeriv ℝ p J (x,z)‖ := by
    simp only [F, L, iteratedFDeriv_comp_add_left, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [heval] at hb'
  exact hb'.trans (norm_jointPhysicalJet_le hH q p (x,z))

omit [CompleteSpace V] in
private theorem iteratedFDeriv_weightedCarrierIntegral
    {ρ : Point → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    {H : Euclidean n × Point → V} (hH : ContDiff ℝ ∞ H) (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (fun y ↦ ∫ z, ρ z • H (y,z)) x =
      ∫ z, ρ z • iteratedFDeriv ℝ q (fun y ↦ H (y,z)) x := by
  have hf : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ ρ w.2 • H w) :=
    (hρ.comp contDiff_snd).smul hH
  rw [iteratedFDeriv_integral_commonCarrier (μ := volume) hf hρc
    (fun _ z hz ↦ by simp only [image_eq_zero_of_notMem_tsupport hz, zero_smul]) q x]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ iteratedFDeriv_const_smul_apply' (a := ρ z)
    (f := fun y ↦ H (y,z)) (i := q)
    ((hH.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt

/-- Every physical jet of the literal original sampled-minus-colored-integral
error is the SAME quadrature error of that jet. The original weights and all
sample colors are unchanged, and compact smooth domination is derived
internally (`app:ch_waves:eq:background-quadrature`). -/
theorem iteratedFDeriv_originalBackgroundError
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hH : ∀ i c, ContDiff ℝ ∞ (H i c)) (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (fun y ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (y,z))) x =
      familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
        (fun i c z ↦ iteratedFDeriv ℝ q (fun y ↦ H i c (y,z)) x) := by
  classical
  let window := convolvedBoxWindow κ p
  let mask := coloredBlockMask p (integerCube (blockCutoff p B h)) window h
  have hslice (i) (c) (z : Point) : ContDiff ℝ ∞ (fun y ↦ H i c (y,z)) :=
    (hH i c).comp (contDiff_id.prodMk contDiff_const)
  have hsample (i) : ContDiff ℝ ∞ (fun y ↦ ∑ a ∈ samples p B (ψ i) window h (U i),
      weight (ψ i) window h (U i) a • H i (color p a.1) (y,node h (U i) a)) :=
    ContDiff.sum fun a _ ↦ (hslice i (color p a.1) (node h (U i) a)).const_smul _
  have hmask (c) : ContDiff ℝ ∞ (mask c) := contDiff_coloredBlockMask hκc hκ p _ h c
  have hint (i) (c) : ContDiff ℝ ∞ (fun y ↦ ∫ z, mask c z • (ψ i z • H i c (y,z))) := by
    simpa only [smul_smul] using contDiff_weightedCarrierIntegral
      ((hmask c).mul (hψ i)) (hψc i).mul_left (hH i c)
  have hdint (i) (c) : iteratedFDeriv ℝ q
      (fun y ↦ ∫ z, mask c z • (ψ i z • H i c (y,z))) x =
      ∫ z, mask c z • (ψ i z • iteratedFDeriv ℝ q (fun y ↦ H i c (y,z)) x) := by
    simpa only [smul_smul] using iteratedFDeriv_weightedCarrierIntegral
      ((hmask c).mul (hψ i)) (hψc i).mul_left (hH i c) q x
  have hsumint (i) : ContDiff ℝ ∞ (fun y ↦ ∑ c, ∫ z, mask c z • (ψ i z • H i c (y,z))) :=
    ContDiff.sum fun c _ ↦ hint i c
  unfold familyBackgroundError
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ ((hsample i).sub (hsumint i)).of_le (by simp) |>.contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ q ((fun y ↦ ∑ a ∈ samples p B (ψ i) window h (U i),
    weight (ψ i) window h (U i) a • H i (color p a.1) (y,node h (U i) a)) -
    (fun y ↦ ∑ c, ∫ z, mask c z • (ψ i z • H i c (y,z)))) x = _
  rw [iteratedFDeriv_sub_apply ((hsample i).of_le (by simp)).contDiffAt
    ((hsumint i).of_le (by simp)).contDiffAt]
  congr 1
  · rw [iteratedFDeriv_fun_sum_apply (fun a _ ↦
      ((hslice i (color p a.1) (node h (U i) a)).const_smul _).of_le (by simp) |>.contDiffAt)]
    apply Finset.sum_congr rfl
    intro a _
    exact iteratedFDeriv_const_smul_apply'
      ((hslice i (color p a.1) (node h (U i) a)).of_le (by simp)).contDiffAt
  · rw [iteratedFDeriv_fun_sum_apply (fun c _ ↦ (hint i c).of_le (by simp) |>.contDiffAt)]
    exact Finset.sum_congr rfl (fun c _ ↦ hdint i c)

/-- The original deterministic quadrature gains `h^p` at each physical
order. Its only quantitative input is the actual joint `p+q` jet of the
weighted FULL kernel; parameter-to-Banach regularity and derivative estimates
are proved from those joints, not assumed (`app:ch_mean_pairs:eq:comparison-input`). -/
theorem originalBackgroundError_physicalJet_le
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hH : ∀ i c, ContDiff ℝ ∞ (H i c)) (q : ℕ) (x : Euclidean n)
    (D : I → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hjoint : ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w) (x,z)‖ ≤ D i)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    ‖iteratedFDeriv ℝ q (fun y ↦ familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U
      (fun i c z ↦ H i c (y,z))) x‖ ≤
        backgroundQuadratureConstant p B * (∑ i, D i) * h^p := by
  rw [iteratedFDeriv_originalBackgroundError hκc hκ p B h ψ hψ hψc U H hH]
  apply norm_familyBackgroundError_le hκc hκ hκint hκ0 hκsupp hp hpatch
    (fun i c z ↦ iteratedFDeriv ℝ q (fun y ↦ H i c (y,z)) x) _ D hD _ hh hh₁ U hU
  · intro i c
    exact ((hψ i).smul ((contDiff_outputJet (hH i c) q).comp
      (contDiff_const.prodMk contDiff_id))).of_le (by simp)
  · intro i c z
    have hw : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c w) :=
      ((hψ i).comp contDiff_snd).smul (hH i c)
    have he : (fun t ↦ iteratedFDeriv ℝ q (fun y ↦ ψ i t • H i c (y,t)) x) =
        (fun t ↦ ψ i t • iteratedFDeriv ℝ q (fun y ↦ H i c (y,t)) x) := by
      funext t
      exact iteratedFDeriv_const_smul_apply' (a := ψ i t) (f := fun y ↦ H i c (y,t))
        (((hH i c).comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt
    have hb := norm_parameterPhysicalJet_le hw q p x z
    rw [he] at hb
    exact hb.trans (hjoint i c z)

/-- All physical orders are estimated on the SAME original shifts. The
constant has only fixed-patch sums and physical derivative orders, never
sample or frequency-band cardinality. Exactly `p` carrier derivatives are
spent; no additional physical Sobolev reserve is used
(`app:ch_waves:eq:background-quadrature`). -/
theorem originalBackgroundError_cNorm_le
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hH : ∀ i c, ContDiff ℝ ∞ (H i c)) (s : ℕ) (K : Set (Euclidean n))
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
      exact originalBackgroundError_physicalJet_le hκc hκ hκint hκ0 hκsupp hp hpatch hψ hψc
        H hH q x (D q) (hD q hq) (hjoint q hq x hx) hh hh₁ U hU
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- A joint reserve `r₀ ≥ s₀+p` pays exactly the carrier quadrature order.
The original error has the faithful all-high grade `C_s*h*T^(s-s₀)` on the
SAME sample, with its constant fixed before H, T, h and U. In the actual
application H is the FULL measured corrected positive Hermitian kernel;
13/24 produce its joint grades with their own fixed reconstruction reserve
(`app:ch_mean_pairs:eq:comparison-input`). -/
theorem originalBackgroundError_cNorm_source_profile
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
    (C : I → ℕ → ℝ) (hC : ∀ i q, 0 ≤ C i q)
    (s₀ r₀ : ℕ) (hr : s₀+p ≤ r₀)
    (H : I → (Fin 3 → Fin (p+1)) → Euclidean n × Point → V)
    (hH : ∀ i c, ContDiff ℝ ∞ (H i c)) (s : ℕ) (K : Set (Euclidean n))
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
      originalBackgroundError_cNorm_le hκc hκ hκint hκ0 hκsupp hp hB hpatch hψ hψc
        H hH s K (fun q i ↦ C i (p+q)*T^(p+q-r₀))
        (fun q _ i ↦ mul_nonneg (hC i (p+q)) (pow_nonneg hT0 _)) hjoint hh hh₁ U hU
    _ ≤ backgroundQuadratureConstant p B *
        ((∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q))*T^(s-s₀)) * h^p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hquad) (pow_nonneg hh.le p)
    _ ≤ backgroundQuadratureConstant p B *
        ((∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q))*T^(s-s₀)) * h :=
      mul_le_mul_of_nonneg_left (pow_le_of_le_one hh.le hh₁ (Nat.ne_of_gt hp))
        (mul_nonneg hquad (mul_nonneg hbudget (pow_nonneg hT0 _)))
    _ = _ := by ring

end JanetCartan.PhysicalMean
