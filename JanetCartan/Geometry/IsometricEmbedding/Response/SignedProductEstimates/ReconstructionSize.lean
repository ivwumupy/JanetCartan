module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.CutRestrictionSize
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Assembly
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported

/-!
# Physical size of the literal ambient reconstruction

The size argument in `app:ch_pairs:eq:pairs-lag-sum-size` uses the complete
oscillatory source and the actual reduced solution, without demodulating by
a Hamilton primary. Applying the existing first-order reconstruction with
zero phase costs exactly one carrier power. The physical Fourier-to-torus
comparison uses the same real field and weak-jet uniqueness, without any
classical Sobolev embedding loss.

The raw normalized reduced response profile is supplied by
`exists_normalized_product_reduced_solver_size_constants`; the complete
source profile is supplied by `exists_signed_modulated_source_sobolev_constants`.
The three literal coefficient profiles are produced on the same history by
`ResponseTransfer.exists_admissible_history_reconstruction_entry_profiles`.
Consumer: the individual physical bounds of `UniformStep.ProductProfiles`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open LocalSobolev Pseudodifferential ResponseTransfer
open UniformStep.Periodization IsometricEmbedding.Reconstruction
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Fourier profiles of a complete complex physical field control the
periodization of its same real part, at the same order
(`app:ch_pairs:eq:pairs-lag-sum-size`). -/
private theorem exists_real_matrix_periodization_constants (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : E → EuclideanSpace ℂ (Fin N))
      (u : PiLp 2 (fun _ : Fin N ↦ L2)),
      (∀ j, u j =ᵐ[volume] fun x ↦ v x j) → MemMatrixFourierSobolev (r : ℝ) u →
      ContDiff ℝ ∞ (fun x ↦ euclideanRealPart (v x)) →
      ∀ b : ℝ, b < 1/2 →
      tsupport (fun x ↦ euclideanRealPart (v x)) ⊆ {x | ∀ i, |x i| ≤ b} →
      periodicSobolevNorm r (vectorPeriodization (fun x ↦ euclideanRealPart (v x))) ≤
        C * matrixFourierSobolevNorm (r : ℝ) u := by
  obtain ⟨C, hC, hconvert⟩ := exists_vector_sobolevExtension_nat n N r
  let A := Real.sqrt (r.factorial : ℝ) *
    Real.sqrt (BallExtension.cartesianEnergyComparisonConstant n r)
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨A*C, mul_nonneg hA hC.le, ?_⟩
  intro v u hrep hu hv b hb hs
  let z := (finiteL2CoordinateIsometry volume).symm u
  have hzcoord : finiteL2CoordinateIsometry volume z = u :=
    (finiteL2CoordinateIsometry volume).apply_symm_apply u
  have hzrep : z =ᵐ[volume] v := (finiteL2CoordinateIsometry_ae_iff volume z v).mpr
    (by simpa only [hzcoord] using hrep)
  have hzmem : MemVectorFourierSobolev (r : ℝ) z := by
    simpa only [MemVectorFourierSobolev, hzcoord] using hu
  let zl : LocalL2 univ (EuclideanSpace ℂ (Fin N)) := ((Lp.memLp z).restrict univ).toLp z
  obtain ⟨e, hefun, _, heNorm⟩ := hconvert z hzmem univ zl
    (MemLp.coeFn_toLp ((Lp.memLp z).restrict univ)).symm
  let er := e.mapCLM (euclideanRealPart (ι := Fin N))
  have her : er.toFun =ᵐ[volume] fun x ↦ euclideanRealPart (v x) := by
    filter_upwards [hzrep] with x hx
    change euclideanRealPart (e.toFun x) = _
    rw [hefun, hx]
  have hclass := Mollification.hasWeakJetOn_of_contDiff volume
    (hv.of_le (show (r : WithTop ℕ∞) ≤ ∞ by simp)) univ
  have hj (j : ℕ) (hj : j ≤ r) :
      er.jet j =ᵐ[volume] iteratedFDeriv ℝ j (fun x ↦ euclideanRealPart (v x)) := by
    simpa only [Measure.restrict_univ] using
      er.weakJet.ae_eq hclass isOpen_univ (ae_restrict_of_ae her) j hj
  have hjmem j (hjr : j ≤ r) :
      MemLp (iteratedFDeriv ℝ j (fun x ↦ euclideanRealPart (v x))) 2 volume :=
    (er.memLp_jet j hjr).ae_eq (hj j hjr)
  have hjnorm : jetL2Norm univ r (fun j ↦ iteratedFDeriv ℝ j
      (fun x ↦ euclideanRealPart (v x))) = er.jetNorm := by
    unfold jetL2Norm SobolevExtension.jetNorm
    simp only [Measure.restrict_univ]
    apply Finset.sum_congr rfl
    intro j hjr
    rw [eLpNorm_congr_ae (hj j (Nat.le_of_lt_succ (Finset.mem_range.mp hjr)))]
  have hernorm : er.jetNorm ≤ e.jetNorm := (e.jetNorm_mapCLM_le euclideanRealPart).trans
    (mul_le_of_le_one_left e.jetNorm_nonneg euclideanRealPart_norm_le)
  have hcart := cartesianJetNorm_le_mul_jetL2Norm univ r
    (fun j ↦ iteratedFDeriv ℝ j (fun x ↦ euclideanRealPart (v x)))
    (fun j hjr ↦ by simpa only [Measure.restrict_univ] using hjmem j hjr)
  have heBound : er.jetNorm ≤ C * matrixFourierSobolevNorm (r : ℝ) u := by
    simpa only [vectorFourierSobolevNorm, hzcoord] using hernorm.trans heNorm
  calc
    _ ≤ Real.sqrt (r.factorial : ℝ) * cartesianJetNorm univ r
        (fun j ↦ iteratedFDeriv ℝ j (fun x ↦ euclideanRealPart (v x))) :=
      periodicSobolevNorm_vectorPeriodization_le hb hs hv r
    _ ≤ A * er.jetNorm := (mul_le_mul_of_nonneg_left hcart (Real.sqrt_nonneg _)).trans_eq
      (by rw [hjnorm]; dsimp only [A]; ring)
    _ ≤ A * (C * matrixFourierSobolevNorm (r : ℝ) u) :=
      mul_le_mul_of_nonneg_left heBound hA
    _ = _ := by ring

/-- The complete physical reconstruction has size `C_r * lam^(r+1)` from
the actual reduced and full-tensor Sobolev profiles
(`app:ch_pairs:eq:pairs-lag-sum-size`). Zero demodulation phase uses the
complete oscillatory inputs themselves; no signed pair is identified with
a Hamilton primary. The same output cutoff is retained. Constants precede
the map, source, solution and carrier, and no accuracy parameter occurs. -/
theorem exists_completedVariation_physical_size_constants
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {b : ℝ} (hb : b < 1/2) (hψbox : tsupport ψ ⊆ {x | ∀ i, |x i| ≤ b})
    (C B : ℕ → ℝ) (hC : ∀ r, 1 ≤ C r) (hB : ∀ r, 0 ≤ B r) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (F : E → Euclidean N) (Ω : Set E), IsOpen Ω → tsupport ψ ⊆ Ω →
      ContDiffOn ℝ ∞ F Ω → IsImmersionOn F Ω → HasFullNormalRankOn F Ω →
      ∀ (g : E → EuclideanSpace ℂ (Fin n)) (a : E → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ g → ContDiff ℝ ∞ a →
      (∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) Ω) →
      ∀ (L lam : ℝ), 1 ≤ L → L ≤ lam →
      (∀ l j r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L^r) →
      ∀ (ug : PiLp 2 (fun _ : Fin n ↦ L2)) (ua : PiLp 2 (fun _ : Fin n × Fin n ↦ L2)),
      (∀ j, ug j =ᵐ[volume] fun x ↦ g x j) →
      (∀ ij, ua ij =ᵐ[volume] fun x ↦ a x ij.1 ij.2) →
      (∀ r : ℕ, MemMatrixFourierSobolev (r : ℝ) ug ∧
        matrixFourierSobolevNorm (r : ℝ) ug ≤ B r * lam^r) →
      (∀ r : ℕ, MemMatrixFourierSobolev (r : ℝ) ua ∧
        matrixFourierSobolevNorm (r : ℝ) ua ≤ B r * lam^r) →
      ∀ r : ℕ, periodicSobolevNorm r
        (cutToTorus ψ (AmbientResponse.completedVariation F
          (fun x ↦ euclideanRealPart (g x)) (ResponseSourceExtension.tensorFieldRealPart a))) ≤
            D r * lam^(r+1) := by
  let ψc : E → ℂ := fun x ↦ (ψ x : ℂ)
  have hψcs : ContDiff ℝ ∞ ψc := Complex.ofRealCLM.contDiff.comp hψ
  have hψcc : HasCompactSupport ψc := hψc.comp_left (g := Complex.ofReal) rfl
  have hbnd (r : ℕ) := (hψcc.iteratedFDeriv r).exists_bound_of_continuous
    (hψcs.continuous_iteratedFDeriv (by simp))
  choose P₀ hP₀ using hbnd
  let P := fun r ↦ max 0 (P₀ r)
  have hP r : 0 ≤ P r := le_max_left _ _
  have hψbound r x : ‖iteratedFDeriv ℝ r ψc x‖ ≤ P r :=
    (hP₀ r x).trans (le_max_right _ _)
  choose Cperiod hCperiod hperiod using fun r ↦
    exists_real_matrix_periodization_constants (n := n) (N := N) r
  let D := fun r ↦ Cperiod r * max 0
    (reconstructionDisplacementConstant n N (max 1 r) P C B)
  have hD r : 0 ≤ D r := mul_nonneg (hCperiod r) (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro F Ω hΩ hsΩ hF himm hrank g a hg ha hV hDer hS L lam hL hLlam
    hVB hDB hSB ug ua hgrep harep hgb hab r
  let k := max 1 r
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hrk : (r : ℝ) ≤ k := by exact_mod_cast (le_max_right 1 r)
  have hC₀ j : 0 ≤ C j := zero_le_one.trans (hC j)
  have hχbound j (_hj : j ≤ k+1) x (_hx : x ∈ Ω) :
      ‖iteratedFDeriv ℝ j (fun _ : E ↦ (1 : ℂ)) x‖ ≤ C j * L^j := by
    cases j with
    | zero => simpa using hC 0
    | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
                exact mul_nonneg (hC₀ _) (pow_nonneg (zero_le_one.trans hL) _)
  have hphase : ∀ i : Fin n, (fun x : E ↦ ((partialDeriv (fun _ : E ↦ (0 : ℝ)) x i : ℝ) : ℂ)) =
      fun _ ↦ 0 := by intro i; funext x; simp [partialDeriv]
  obtain ⟨out, _, houtrep, houtmem, houtbound, _⟩ := completedVariationComplex_graded_envelopes
    k hk (s := (r : ℝ)) (Nat.cast_nonneg _) hrk F hΩ
    (fun _ ↦ 0) (fun _ ↦ 1) ψ g a (differentiable_const 0) hg
    (fun j l ↦ (AmplitudeBound.matrixEntryEvaluation j l).contDiff.comp ha)
    hψcs hψcc
    ((tsupport_comp_subset (g := Complex.ofReal) (by simp) ψ).trans hsΩ)
    contDiffOn_const (fun i ↦ by rw [hphase]; exact contDiffOn_const)
    hV hDer hS P C B hP hC₀ hB (A := 1) (K := lam) (ρ := lam)
    zero_le_one hL hLlam le_rfl
    (fun j _ x _ ↦ (hψbound j x).trans
      (le_mul_of_one_le_right (hP j) (one_le_pow₀ hL)))
    hχbound
    (fun i j _ x _ ↦ by
      rw [hphase]
      cases j with
      | zero => simpa using (mul_nonneg (hC₀ 0) (pow_nonneg (zero_le_one.trans hL) 0))
      | succ j =>
        simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
        exact mul_nonneg (hC₀ _) (pow_nonneg (zero_le_one.trans hL) _))
    (fun l j q _ x hx ↦ hVB l j q x hx)
    (fun l ij q _ x hx ↦ hDB l ij q x hx)
    (fun l ij q _ x hx ↦ hSB l ij q x hx)
    ug ua hgrep harep (hgb _).1 (hab _).1
    (fun p _ ↦ by simpa only [mul_one] using (hgb p).2)
    (fun p _ ↦ by simpa only [mul_one] using (hab p).2)
  let v := fun x ↦ (ψ x : ℂ) • completedVariationComplex F g a x
  have hmod : modulatedWave lam (fun _ : E ↦ 0) g = g := by
    funext x
    simp [modulatedWave, waveCarrier]
  have houtrep' : ∀ l, out l =ᵐ[volume] fun x ↦ v x l := by
    rw [hmod] at houtrep
    simpa only [waveCarrier, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul, Complex.ofReal_one] using houtrep
  have hvreal : (fun x ↦ euclideanRealPart (v x)) = cutField ψ
      (AmbientResponse.completedVariation F (fun x ↦ euclideanRealPart (g x))
        (ResponseSourceExtension.tensorFieldRealPart a)) := by
    funext x
    apply PiLp.ext
    intro l
    have hgRe : (fun x ↦ euclideanRealPart (g x)) =
        fun y ↦ WithLp.toLp 2 (fun j ↦ (g y j).re) := by
      funext y
      apply PiLp.ext
      intro j
      exact euclideanRealPart_apply _ _
    rw [hgRe]
    simpa only [v, cutField, euclideanRealPart_apply, PiLp.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ResponseSourceExtension.tensorFieldRealPart,
      LinearMap.coe_mk, AddHom.coe_mk] using
      congrArg (fun z : ℝ ↦ ψ x * z) (completedVariationComplex_re F a
        (hg.differentiable (by simp) x) l)
  have hvsm : ContDiff ℝ ∞ (fun x ↦ euclideanRealPart (v x)) := by
    rw [hvreal]
    let tensorRe : Matrix (Fin n) (Fin n) ℂ →L[ℝ] MetricTensor n :=
      LinearMap.toContinuousLinearMap
        { toFun := fun H i j ↦ (H i j).re
          map_add' := by intros; ext; simp
          map_smul' := by intro c H; ext i j; simp }
    exact PrimarySourceAdmission.contDiff_cutoff_of_support_subset hψ hΩ
      (AmbientResponse.contDiffOn_completedVariation hΩ hF
        ((euclideanRealPart (ι := Fin n)).contDiff.comp hg).contDiffOn
        (tensorRe.contDiff.comp ha).contDiffOn himm hrank) hsΩ
  have hvsupp : tsupport (fun x ↦ euclideanRealPart (v x)) ⊆ {x | ∀ i, |x i| ≤ b} := by
    rw [hvreal]
    exact (tsupport_cutField_subset _ _).trans hψbox
  have hper := hperiod r v out houtrep' houtmem hvsm b hb hvsupp
  change periodicSobolevNorm r (vectorPeriodization _) ≤ _
  rw [← hvreal]
  apply hper.trans
  have hlam : 0 ≤ lam := (zero_le_one.trans hL).trans hLlam
  calc
    _ ≤ Cperiod r * (reconstructionDisplacementConstant n N k P C B * lam * lam^(r : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_one] using houtbound) (hCperiod r)
    _ ≤ Cperiod r * (max 0 (reconstructionDisplacementConstant n N k P C B) * lam * lam^(r : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hlam) (Real.rpow_nonneg hlam _)) (hCperiod r)
    _ = D r * lam^(r+1) := by
      rw [Real.rpow_natCast, pow_succ]
      dsimp only [D, k]
      ring

end JanetCartan.SignedProductEstimates
