module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.MaskedJets

/-!
# Tame physical action with the original coefficients

The full physical action is a fixed smooth function of the coefficient values
and the first jet of the symbol. Compact-range tame composition keeps all
high norms additive and costs exactly one derivative. The zeroth-order
coefficient and the derivative of the entire symbol are retained.
Consumer: `directPDOSymbols` index three, in
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
open FullPhaseCharts.InverseEstimates NullTransport.AmplitudeTame
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

/-- The complete physical action has a single-high bound from original
zeroth-order coefficient bounds and a first-order bound of its input.
For the algebraic residual the input is the frequency-weighted full source–
inverse product; its first-order bound is produced by
`exists_conicAlgebraicSymbol_weighted_cNorm_bounds` from original `C¹ Q`.
Thus this lemma does not require an inverse seminorm premise in the final
construction. The displayed derivative reserve is one, at every order.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_physicalSymbolApply_slice_cNorm_bound
    (i : Fin (d + 1)) (x : E) {R : ℝ} (hR : 0 < R) (xQ : E) (RQ : ℝ)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x R) (closedBall xQ RQ))
    (M N : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set E), IsOpen Ω → closedBall xQ RQ ⊆ Ω →
        ∀ (Q : E → Coeff) (B : E → Mat) (f : E → CMat),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω → ContDiff ℝ ∞ f →
          cNorm (closedBall xQ RQ) 0 Q ≤ M → cNorm (closedBall xQ RQ) 0 B ≤ M →
          cNorm (closedBall x R) 1 f ≤ N → ∀ m,
          cNorm (closedBall x R) m
            (fun y ↦ physicalSymbolApply
              (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
              (fun y ↦ (zeroth i B y).map Complex.ofReal) (fun y _ ↦ f y) y 0) ≤
            C m * (1 + cNorm (closedBall xQ RQ) (m + 1) Q +
              cNorm (closedBall xQ RQ) (m + 1) B + cNorm (closedBall x R) (m + 1) f) := by
  let J := Coeff × (Mat × ((E →L[ℝ] CMat) × CMat))
  let G : J → CMat := fun p ↦
    (∑ a, (pencil p.1 (physicalCoordinates i (EuclideanSpace.single a 1))).map Complex.ofReal *
      p.2.2.1 (EuclideanSpace.single a 1)) + p.2.1.map Complex.ofReal * p.2.2.2
  have hG : ContDiff ℝ ∞ G := by
    apply ContDiff.add
    · apply ContDiff.sum
      intro a _
      exact (contDiff_matrix_map_ofReal.comp
        (contDiff_pencil.comp (contDiff_fst.prodMk contDiff_const))).mul
        (contDiff_snd.snd.fst.clm_apply contDiff_const)
    · exact (contDiff_matrix_map_ofReal.comp contDiff_snd.fst).mul contDiff_snd.snd.snd
  let T := closedBall (0 : J) (1 + max 0 M + max 0 N)
  choose A hA hcomp using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn x hR
      (isCompact_closedBall (0 : J) (1 + max 0 M + max 0 N)) (le_refl m)
      (g := G) (fun _ _ ↦ hG.contDiffAt.of_le (by simp))
  let L := (physicalCoordinates i).toContinuousLinearMap
  refine ⟨fun m ↦ A m * (3 + linearNormCost L m),
    fun m ↦ mul_pos (hA m) (by linarith [linearNormCost_pos L m]), ?_⟩
  intro Ω hΩ hKQ Q B f hQ hB hf hQM hBM hfN m
  let K := closedBall x R
  let KQ := closedBall xQ RQ
  let U := L ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage L.continuous
  have hKU : K ⊆ U := fun y hy ↦ hKQ (hphysical hy)
  have hQL : ContDiffOn ℝ ∞ (Q ∘ L) U := hQ.comp L.contDiff.contDiffOn (fun _ hy ↦ hy)
  have hBL : ContDiffOn ℝ ∞ (B ∘ L) U := hB.comp L.contDiff.contDiffOn (fun _ hy ↦ hy)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  let v : E → J := fun y ↦ (Q (L y), (B (L y), (fderiv ℝ f y, f y)))
  have hv : ContDiffOn ℝ ∞ v U := hQL.prodMk (hBL.prodMk (hdf.prodMk hf).contDiffOn)
  have hmap : MapsTo v K T := by
    intro y hy
    have hq : ‖Q (L y)‖ ≤ M := by
      have he := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := 0)
          (isCompact_closedBall xQ RQ)
          (fun z hz ↦ (hQ.contDiffAt (hΩ.mem_nhds (hKQ hz))).of_le (by simp))
          (hphysical hy) (le_refl 0)
      rw [norm_iteratedFDeriv_zero] at he
      exact he.trans hQM
    have hb : ‖B (L y)‖ ≤ M := by
      have he := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := 0)
          (isCompact_closedBall xQ RQ)
          (fun z hz ↦ (hB.contDiffAt (hΩ.mem_nhds (hKQ hz))).of_le (by simp))
          (hphysical hy) (le_refl 0)
      rw [norm_iteratedFDeriv_zero] at he
      exact he.trans hBM
    have hfv : ‖f y‖ ≤ N := by
      have he := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := 1)
        (isCompact_closedBall x R)
        (fun _ _ ↦ hf.contDiffAt.of_le (by simp)) hy (show 0 ≤ 1 by omega)
      rw [norm_iteratedFDeriv_zero] at he
      exact he.trans hfN
    have hfd : ‖fderiv ℝ f y‖ ≤ N := by
      have he := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x R)
        (fun _ _ ↦ hdf.contDiffAt.of_le (show (0 : ℕ∞ω) ≤ ∞ by simp)) hy (le_refl 0)
      rw [norm_iteratedFDeriv_zero] at he
      exact he.trans ((GeometricProfile.cNorm_fderiv_le K 0 f).trans hfN)
    simp only [T, mem_closedBall, dist_zero_right, v]
    have hM := le_max_right 0 M
    have hN := le_max_right 0 N
    have hM0 := le_max_left 0 M
    have hN0 := le_max_left 0 N
    exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))
  have hvnorm : cNorm K m v ≤
      linearNormCost L m * cNorm KQ m Q + linearNormCost L m * cNorm KQ m B +
        2 * cNorm K (m + 1) f := by
    have hpair := cNorm_prodMk_le_on K (isCompact_closedBall x R) m
      (fun y hy ↦ (hQL.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp))
      (fun y hy ↦ ((hBL.prodMk (hdf.prodMk hf).contDiffOn).contDiffAt
        (hU.mem_nhds (hKU hy))).of_le (by simp))
    have hpair' := cNorm_prodMk_le_on K (isCompact_closedBall x R) m
      (fun y hy ↦ (hBL.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp))
      (fun _ _ ↦ (hdf.prodMk hf).contDiffAt.of_le (by simp))
    have hjet := cNorm_prodMk_le_on K (isCompact_closedBall x R) m
      (fun _ _ ↦ hdf.contDiffAt.of_le (by simp)) (fun _ _ ↦ hf.contDiffAt.of_le (by simp))
    have hq := cNorm_comp_linear_le L (isCompact_closedBall xQ RQ) hΩ hKQ hQ hphysical m
    have hb := cNorm_comp_linear_le L (isCompact_closedBall xQ RQ) hΩ hKQ hB hphysical m
    have hd := GeometricProfile.cNorm_fderiv_le K m f
    have hfmono := cNorm_mono_order (s := K) (f := f) (Nat.le_succ m)
    dsimp only [K, KQ, v, Function.comp_def] at hpair hpair' hjet hq hb hd hfmono ⊢
    linarith
  have hbound := hcomp m U hU hKU v hv hmap
  change cNorm K m (fun y ↦ physicalSymbolApply
    (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth i B y).map Complex.ofReal) (fun y _ ↦ f y) y 0) ≤
      A m * (1 + cNorm K m v) at hbound
  apply hbound.trans
  have hq := cNorm_mono_order (s := KQ) (f := Q) (Nat.le_succ m)
  have hb := cNorm_mono_order (s := KQ) (f := B) (Nat.le_succ m)
  have hL := (linearNormCost_pos L m).le
  have hvnorm' : cNorm K m v ≤
      linearNormCost L m * (cNorm KQ (m + 1) Q + cNorm KQ (m + 1) B) +
        2 * cNorm K (m + 1) f := by
    have hq' := mul_le_mul_of_nonneg_left hq hL
    have hb' := mul_le_mul_of_nonneg_left hb hL
    linarith
  have hmajor : 1 + cNorm K m v ≤ (3 + linearNormCost L m) *
      (1 + cNorm KQ (m + 1) Q + cNorm KQ (m + 1) B + cNorm K (m + 1) f) := by
    nlinarith [cNorm_nonneg KQ (m + 1) Q, cNorm_nonneg KQ (m + 1) B,
      cNorm_nonneg K (m + 1) f, mul_nonneg hL (cNorm_nonneg K (m + 1) f)]
  exact (mul_le_mul_of_nonneg_left hmajor (hA m).le).trans_eq (by ring)

/-- Frequency weights commute with the full physical action, including the
zeroth-order coefficient. No derivative of the physical symbol is omitted.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalSymbolApply_real_frequency_smul
    (A : E → Fin (d + 1) → CMat) (B : E → CMat)
    (c : E → E → CMat) (w : E → ℝ) (x η : E) :
    physicalSymbolApply A B (fun y ξ ↦ w ξ • c y ξ) x η =
      w η • physicalSymbolApply A B c x η := by
  have hd a : partialDeriv (fun y ↦ w η • c y η) x a =
      w η • partialDeriv (fun y ↦ c y η) x a := by
    exact congrArg (fun L : E →L[ℝ] CMat ↦ L (EuclideanSpace.single a 1))
      (congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun y ↦ c y η) (w η)) x)
  simp only [physicalSymbolApply, hd, Matrix.mul_smul, smul_add, Finset.smul_sum]

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
