module

public import JanetCartan.Analysis.Sobolev.Local.Cutoff
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# The actual cutoff zero extension in the vector Fourier scale

The finite direct restriction estimates need a whole-space input whose high
norm is controlled by the restriction norm and whose L² norm is controlled
by the original local L² datum. Cutting off a genuine weak extension gives
exactly the cutoff of the zero extension. In particular its L² bound does
not involve the chosen extension's jet norm. Consumers: the positive transfer
in `RestrictionBounds.Positive`, `sector-theorem-solution` and
`sector-theorem-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential FourierIntegral.LowBounds ArbitraryAccuracy
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Genuine complex vector weak extensions have Fourier regularity with a
constant fixed before the domain and extension. This is the input conversion
for `sector-theorem-solution` and `sector-theorem-residual`. -/
theorem vectorFourierSobolev_extension_bounds (n q s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Euclidean n))
      (u : LocalL2 U (EuclideanSpace ℂ (Fin q))) (e : SobolevExtension U s u),
      MemVectorFourierSobolev (s : ℝ) e.toL2 ∧
        vectorFourierSobolevNorm (s : ℝ) e.toL2 ≤ C * e.jetNorm := by
  obtain ⟨C, hC, hscalar⟩ := scalarFourierSobolev_extension_bounds n s
  let proj (j : Fin q) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) j).restrictScalars ℝ
  have hp (j : Fin q) : ‖proj j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖v j‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using PiLp.norm_apply_le v j
  refine ⟨((q : ℝ)+1)*C, by positivity, ?_⟩
  intro U u e
  have he (j : Fin q) : (e.mapCLM (proj j)).toL2 =
      finiteL2CoordinateIsometry volume e.toL2 j := by
    rw [e.toL2_mapCLM]
    apply Lp.ext
    filter_upwards [(proj j).coeFn_compLp e.toL2,
      finiteL2Coordinates_apply_ae volume e.toL2 j] with y hy hz
    exact hy.trans hz.symm
  have hs (j : Fin q) := hscalar U ((proj j).compLp u) (e.mapCLM (proj j))
  simp_rw [he] at hs
  refine ⟨fun j ↦ (hs j).1, ?_⟩
  have hj (j : Fin q) : fourierSobolevNorm (s : ℝ)
      (finiteL2CoordinateIsometry volume e.toL2 j) ≤ C * e.jetNorm :=
    (hs j).2.trans (mul_le_mul_of_nonneg_left
      ((e.jetNorm_mapCLM_le (proj j)).trans
        (mul_le_of_le_one_left e.jetNorm_nonneg (hp j))) hC.le)
  calc
    _ ≤ ∑ j, fourierSobolevNorm (s : ℝ)
        (finiteL2CoordinateIsometry volume e.toL2 j) :=
      matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ _j : Fin q, C * e.jetNorm := Finset.sum_le_sum fun j _ ↦ hj j
    _ ≤ (((q : ℝ)+1)*C)*e.jetNorm := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith [mul_nonneg hC.le e.jetNorm_nonneg]

/-- A supported physical cutoff of any genuine extension equals the cutoff
of the original local datum's zero extension. This identity preserves the
low-data term of `sector-theorem-residual`; the extension is not assumed to
have any support. -/
theorem sourceCutMultiplier_extension_eq_zeroExtend
    {U : Set E} (hU : MeasurableSet U) {s : ℕ} {u : LocalL2 U F}
    (e : SobolevExtension U s u) (χ : E → ℝ) (hχ : Continuous χ)
    (hb : ∀ y, ‖χ y‖ ≤ 1) (hs : tsupport χ ⊆ U) :
    sourceCutMultiplier χ hχ hb e.toL2 =
      sourceCutMultiplier χ hχ hb (SmallSupport.zeroExtend hU u) := by
  apply Lp.ext
  have he := (ae_restrict_iff' hU).mp e.toL2_restrict
  filter_upwards [sourceCutMultiplier_coeFn χ hχ hb e.toL2,
    sourceCutMultiplier_coeFn χ hχ hb (SmallSupport.zeroExtend hU u),
    SmallSupport.zeroExtend_coeFn hU u, he] with y hy hz hu he
  rw [hy, hz, hu]
  by_cases hyU : y ∈ U
  · rw [indicator_of_mem hyU, he hyU]
  · have hzero : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hyU (hs h))
    simp only [hzero, Complex.ofReal_zero, zero_smul]

/-- The literal cutoff zero extension has L² norm at most the original local
norm, independent of all higher weak jets (`sector-theorem-residual`). -/
theorem norm_sourceCutMultiplier_zeroExtend_le
    {U : Set E} (hU : MeasurableSet U) (χ : E → ℝ) (hχ : Continuous χ)
    (hb : ∀ y, ‖χ y‖ ≤ 1) (u : LocalL2 U F) :
    ‖sourceCutMultiplier χ hχ hb (SmallSupport.zeroExtend hU u)‖ ≤ ‖u‖ := by
  simpa only [one_mul, LinearIsometry.norm_map] using
    (sourceCutMultiplier χ hχ hb).le_of_opNorm_le
      (norm_sourceCutMultiplier_le χ hχ hb) (SmallSupport.zeroExtend hU u)

/-- A fixed smooth compact physical cutoff sends a genuine restriction Hˢ
input to whole-space Fourier Hˢ. Its constant precedes the domain and input;
the simultaneous L² estimate above remains one. This supplies the cutoff
input to `sector-theorem-solution` and `sector-theorem-residual`. -/
theorem exists_sourceCut_zeroExtension_fourier_bound
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hb : ∀ y, ‖χ y‖ ≤ 1) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set E) (hU : MeasurableSet U),
      tsupport χ ⊆ U → ∀ (u : LocalL2 U F), MemRestrictionSobolev U s u →
      let z := sourceCutMultiplier χ hχ.continuous hb (SmallSupport.zeroExtend hU u)
      MemVectorFourierSobolev (s : ℝ) z ∧
        vectorFourierSobolevNorm (s : ℝ) z ≤ C * restrictionSobolevNorm U s u := by
  obtain ⟨A, hA, hfourier⟩ := vectorFourierSobolev_extension_bounds n q s
  obtain ⟨B, hB, hcut⟩ := exists_cutoffAllJet_bound («F» := F) χ hχ hc s
  refine ⟨1+A*B, by nlinarith, ?_⟩
  intro U hU hs u hu z
  have hfor (e : SobolevExtension U s u) :
      MemVectorFourierSobolev (s : ℝ) z ∧
        vectorFourierSobolevNorm (s : ℝ) z ≤ (1+A*B)*e.jetNorm := by
    let v : LocalL2 univ F := ((Lp.memLp z).restrict univ).toLp z
    have heq : (fun y ↦ χ y • e.toFun y) =ᵐ[volume] z := by
      have hid := sourceCutMultiplier_extension_eq_zeroExtend hU e χ hχ.continuous hb hs
      have hm := sourceCutMultiplier_coeFn χ hχ.continuous hb e.toL2
      rw [hid] at hm
      filter_upwards [hm, e.toL2_coeFn] with y hy he
      rw [he] at hy
      rw [hy]
      ext j
      simp only [PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
    let ec : SobolevExtension univ s v :=
      { toFun := fun y ↦ χ y • e.toFun y
        jet := cutoffAllJet χ hχ hc e.jet
        weakJet := hasWeakJetOn_cutoffAllJet e.weakJet e.memLp_jet hχ hc
        memLp_fun := memLp_bounded_smul e.memLp_fun hχ.continuous hb
        memLp_jet := fun _ hj ↦ memLp_cutoffAllJet e.memLp_jet hχ hc hj
        restrict_eq := (show (fun y ↦ χ y • e.toFun y) =ᵐ[volume.restrict univ] z from
          ae_restrict_of_ae heq).trans
          (MemLp.coeFn_toLp ((Lp.memLp z).restrict univ)).symm }
    have hec : ec.toL2 = z := Lp.ext (ec.toL2_coeFn.trans heq)
    obtain ⟨hm, hn⟩ := hfourier univ v ec
    rw [hec] at hm hn
    refine ⟨hm, hn.trans ?_⟩
    have hjet : ec.jetNorm ≤ B*e.jetNorm := hcut e.jet e.memLp_jet
    calc
      A*ec.jetNorm ≤ A*(B*e.jetNorm) := mul_le_mul_of_nonneg_left hjet hA.le
      _ ≤ (1+A*B)*e.jetNorm := by nlinarith [e.jetNorm_nonneg]
  exact ⟨(hfor hu.some).1,
    le_mul_restrictionSobolevNorm_of_extensions hu (by positivity) (fun e ↦ (hfor e).2)⟩

end JanetCartan.RegularSector.FiniteAssembly
