module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.TensorResponse
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSources
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Fourier
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Representative
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms

/-!
# Source norms for the same fixed smooth inverse

For `app:ch_response:prop:response-ambient`, compare the original Lebesgue
classical-test norm to physical jets using the proved Fourier comparison and
local Sobolev embedding. Both tensor quadratures, after the unchanged stress
projection and source cutoff, obey the resulting restriction-space estimate.
The consumer is the finite source bound for the literal fixed ambient response;
no source measure, inverse, cutoff, or smooth representative is reselected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory Metric
open scoped ContDiff
namespace JanetCartan.CorrectedAtoms
open RetardedSobolev.Spaces LocalSobolev Pseudodifferential
open FourierIntegral FiniteChain.Graph.KernelLimits
open ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
open RegularSector.FiniteAssembly.CoefficientNorms

/-- Classical physical source norms are controlled by the original Lebesgue
test-jet norm, with a fixed derivative reserve. Consumer: finite source bounds
for the SAME fixed inverse (`app:ch_response:prop:response-ambient`). -/
private theorem exists_physicalTest_ballCNorm_le_ofTest {d : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Test d, ∀ x : Euclidean (d + 1), ∀ R : ℝ, 0 < R →
      cNorm (closedBall x R) m (fun y ↦ f.val (e.symm y)) ≤
        C * ‖ofTest (m + (d + 2)) volume f‖ := by
  let s := m + (d + 2)
  obtain ⟨Cf, hCf, hfourier⟩ := exists_vector_sobolevExtension_nat (d + 1) 1 s
  obtain ⟨Ce, hCe, hemb⟩ := exists_cNorm_le_restrictionSobolevNorm (F := ℂ) (d + 1) m
  let D : EuclideanSpace ℂ (Fin 1) →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 ↦ ℂ) 0).restrictScalars ℝ
  refine ⟨Ce * ‖D‖ * Cf * fourierComparisonConstant e s, by
    have := fourierComparisonConstant_pos e s
    positivity, ?_⟩
  intro f x R hR
  let w := physicalZeroJet e he s (ofTest s volume f)
  let u : Lp (EuclideanSpace ℂ (Fin 1)) 2 (volume : Measure (Euclidean (d + 1))) :=
    (finiteL2CoordinateIsometry volume).symm (WithLp.toLp 2 (fun _ : Fin 1 ↦ w))
  have hcoord (i : Fin 1) : finiteL2CoordinateIsometry volume u i = w := by
    simp only [u, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply]
  have hw := physicalZeroJet_fourier_bound e he s (ofTest s volume f)
  have hu : MemVectorFourierSobolev (s : ℝ) u := by
    intro i
    rw [hcoord]
    exact hw.1
  have hnorm : vectorFourierSobolevNorm (s : ℝ) u ≤
      fourierComparisonConstant e s * ‖ofTest s volume f‖ := by
    apply (matrixFourierSobolevNorm_le_sum (s : ℝ) (finiteL2CoordinateIsometry volume u)).trans
    simpa only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_one,
      one_smul] using hw.2
  let V := ball x (R + 1)
  let v : LocalL2 V (EuclideanSpace ℂ (Fin 1)) := ((Lp.memLp u).restrict V).toLp u
  obtain ⟨ext, hext, _hextL2, hextNorm⟩ := hfourier u hu V v
    (MemLp.coeFn_toLp _).symm
  let extC := ext.mapCLM D
  have hrep : extC.toFun =ᵐ[volume] fun y ↦ f.val (e.symm y) := by
    have h := finiteL2Coordinates_apply_ae volume u (0 : Fin 1)
    change finiteL2CoordinateIsometry volume u 0 =ᵐ[volume] fun y ↦ u y 0 at h
    rw [hcoord] at h
    have hψ := physicalZeroJet_ofTest_ae e he s f
    filter_upwards [h, hψ] with y hy hψy
    change D (ext.toFun y) = _
    rw [hext]
    exact hy.symm.trans hψy
  have hrepV : extC.toFun =ᵐ[volume.restrict V] fun y ↦ f.val (e.symm y) :=
    ae_restrict_of_ae hrep
  have hlocal : (fun y ↦ f.val (e.symm y)) =ᵐ[volume.restrict V] D.compLp v :=
    hrepV.symm.trans extC.restrict_eq
  have hcost := hemb x R (R + 1) hR (by linarith)
    (fun y ↦ f.val (e.symm y)) (f.property.1.comp e.symm.contDiff).contDiffOn
    _ hlocal (by simpa [s, Nat.add_assoc] using (show MemRestrictionSobolev V s (D.compLp v) from ⟨extC⟩))
  have horder : m + (d + 1) + 1 = s := by dsimp [s]; omega
  rw [horder] at hcost
  have hn := (restrictionSobolevNorm_le extC).trans (ext.jetNorm_mapCLM_le D)
  exact hcost.trans ((mul_le_mul_of_nonneg_left
    (hn.trans (mul_le_mul_of_nonneg_left
      (hextNorm.trans (mul_le_mul_of_nonneg_left hnorm hCf.le)) (norm_nonneg D))) (zero_le_one.trans hCe)).trans_eq
        (by ring))

/-- All physical jets through a fixed order are controlled by the original
Lebesgue source norm. Constants precede the test and observation point
(`app:ch_response:prop:response-ambient`). -/
theorem exists_physicalTest_jet_le_ofTest {d : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Test d, ∀ j ≤ m, ∀ x : Euclidean (d + 1),
      ‖iteratedFDeriv ℝ j (fun y ↦ f.val (e.symm y)) x‖ ≤
        C * ‖ofTest (m + (d + 2)) volume f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_physicalTest_ballCNorm_le_ofTest e he m
  refine ⟨C, hC, fun f j hj x ↦ ?_⟩
  exact (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall x 1)
    ((f.property.1.comp e.symm.contDiff).of_le (by simp))
    (mem_closedBall_self (by norm_num)) hj).trans (hbound f x 1 (by norm_num))

/-- The same physical source comparison controls the actual `cNorm` on every
observation set, with one derivative budget. Consumer: scalar components of
`cutoffStressSmoothSource` (`app:ch_response:prop:response-ambient`). -/
theorem exists_physicalTest_cNorm_le_ofTest {d : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Test d, ∀ K : Set (Euclidean (d + 1)),
      cNorm K m (fun y ↦ f.val (e.symm y)) ≤
        C * ‖ofTest (m + (d + 2)) volume f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_physicalTest_jet_le_ofTest e he m
  refine ⟨(m + 1 : ℝ) * C, by positivity, fun f K ↦ ?_⟩
  have hh := cNorm_le_sum_of_bounds (s := K) (r := m)
    (fun _ _ ↦ mul_nonneg hC (norm_nonneg (ofTest (m + (d + 2)) volume f)))
    (fun j hj x _ ↦ hbound f j hj x)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc] using hh

/-- A fixed smooth physical coefficient maps the original supported scalar
tests into the inverse's restriction scale (`app:ch_response:prop:response-ambient`).
This internal estimate is applied to the literal stress-source coefficients. -/
private theorem exists_supportedCoefficient_restriction_bound {d : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    {S U : Set (Euclidean (d + 1))} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (A : Euclidean (d + 1) → ℂ →L[ℝ] Euclidean (d + 1))
    (hA : ContDiffOn ℝ ∞ A U) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : supportedTests (e ⁻¹' S),
      let w := fun x ↦ A x (f.val.val (e.symm x))
      ContDiff ℝ ∞ w → ∀ hw : MemLp w 2 volume, ∀ W : Set (Euclidean (d + 1)),
        restrictionSobolevNorm W m ((hw.restrict W).toLp w) ≤
          C * ‖ofTest (m + (d + 2)) volume f.val‖ := by
  obtain ⟨C₀, hC₀, hscalar⟩ := exists_physicalTest_jet_le_ofTest e he m
  let B := ContinuousLinearMap.id ℝ (ℂ →L[ℝ] Euclidean (d + 1))
  let C₁ := ‖B‖ * (2 : ℝ) ^ m * cNorm S m A * C₀
  let vS := indicatorConstLp (μ := (volume : Measure (Euclidean (d + 1)))) 2
    hS.measurableSet hS.measure_lt_top.ne (1 : ℝ)
  have hAn : 0 ≤ cNorm S m A := cNorm_nonneg _ _ _
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  refine ⟨(m + 1 : ℝ) * C₁ * ‖vS‖, by positivity, ?_⟩
  intro f w hcont hw W
  have hsupport : tsupport w ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    by_contra hxS
    apply hx
    have hf0 : f.val.val (e.symm x) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
      hxS (by simpa using f.property h)
    change A x (f.val.val (e.symm x)) = 0
    rw [hf0, map_zero]
  have hcompact : HasCompactSupport w := hS.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hjetmem (j : ℕ) : MemLp (iteratedFDeriv ℝ j w) 2 volume :=
    (hcont.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (hcompact.iteratedFDeriv j)
  have hjet (j : ℕ) (hj : j ≤ m) (x : Euclidean (d + 1)) (hx : x ∈ S) :
      ‖iteratedFDeriv ℝ j w x‖ ≤ C₁ * ‖ofTest (m + (d + 2)) volume f.val‖ := by
    have hf := (f.val.property.1.comp e.symm.contDiff).contDiffOn (s := U)
    have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hA hf hU.uniqueDiffOn (hSU hx)
      (by simp : (j : ℕ∞ω) ≤ ∞)
    simp only [iteratedFDerivWithin_of_isOpen _ hU (hSU hx)] at hb
    change ‖iteratedFDeriv ℝ j w x‖ ≤ _ at hb
    have hcoef (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i A x‖ ≤ cNorm S m A :=
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
        (fun y hy ↦ (hA.contDiffAt (hU.mem_nhds (hSU hy))).of_le (by simp)) hx hi
    have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = (2 : ℝ) ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    apply hb.trans
    calc
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * cNorm S m A *
            (C₀ * ‖ofTest (m + (d + 2)) volume f.val‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcoef i (hij.trans hj)) (Nat.cast_nonneg _))
          (hscalar f.val (j-i) ((Nat.sub_le _ _).trans hj) x) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      _ = ‖B‖ * (2 : ℝ) ^ j * cNorm S m A * C₀ *
          ‖ofTest (m + (d + 2)) volume f.val‖ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
        ring
      _ ≤ C₁ * ‖ofTest (m + (d + 2)) volume f.val‖ := by
        dsimp only [C₁]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hC₀
        apply mul_le_mul_of_nonneg_right _ hAn
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (norm_nonneg B)
  have hL2 (j : ℕ) (hj : j ≤ m) :
      (eLpNorm (iteratedFDeriv ℝ j w) 2 volume).toReal ≤
        (C₁ * ‖ofTest (m + (d + 2)) volume f.val‖) * ‖vS‖ := by
    rw [← Lp.norm_toLp _ (hjetmem j)]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hjetmem j).coeFn_toLp,
      indicatorConstLp_coeFn (μ := (volume : Measure (Euclidean (d + 1)))) (p := 2)
        (hs := hS.measurableSet) (hμs := hS.measure_lt_top.ne) (c := (1 : ℝ))] with x hx hv
    rw [hx, hv]
    by_cases hxS : x ∈ S
    · simpa only [indicator_of_mem hxS, norm_one, mul_one] using hjet j hj x hxS
    · rw [indicator_of_notMem hxS, norm_zero, mul_zero]
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hxS (hsupport
        (tsupport_iteratedFDeriv_subset j h))), norm_zero]
  let ext : SobolevExtension W m ((hw.restrict W).toLp w) := {
    toFun := w
    jet := fun j ↦ iteratedFDeriv ℝ j w
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hcont.of_le (by simp)) univ
    memLp_fun := hw
    memLp_jet := fun j _ ↦ hjetmem j
    restrict_eq := (MemLp.coeFn_toLp _).symm }
  apply (restrictionSobolevNorm_le ext).trans
  have hh := Finset.sum_le_sum (s := Finset.range (m + 1))
    (fun j hj ↦ hL2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  change (∑ j ∈ Finset.range (m + 1),
    (eLpNorm (iteratedFDeriv ℝ j w) 2 volume).toReal) ≤ _
  exact hh.trans_eq (by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring)

open PrimarySourceAdmission ResponseSourceExtension ResponseSmoothParameters AmbientResponse
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

/-- Both original tensor quadratures, after the unchanged stress projection
and source cutoff, obey a finite source bound in the fixed inverse's actual
restriction norm. The constant precedes the scalar test and inverse domain
(`app:ch_response:prop:response-ambient`, `app:ch_regular:eq:inverse-tame`). -/
theorem exists_cutoffStress_tensorComponent_restriction_bounds {d : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (η : Euclidean (d + 1) → ℝ) {S U : Set (Euclidean (d + 1))}
    (hS : IsCompact S) (hU : IsOpen U) (hQ : ∀ k, ContDiffOn ℝ ∞ (fun x ↦ Q x k) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U) (i j : Fin (d + 1)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : supportedTests (e ⁻¹' S),
      let hr : compactSmoothSources S := ⟨tensorFieldRealPart (tensorTestSource e i j v.val),
        (tensorTestSource_quadratures_mem e hS i j v).1⟩
      let hi : compactSmoothSources S := ⟨tensorFieldImagPart (tensorTestSource e i j v.val),
        (tensorTestSource_quadratures_mem e hS i j v).2⟩
      ∀ W : Set (Euclidean (d + 1)),
      let sr := (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU hr : LocalL2 W (Euclidean (d + 1)))
      let si := (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU hi : LocalL2 W (Euclidean (d + 1)))
      restrictionSobolevNorm W m sr + restrictionSobolevNorm W m si ≤
          C * ‖ofTest (m + (d + 2)) volume v.val‖ ∧
        ‖sr‖ + ‖si‖ ≤ C * ‖ofTest (m + (d + 2)) volume v.val‖ := by
  let c : Euclidean (d + 1) → Euclidean (d + 1) :=
    fun x ↦ WithLp.toLp 2 (fun k ↦ η x * ((1 / 2 : ℝ) * Q x k i j))
  let entry : MetricTensor (d + 1) →L[ℝ] ℝ :=
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) ↦ Fin (d + 1) → ℝ) i)).toContinuousLinearMap
  have hc : ContDiffOn ℝ ∞ c U := by
    apply PiLp.contDiff_toLp.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro k
    exact hη.contDiffOn.mul ((entry.contDiff.comp_contDiffOn (hQ k)).const_smul (1 / 2 : ℝ))
  let part : Bool → ℂ →L[ℝ] ℝ := fun b ↦ if b then Complex.imCLM else Complex.reCLM
  let A (b : Bool) : Euclidean (d + 1) → ℂ →L[ℝ] Euclidean (d + 1) :=
    fun x ↦ (part b).smulRight (c x)
  have hA (b : Bool) : ContDiffOn ℝ ∞ (A b) U := contDiffOn_const.smulRight hc
  choose C hC hbound using fun b ↦ exists_supportedCoefficient_restriction_bound e he
    hS hU hSU (A b) (hA b) m
  let src (v : supportedTests (e ⁻¹' S)) (b : Bool) : compactSmoothSources S :=
    if b then ⟨tensorFieldImagPart (tensorTestSource e i j v.val),
      (tensorTestSource_quadratures_mem e hS i j v).2⟩ else
      ⟨tensorFieldRealPart (tensorTestSource e i j v.val),
      (tensorTestSource_quadratures_mem e hS i j v).1⟩
  have hfield (v : supportedTests (e ⁻¹' S)) (b : Bool) :
      euclideanCutoffStressSource Q η (src v b) = fun x ↦ A b x (v.val.val (e.symm x)) := by
    ext x k
    cases b <;>
      simp [src, A, part, c, euclideanCutoffStressSource, cutoffSource, stressSource,
        tensorPairing, tensorFieldImagPart, tensorFieldRealPart, tensorTestSource,
        Matrix.single, apply_ite, ite_and, mul_assoc, mul_comm, mul_left_comm]
  have hb (v : supportedTests (e ⁻¹' S)) (b : Bool) (W : Set (Euclidean (d + 1))) :
      restrictionSobolevNorm W m
        (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU (src v b) : LocalL2 W (Euclidean (d + 1))) ≤
        C b * ‖ofTest (m + (d + 2)) volume v.val‖ := by
    have hsmooth := contDiff_euclideanCutoffStressSource Q η hU hQ hη hSU (src v b)
    have hmem := memLp_euclideanCutoffStressSource Q η hU hQ hη hSU (src v b)
    rw [hfield] at hsmooth hmem
    have h := hbound b v hsmooth hmem W
    convert h using 1
    congr 1
    exact MemLp.toLp_congr
      ((memLp_euclideanCutoffStressSource Q η hU hQ hη hSU (src v b)).restrict W)
      (hmem.restrict W) (Filter.Eventually.of_forall (congrFun (hfield v b)))
  refine ⟨C false + C true, add_nonneg (hC false) (hC true), ?_⟩
  intro v hr hi W sr si
  have hsum : restrictionSobolevNorm W m sr + restrictionSobolevNorm W m si ≤
      (C false + C true) * ‖ofTest (m + (d + 2)) volume v.val‖ := by
    simpa only [sr, si, hr, hi, src, Bool.false_eq_true, ite_false, ite_true, add_mul] using
      add_le_add (hb v false W) (hb v true W)
  refine ⟨hsum, ?_⟩
  exact (add_le_add
    (norm_le_restrictionSobolevNorm
      (memRestrictionSobolev_euclideanCutoffStressSource Q η hU hQ hη hSU hr m))
    (norm_le_restrictionSobolevNorm
      (memRestrictionSobolev_euclideanCutoffStressSource Q η hU hQ hη hSU hi m))).trans hsum

/-- The unprojected tensor quadratures also have homogeneous source bounds.
The original entry, physical chart and Lebesgue norm are unchanged. Consumer:
the normal-source term of `app:ch_response:eq:response-full-map`. -/
theorem exists_tensorTestSource_cNorm_le_ofTest {d : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (i j : Fin (d + 1)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Test d, ∀ K : Set (Euclidean (d + 1)),
      cNorm K m (tensorFieldRealPart (tensorTestSource e i j v)) +
        cNorm K m (tensorFieldImagPart (tensorTestSource e i j v)) ≤
          C * ‖ofTest (m + (d + 2)) volume v‖ := by
  obtain ⟨C₀, hC₀, hscalar⟩ := exists_physicalTest_jet_le_ofTest e he m
  let A (b : Bool) : ℂ →L[ℝ] MetricTensor (d + 1) :=
    ((Matrix.singleLinearMap ℝ i j : ℝ →ₗ[ℝ] MetricTensor (d + 1)).toContinuousLinearMap).comp
      (if b then Complex.imCLM else Complex.reCLM)
  have hbound (b : Bool) (v : Test d) (K : Set (Euclidean (d + 1))) :
      cNorm K m (fun x ↦ A b (v.val (e.symm x))) ≤
        ((m+1 : ℝ) * ‖A b‖ * C₀) * ‖ofTest (m + (d + 2)) volume v‖ := by
    have hh := cNorm_le_sum_of_bounds (s := K) (r := m)
      (fun _ _ ↦ mul_nonneg (mul_nonneg (norm_nonneg (A b)) hC₀)
        (norm_nonneg (ofTest (m + (d + 2)) volume v)))
      (fun k hk x _ ↦ ((A b).norm_iteratedFDeriv_comp_left
        (v.property.1.comp e.symm.contDiff).contDiffAt (by simp : (k : ℕ∞ω) ≤ ∞)).trans
        ((mul_le_mul_of_nonneg_left (hscalar v k hk x) (norm_nonneg (A b))).trans_eq
          (mul_assoc _ _ _).symm))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, mul_assoc, Function.comp_def] using hh
  refine ⟨(m+1 : ℝ) * ‖A false‖ * C₀ + (m+1 : ℝ) * ‖A true‖ * C₀,
    by positivity, fun v K ↦ ?_⟩
  have hr : tensorFieldRealPart (tensorTestSource e i j v) =
      fun x ↦ A false (v.val (e.symm x)) := by
    ext x a b
    by_cases ha : i = a <;> by_cases hb : j = b <;>
      simp [tensorFieldRealPart, tensorTestSource, A, Matrix.single, ha, hb]
  have hi : tensorFieldImagPart (tensorTestSource e i j v) =
      fun x ↦ A true (v.val (e.symm x)) := by
    ext x a b
    by_cases ha : i = a <;> by_cases hb : j = b <;>
      simp [tensorFieldImagPart, tensorTestSource, A, Matrix.single, ha, hb]
  rw [hr, hi, add_mul]
  exact add_le_add (hbound false v K) (hbound true v K)


end JanetCartan.CorrectedAtoms
