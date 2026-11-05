module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.SourceSobolevBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.CompletionSourceBounds

/-!
# The finite source bound for the same fixed ambient response

Apply the classical smooth-solver estimate already exported by
`FixedDomainInverse.DirectSmooth` to the original cutoff stress sources.
The checked physical test comparison and canonical completion bound give
exactly the component estimate required by `Response.SmoothParameters` and
canonical Fourier integration. Both quadratures use one supplied solver and
one ambient extension; the original source and observation cutoffs remain.

The direct inverse must still be selected on the initialized stationary family.
The finite bound proved here is qualitative in that family's coefficients;
it does not replace the frequency-sensitive envelopes of `Response.Transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory Metric Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open PrimarySourceAdmission AmbientResponse ResponseSourceExtension ResponseSmoothParameters
open FixedDomainInverse LocalSobolev RetardedSobolev.Spaces
open FourierIntegral FiniteChain.Graph.KernelLimits

/-- Both literal real quadratures bound the complex response jet; no second
response is selected (`app:ch_response:prop:response-ambient`). -/
private theorem norm_iteratedFDeriv_complexifyResponse_le {n N : ℕ}
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : ContDiff ℝ ∞ (B (tensorFieldRealPart h)))
    (hi : ContDiff ℝ ∞ (B (tensorFieldImagPart h))) (q : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ q (complexifyResponse B h) x‖ ≤
      ‖iteratedFDeriv ℝ q (B (tensorFieldRealPart h)) x‖ +
        ‖iteratedFDeriv ℝ q (B (tensorFieldImagPart h)) x‖ := by
  let E : Euclidean N →L[ℝ] EuclideanSpace ℂ (Fin N) := euclideanComplexInclusion
  have hEn : ‖E‖ ≤ 1 := euclideanComplexInclusion_norm_le
  have hR := E.contDiff.comp hr
  have hI := E.contDiff.comp hi
  have hEr : ‖iteratedFDeriv ℝ q (E ∘ B (tensorFieldRealPart h)) x‖ ≤
      ‖iteratedFDeriv ℝ q (B (tensorFieldRealPart h)) x‖ :=
    (E.norm_iteratedFDeriv_comp_left hr.contDiffAt (by simp : (q : ℕ∞ω) ≤ ∞)).trans
      ((mul_le_mul_of_nonneg_right hEn
        (norm_nonneg (iteratedFDeriv ℝ q (B (tensorFieldRealPart h)) x))).trans_eq (one_mul _))
  have hEi : ‖iteratedFDeriv ℝ q (E ∘ B (tensorFieldImagPart h)) x‖ ≤
      ‖iteratedFDeriv ℝ q (B (tensorFieldImagPart h)) x‖ :=
    (E.norm_iteratedFDeriv_comp_left hi.contDiffAt (by simp : (q : ℕ∞ω) ≤ ∞)).trans
      ((mul_le_mul_of_nonneg_right hEn
        (norm_nonneg (iteratedFDeriv ℝ q (B (tensorFieldImagPart h)) x))).trans_eq (one_mul _))
  change ‖iteratedFDeriv ℝ q ((E ∘ B (tensorFieldRealPart h)) +
    (fun y ↦ Complex.I • (E ∘ B (tensorFieldImagPart h)) y)) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hR.of_le (by simp)).contDiffAt
    ((hI.const_smul Complex.I).of_le (by simp)).contDiffAt]
  apply (norm_add_le _ _).trans
  change ‖iteratedFDeriv ℝ q (E ∘ B (tensorFieldRealPart h)) x‖ +
    ‖iteratedFDeriv ℝ q (Complex.I • (E ∘ B (tensorFieldImagPart h))) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hI.of_le (by simp)).contDiffAt,
    norm_smul, Complex.norm_I, one_mul]
  exact add_le_add hEr hEi

/-- The accepted direct solver's classical estimate supplies the precise
component bound consumed by `contDiffOn_fullPrimaryResponse_of_tame` and
`fullPrimaryWave_response_integral`. Source admission, the source-norm
comparison, canonical completion, and both real quadratures are proved here.
The supplied solver bound is the literal output of
`FixedDomainInverse.exists_finite_direct_smooth_fixed_inverse` at the SAME
radius, cutoff and restriction norm (`app:ch_regular:eq:inverse-tame`,
`app:ch_response:prop:response-ambient`). -/
theorem exists_fixedSmoothSolver_tensorComponent_bounds {d N : ℕ}
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (F : Euclidean (d + 1) → Euclidean N)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (η : Euclidean (d + 1) → ℝ)
    {S U W core chart : Set (Euclidean (d + 1))}
    (hS : IsCompact S) (hU : IsOpen U)
    (hQ : ∀ k, ContDiffOn ℝ ∞ (fun x ↦ Q x k) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean (d + 1)) →ₗ[ℝ]
      (Euclidean (d + 1) → Euclidean (d + 1)))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
    (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
    (x : Euclidean (d + 1)) (Rout : ℝ)
    (hcore : closedBall x Rout ⊆ core)
    (D a : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m) (ha : ∀ m, 0 ≤ a m) (β : ℕ)
    (hbound : ∀ (h : smoothSource W (Euclidean (d + 1))) (m : ℕ),
      cNorm (closedBall x Rout) m (solver h) ≤ D m *
        (restrictionSobolevNorm W (m + (d + 2)) (h : LocalL2 W (Euclidean (d + 1))) +
          (1 + a (m + (d + 2) + β)) * ‖(h : LocalL2 W (Euclidean (d + 1)))‖)) :
    let B := fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
    ∀ i j : Fin (d + 1), ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : supportedTests (e ⁻¹' S), ∀ y ∈ closedBall x Rout,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e S B i j v) y‖ ≤
          C * ‖ofTest s volume v.val‖ := by
  dsimp only
  have hobs : closedBall x Rout ⊆ chart := by
    intro y hy
    apply Ξ.support_chart
    apply subset_tsupport
    have h1 : y ∈ {z | Ξ.toFun z = 1} := interior_subset (Ξ.plateau (hcore hy))
    change Ξ.toFun y ≠ 0
    rw [h1]
    exact one_ne_zero
  let K := closedBall x Rout
  let B := fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
  intro i j q
  let m := q + 1 + (d + 2)
  let s := m + (d + 2)
  obtain ⟨Cs, hCs, hsource⟩ := exists_cutoffStress_tensorComponent_restriction_bounds
    e he Q η hS hU hQ hη hSU i j m
  obtain ⟨Ct, hCt, htensor⟩ := exists_tensorTestSource_cNorm_le_ofTest e he i j m
  obtain ⟨Cg, hCg, hcompletion⟩ := exists_completedVariation_jet_bound
    (isCompact_closedBall x Rout) hchart hobs hF hi hrank q
  let C := Cg * (D (q+1) * (2 + a (m+β)) * Cs + Ct)
  have ham := ha (m+β)
  have hDq := hD (q+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨s, C, hC, ?_⟩
  intro v y hy
  let hr : compactSmoothSources S := ⟨tensorFieldRealPart (tensorTestSource e i j v.val),
    (tensorTestSource_quadratures_mem e hS i j v).1⟩
  let hi' : compactSmoothSources S := ⟨tensorFieldImagPart (tensorTestSource e i j v.val),
    (tensorTestSource_quadratures_mem e hS i j v).2⟩
  let sr := cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU hr
  let si := cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU hi'
  let Z := ‖ofTest s volume v.val‖
  have hs := hsource v W
  have hsn : restrictionSobolevNorm W m (sr : LocalL2 W (Euclidean (d+1))) +
      restrictionSobolevNorm W m (si : LocalL2 W (Euclidean (d+1))) ≤ Cs * Z := hs.1
  have hsl : ‖(sr : LocalL2 W (Euclidean (d+1)))‖ +
      ‖(si : LocalL2 W (Euclidean (d+1)))‖ ≤ Cs * Z := hs.2
  have hsol : cNorm K (q+1) (solver sr) + cNorm K (q+1) (solver si) ≤
      (D (q+1) * (2 + a (m+β)) * Cs) * Z := by
    have hb := add_le_add (hbound sr (q+1)) (hbound si (q+1))
    change _ ≤ D (q+1) * (_ + (1 + a (m+β)) * _) +
      D (q+1) * (_ + (1 + a (m+β)) * _) at hb
    apply hb.trans
    calc
      _ = D (q+1) * ((restrictionSobolevNorm W m (sr : LocalL2 W (Euclidean (d+1))) +
          restrictionSobolevNorm W m (si : LocalL2 W (Euclidean (d+1)))) +
          (1 + a (m+β)) * (‖(sr : LocalL2 W (Euclidean (d+1)))‖ +
            ‖(si : LocalL2 W (Euclidean (d+1)))‖)) := by ring
      _ ≤ D (q+1) * (Cs * Z + (1 + a (m+β)) * (Cs * Z)) :=
        mul_le_mul_of_nonneg_left (add_le_add hsn
          (mul_le_mul_of_nonneg_left hsl (by positivity))) (hD _)
      _ = _ := by ring
  have hten : cNorm K q (hr : MetricField (d+1)) +
      cNorm K q (hi' : MetricField (d+1)) ≤ Ct * Z := by
    exact (add_le_add (cNorm_mono_order (by dsimp [m]; omega : q ≤ m))
      (cNorm_mono_order (by dsimp [m]; omega : q ≤ m))).trans (htensor v.val K)
  have hreg (h : compactSmoothSources S) : ContDiff ℝ ∞ (B h) :=
    contDiff_fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
      hchart hF hi hrank h
  have hjet (h : compactSmoothSources S) :
      ‖iteratedFDeriv ℝ q (B h) y‖ ≤ Cg *
        (cNorm K (q+1) (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) +
          cNorm K q (h : MetricField (d+1))) := by
    have heq := ((fixedSmoothSolverAmbientExtension_eventuallyEq F Q η hU hQ hη hSU
      solver hsolver Ξ h (hcore hy)).iteratedFDeriv ℝ q).self_of_nhds
    rw [heq]
    exact hcompletion _ _ (hsolver _) h.property.1 y hy
  have hcomplex := norm_iteratedFDeriv_complexifyResponse_le B (tensorTestSource e i j v.val)
    (hreg hr) (hreg hi') q y
  apply hcomplex.trans
  apply (add_le_add (hjet hr) (hjet hi')).trans
  calc
    _ = Cg * ((cNorm K (q+1) (solver sr) + cNorm K (q+1) (solver si)) +
        (cNorm K q (hr : MetricField (d+1)) + cNorm K q (hi' : MetricField (d+1)))) := by ring
    _ ≤ Cg * ((D (q+1) * (2 + a (m+β)) * Cs) * Z + Ct * Z) :=
      mul_le_mul_of_nonneg_left (add_le_add hsol hten) hCg
    _ = C * Z := by dsimp [C]; ring

end JanetCartan.CorrectedAtoms
