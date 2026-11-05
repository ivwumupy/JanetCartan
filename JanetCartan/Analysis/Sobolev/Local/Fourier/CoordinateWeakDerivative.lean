module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakLimits
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection

/-!
# Distributional coordinate derivatives and real weak Fréchet derivatives

The reverse distribution-to-weak bridge for `app:not:fourier`. This leaf is
used by the restriction H¹ comparison for
`app:ch_regular_base:eq:sector-theorem-residual`. All measures are Euclidean
Lebesgue measures and all differentiation is over ℝ, including complex fibers.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped SchwartzMap LineDeriv ContDiff

namespace JanetCartan.Pseudodifferential

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- An actual distributional coordinate derivative satisfies the compact real
test identity used in `app:not:fourier`. No regularity of the representatives
is required. -/
theorem HasEuclideanL2CoordinateDerivative.integral_test {i : Fin n}
    {u v : Lp (α := E) ℂ 2} (h : HasEuclideanL2CoordinateDerivative i u v)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ψ x • v x) =
      - ∫ x, fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • u x := by
  let φ := (hc.toSchwartzMap hψ).postcompCLM Complex.ofRealCLM
  have hd (x : E) : fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      (fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) : ℂ) := by
    exact congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((Complex.ofRealCLM.hasFDerivAt.comp x
        ((hψ.differentiable (by simp) x).hasFDerivAt)).fderiv)
  have he := congrArg (fun T : 𝓢'(E, ℂ) ↦ T φ) h
  change (∂_{EuclideanSpace.basisFun (Fin n) ℝ i} (u : 𝓢'(E, ℂ))) φ = _ at he
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at he
  have hφ (x : E) : φ x = (ψ x : ℂ) := rfl
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, hd, hφ,
    smul_eq_mul, Complex.real_smul] using he.symm

end JanetCartan.Pseudodifferential

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Reassemble real coordinate derivative fields as a field of Fréchet maps
for `app:not:fourier`. The operator norm is not identified with a coordinate
norm; it will be bounded using the triangle inequality. -/
def coordinateFDeriv (v : Fin n → E → F) (x : E) : E →L[ℝ] F :=
  ∑ i, (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).smulRight (v i x)

/-- Evaluation of the assembled weak derivative, for
`app:ch_regular_base:eq:sector-theorem-residual`. -/
theorem coordinateFDeriv_apply (v : Fin n → E → F) (x z : E) :
    coordinateFDeriv v x z = ∑ i, z i • v i x := by
  simp [coordinateFDeriv]

/-- Coordinate synthesis preserves genuine L² membership, for
`app:not:fourier`. -/
theorem memLp_coordinateFDeriv {v : Fin n → E → F}
    (hv : ∀ i, MemLp (v i) 2 volume) : MemLp (coordinateFDeriv v) 2 volume := by
  exact memLp_finsetSum Finset.univ (f := fun i x ↦
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).smulRight (v i x))
    (fun i _ ↦ (ContinuousLinearMap.smulRightL ℝ E F
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)).comp_memLp' (hv i))

/-- Coordinate synthesis controls the L² operator norm by the sum of the L²
coordinate norms. This is the explicit norm conversion in `app:not:fourier`. -/
theorem l2Norm_coordinateFDeriv_le {v : Fin n → E → F}
    (hv : ∀ i, MemLp (v i) 2 volume) :
    (eLpNorm (coordinateFDeriv v) 2 volume).toReal ≤
      ∑ i, (eLpNorm (v i) 2 volume).toReal := by
  let L (i : Fin n) := ContinuousLinearMap.smulRightL ℝ E F
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)
  have hL (i : Fin n) : ‖L i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [one_mul]
    change ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).smulRight z‖ ≤ ‖z‖
    rw [ContinuousLinearMap.norm_smulRight_apply]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using PiLp.norm_apply_le x i
  have hb (i : Fin n) : (eLpNorm (fun x ↦ L i (v i x)) 2 volume).toReal ≤
      (eLpNorm (v i) 2 volume).toReal := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((L i).comp_memLp' (hv i)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ (L i).le_opNorm (v i x)) 2
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv i).eLpNorm_ne_top) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at ht
    exact ht.trans (mul_le_of_le_one_left ENNReal.toReal_nonneg (hL i))
  have hsum := eLpNorm_sum_le (μ := (volume : Measure E)) (p := 2)
    (f := fun i x ↦ L i (v i x)) (s := Finset.univ) (by norm_num)
  have ht := ENNReal.toReal_mono
    (show (∑ i, eLpNorm (fun x ↦ L i (v i x)) 2 volume) ≠ ⊤ by
      exact ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ ↦
        ((L i).comp_memLp' (hv i)).eLpNorm_lt_top)) hsum
  rw [ENNReal.toReal_sum (f := fun i ↦ eLpNorm (fun x ↦ L i (v i x)) 2 volume)
    (fun i _ ↦ ((L i).comp_memLp' (hv i)).eLpNorm_ne_top)] at ht
  have heq : (∑ i, fun x ↦ L i (v i x)) = coordinateFDeriv v := by
    funext x
    simp [coordinateFDeriv, L]
  rw [heq] at ht
  exact ht.trans (Finset.sum_le_sum fun i _ ↦ hb i)

/-- Compact test identities in all real coordinates imply the full weak
Fréchet identity. This is the finite-dimensional reconstruction needed by
`app:ch_regular_base:eq:sector-theorem-residual`. -/
theorem hasWeakFDerivOn_coordinateFDeriv {f : E → F} {v : Fin n → E → F}
    (hf : MemLp f 2 volume) (hv : ∀ i, MemLp (v i) 2 volume)
    (htest : ∀ (ψ : E → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ i, (∫ x, ψ x • v i x) =
        - ∫ x, fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • f x) :
    Mollification.HasWeakFDerivOn volume f (coordinateFDeriv v) univ := by
  refine ⟨(hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ,
    ((memLp_coordinateFDeriv hv).locallyIntegrable (by norm_num)).locallyIntegrableOn univ,
    ?_⟩
  intro ψ hψ hc _ z
  have hi (i : Fin n) : Integrable (fun x ↦ ψ x • v i x) :=
    ((hv i).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hψ.continuous hc
  have hd (i : Fin n) : Integrable
      (fun x ↦ fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • f x) := by
    apply (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hc.fderiv ℝ).comp_left
        (g := fun L : E →L[ℝ] ℝ ↦ L (EuclideanSpace.basisFun (Fin n) ℝ i)) rfl
  have hz : ∑ i, z i • EuclideanSpace.basisFun (Fin n) ℝ i = z := by
    simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
  have hdz (x : E) : fderiv ℝ ψ x z =
      ∑ i, z i * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    conv_lhs => rw [← hz]
    simp
  simp_rw [coordinateFDeriv_apply, Finset.smul_sum, smul_comm (ψ _)]
  rw [integral_finsetSum Finset.univ (f := fun i x ↦ z i • (ψ x • v i x))
    (fun i _ ↦ (hi i).smul (z i))]
  simp only [integral_smul, htest ψ hψ hc, smul_neg, Finset.sum_neg_distrib]
  congr 1
  simp_rw [← integral_smul]
  rw [← integral_finsetSum Finset.univ
    (f := fun i x ↦ z i • (fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • f x))
    (fun i _ ↦ (hd i).smul (z i))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    dsimp only
    rw [hdz]
    simp [Finset.sum_smul, mul_smul]

end JanetCartan.LocalSobolev
