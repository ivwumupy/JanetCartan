module

public import JanetCartan.Iteration.PhysicalMean.LinearProfiles
public import JanetCartan.Iteration.PhysicalMean.PicardProfiles
public import JanetCartan.Iteration.PhysicalMean.Precision
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation

/-!
# Middle source precision for the actual finite Picard run

The two-term fixed-cutoff recurrence controls the low norm. The independently
proved high profiles control the SAME run at `s0=2*m0`. Weighted Fourier
interpolation then gives the square-root gain required by Step 5 of
`app:ch_mean_pairs:prop:mean-iteration`. This deduction neither changes K
between iterates nor assumes the desired final residual estimate.
The actual E and Q estimates are supplied by LinearProfiles,
CanonicalQuadraticProfile, CarrierOnlyTail and CanonicalLowQuadratic.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential

/-- The ACTUAL full canonical quadratic is symmetric, so the difference
recurrence applies directly, without a polarization or symmetry premise. -/
theorem fixedSourceQuadratic_comm {n : ℕ} {ι m : Type*} [Fintype ι] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
    (weight : ι → ℝ)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] ContinuumRow.OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (u v : SmoothResidual n) :
    fixedSourceQuadratic weight C hC A G Q₀ u v = fixedSourceQuadratic weight C hC A G Q₀ v u := by
  apply Subtype.ext
  funext x slot
  change C x (∑ i, weight i • mixedHermitianTensor
      ((fixedSourceDerivative A G Q₀ u).val x i) ((fixedSourceDerivative A G Q₀ v).val x i)) =
    C x (∑ i, weight i • mixedHermitianTensor
      ((fixedSourceDerivative A G Q₀ v).val x i) ((fixedSourceDerivative A G Q₀ u).val x i))
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mixedHermitianTensor_comm]

/-- Interpolate the SAME smooth source at the exact middle Sobolev order.
Only its actual Fourier class is used; there is no artificial smooth norm or
embedding-order loss in the analytic source recurrence. -/
theorem residualSobolevSeminorm_middle_le {n m₀ : ℕ} (hm₀ : 0 < m₀)
    (u : SmoothResidual n) {δ h A B : ℝ} (hδ : 0 < δ)
    (hlow : residualSobolevSeminorm n 0 u ≤ A*h*δ)
    (hhigh : residualSobolevSeminorm n (2*m₀) u ≤ B*h) :
    residualSobolevSeminorm n m₀ u ≤ (A+B)*h*Real.sqrt δ := by
  have hi := periodic_gradeNorm_weighted_interpolate (show m₀ ≤ 2*m₀ by omega)
    (inv_nonneg.mpr hδ.le)
    (ofL2 (2*m₀) (smoothResidualToL2 n u) (smoothResidualToL2_mem u (2*m₀)))
  rw [toL2_ofL2, norm_eq, toL2_ofL2, ← residualSobolevSeminorm_eq_gradeNorm,
    ← residualSobolevSeminorm_eq_periodicSobolevNorm, ← residualSobolevSeminorm_zero] at hi
  have hmpos : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have he : 1-(m₀ : ℝ)/(2*m₀ : ℕ) = (1/2 : ℝ) := by
    push_cast
    field_simp
    ring
  rw [he, ← Real.sqrt_eq_rpow, Real.sqrt_inv] at hi
  have hright : residualSobolevSeminorm n (2*m₀) u+δ⁻¹*residualSobolevSeminorm n 0 u ≤ (A+B)*h := by
    apply (add_le_add hhigh (mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hδ.le))).trans_eq
    field_simp
    ring
  have hi' : residualSobolevSeminorm n m₀ u/Real.sqrt δ ≤ (A+B)*h := by
    simpa only [div_eq_mul_inv, mul_comm] using hi.trans hright
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hδ)).mp hi'

/-- The actual middle order `m0=floor(n/2)+2` controls the original physical
source and its first derivative. This is the sharp Fourier embedding, not the
older loss-n estimate. The same representative is retained everywhere. -/
theorem cNorm_residualRepresentative_le_middle {n : ℕ} (u : SmoothResidual n) :
    cNorm (fundamentalCell n) 1 (periodicLift (fun x ↦ u.val x ())) ≤
      (2*fourierInterpolationConstant n 1 (n/2+2))*residualSobolevSeminorm n (n/2+2) u := by
  have hrep (s : ℕ) : periodicSobolevNorm s (fun x ↦ u.val x ()) = residualSobolevSeminorm n s u := by
    rw [residualSobolevSeminorm_eq_gradeNorm, smoothResidualToL2_gradeNorm]
  have hm : (1 : ℝ)+(n : ℝ)/2 < ((n/2+2 : ℕ) : ℝ) := by
    have hi : n < 2*(n/2+1) := by omega
    have hi' : (n : ℝ) < ((2*(n/2+1) : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at hi' ⊢
    linarith
  have hc := cNorm_le_fourierInterpolation (r := 1) (m := n/2+2) (K := 1)
    (SmoothPeriodicFamily.smooth u ()) (by simpa only [Nat.cast_one] using hm)
    (show (1 : ℝ) ≤ 1 from le_rfl)
  have hzrep : periodicSobolevNorm 0 (fun x ↦ u.val x ()) = residualSobolevSeminorm n 0 u := by
    simpa only [Nat.cast_zero] using hrep 0
  rw [Real.one_rpow, Real.one_rpow, one_mul, one_mul,
    ← periodicSobolevNorm_zero_eq_periodicL2Norm (SmoothPeriodicFamily.memLp u ()), hzrep, hrep (n/2+2)] at hc
  have hlo : residualSobolevSeminorm n 0 u ≤ residualSobolevSeminorm n (n/2+2) u := by
    rw [residualSobolevSeminorm_zero, residualSobolevSeminorm_eq_gradeNorm]
    exact (periodicSobolevScale n (Euclidean n)).norm_le_gradeNorm (smoothResidualToL2_mem u _)
  apply hc.trans
  exact (mul_le_mul_of_nonneg_left (add_le_add hlo le_rfl)
    (fourierInterpolationConstant_nonneg n 1 (n/2+2))).trans_eq (by ring)

/-- The finite constant contains only the fixed profile recursion and the
chosen finite J and proof-tail order q. It is independent of K, scales, sources,
samples and histories. -/
def finiteSourceResidualConstant (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (b : ℝ) (m₀ q J : ℕ) : ℝ :=
  let D := fun s ↦ ∑ k ∈ Finset.range (J+1), sourceIterateProfile Cg CE CQ k s
  Cg 0+2*(J : ℝ)*b*(D q+D 0)+
    (sourceIterateProfile Cg CE CQ (J+1) (2*m₀)+sourceIterateProfile Cg CE CQ J (2*m₀))

/-- Nonnegativity is proved from the original order-only coefficient bounds. -/
theorem finiteSourceResidualConstant_nonneg (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    {b : ℝ} (hb : 0 ≤ b) (m₀ q J : ℕ) : 0 ≤ finiteSourceResidualConstant Cg CE CQ b m₀ q J := by
  have hP := sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ
  have hD (s : ℕ) : 0 ≤ ∑ k ∈ Finset.range (J+1), sourceIterateProfile Cg CE CQ k s :=
    Finset.sum_nonneg fun k _ ↦ hP k s
  unfold finiteSourceResidualConstant
  exact add_nonneg (add_nonneg (hCg 0)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg J)) hb)
      (add_nonneg (hD q) (hD 0)))) (add_nonneg (hP _ _) (hP _ _))

/-- The actual smooth residual of the constructed finite run has the precise
middle-order square-root bound. Low contraction is used ONLY at order zero;
higher profile constants may grow with this finite J. The caller applies the
four checked canonical analytic producers, not a successful Picard premise. -/
theorem sourceResidual_fixedCutoff_middle_le {n : ℕ}
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    (E : SmoothResidual n →ₗ[ℝ] SmoothResidual n)
    (Q : SmoothResidual n →ₗ[ℝ] SmoothResidual n →ₗ[ℝ] SmoothResidual n)
    (hQ : ∀ u v, Q u v = Q v u) (g : SmoothResidual n)
    (m₀ q J : ℕ) (hm₀ : 0 < m₀)
    {T R K h a b c₀ ω : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hK : 0 < K)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc₀ : 0 ≤ c₀) (hω : 0 ≤ ω)
    (hg : ∀ s, residualSobolevSeminorm n s g ≤ Cg s*h*R^(s-2*m₀))
    (hlinear : ∀ u s, residualSobolevSeminorm n s (E u) ≤ CE s*
      (residualSobolevSeminorm n s u+T^(s-2*m₀)*residualSobolevSeminorm n 0 u))
    (hquadratic : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ u : SmoothResidual n,
      (∀ s, residualSobolevSeminorm n s u ≤ A s*h*R^(s-2*m₀)) → ∀ s,
      residualSobolevSeminorm n s (Q u u) ≤ CQ A s*h^2*R^(s-2*m₀))
    (hlowLinear : ∀ u, residualSobolevSeminorm n 0 (u-E u) ≤ a*residualSobolevSeminorm n 0 u+
      (b/K^q)*(residualSobolevSeminorm n q u+T^(q-2*m₀)*residualSobolevSeminorm n 0 u))
    (hlowQuadratic : ∀ u v, residualSobolevSeminorm n 0 (Q u v) ≤
      c₀*residualSobolevSeminorm n 0 u*residualSobolevSeminorm n m₀ v) :
    let D := fun s ↦ ∑ k ∈ Finset.range (J+1), sourceIterateProfile Cg CE CQ k s
    a+2*c₀*D m₀*h ≤ R^(-ω) →
      residualSobolevSeminorm n m₀ (sourceResidual E Q g (sourceIterate E Q g J)) ≤
        finiteSourceResidualConstant Cg CE CQ b m₀ q J*h*
          Real.sqrt (R^(-ω*(J : ℝ))+(R/K)^q) := by
  intro D hsmall
  have hP := sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ
  have hD (s : ℕ) : 0 ≤ D s := Finset.sum_nonneg fun k _ ↦ hP k s
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hcut : 0 ≤ (R/K)^q := pow_nonneg (div_nonneg hRp.le hK.le) _
  have hbase : 0 ≤ a+2*c₀*D m₀*h :=
    add_nonneg ha (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc₀) (hD m₀)) hh)
  have hsmallOne : a+2*c₀*D m₀*h ≤ 1 :=
    hsmall.trans (Real.rpow_le_one_of_one_le_of_nonpos hR (neg_nonpos.mpr hω))
  have hlow := sourceResidual_fixedCutoff_seminorm_le (residualSobolevSeminorm n)
    Cg CE CQ hCg hCE hCQ E Q hQ g (2*m₀) m₀ q J (by omega)
    hT hR hTR hK hh hh1 ha hb hc₀ hg hlinear hquadratic hlowLinear hlowQuadratic hsmallOne
  have hpower : (a+2*c₀*D m₀*h)^J ≤ R^(-ω*(J : ℝ)) := by
    apply (pow_le_pow_left₀ hbase hsmall J).trans_eq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
  let ctail := 2*(J : ℝ)*b*(D q+D 0)
  have hctail : 0 ≤ ctail :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg J)) hb)
      (add_nonneg (hD q) (hD 0))
  have hlow' : residualSobolevSeminorm n 0 (sourceResidual E Q g (sourceIterate E Q g J)) ≤
      (Cg 0+ctail)*h*(R^(-ω*(J : ℝ))+(R/K)^q) := by
    apply hlow.trans
    have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower (hCg 0)) hh
    have hcross₁ := mul_nonneg (mul_nonneg (hCg 0) hh) hcut
    have hcross₂ := mul_nonneg (mul_nonneg hctail hh) (Real.rpow_nonneg hRp.le (-ω*(J : ℝ)))
    dsimp only [ctail] at hcross₂ ⊢
    nlinarith only [hp, hcross₁, hcross₂]
  have hprofile := sourceIterate_seminorm_profile (residualSobolevSeminorm n)
    Cg CE CQ hCg hCE hCQ E Q g (2*m₀) hT hR hTR hh hh1 hg hlinear hquadratic
  have hhigh : residualSobolevSeminorm n (2*m₀) (sourceResidual E Q g (sourceIterate E Q g J)) ≤
      (sourceIterateProfile Cg CE CQ (J+1) (2*m₀)+sourceIterateProfile Cg CE CQ J (2*m₀))*h := by
    rw [sourceResidual_eq_difference]
    have he := (map_sub_le_add (residualSobolevSeminorm n (2*m₀)) _ _).trans
      (add_le_add (hprofile (J+1) (2*m₀)) (hprofile J (2*m₀)))
    simpa only [Nat.sub_self, pow_zero, mul_one, add_mul] using he
  have hδ : 0 < R^(-ω*(J : ℝ))+(R/K)^q :=
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hRp _) hcut
  exact residualSobolevSeminorm_middle_le hm₀ _ hδ hlow' hhigh

end JanetCartan.PhysicalMean
