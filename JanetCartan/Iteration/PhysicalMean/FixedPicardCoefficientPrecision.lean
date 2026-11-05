module

public import JanetCartan.Iteration.PhysicalMean.SourcePrecision

/-!
# Preserve the fixed contraction constant in source precision

`paper-v2.tex`, Step5 of `app:ch_mean_pairs:prop:mean-iteration`, keeps
C_N*R^(-ω) in the low recurrence and absorbs its N-th power into the finite
residual constant. It does NOT require the coefficient to equal one.
This deduction preserves the actual sampling exponent ω and fixed K, source,
operators and run. It strengthens the consumer interface, not the event.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean
open CurrentMean

/-- The coefficient power is a FINITE Picard-index cost, not a band, sample
or wave cardinality loss. All inputs are fixed before the current history. -/
def finiteSourceResidualConstantWithCoefficient
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ) (b Cρ : ℝ) (m₀ q N : ℕ) : ℝ :=
  let D := fun s ↦ ∑ k ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ k s
  Cρ^N*Cg 0+2*(N : ℝ)*b*(D q+D 0)+
    (sourceIterateProfile Cg CE CQ (N+1) (2*m₀)+sourceIterateProfile Cg CE CQ N (2*m₀))

/-- Nonnegativity of the coefficient-preserving finite residual budget. -/
theorem finiteSourceResidualConstantWithCoefficient_nonneg
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    {b Cρ : ℝ} (hb : 0 ≤ b) (hCρ : 0 ≤ Cρ) (m₀ q N : ℕ) :
    0 ≤ finiteSourceResidualConstantWithCoefficient Cg CE CQ b Cρ m₀ q N := by
  have hP := sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ
  have hD (s : ℕ) : 0 ≤ ∑ k ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ k s :=
    Finset.sum_nonneg fun k _ ↦ hP k s
  unfold finiteSourceResidualConstantWithCoefficient
  exact add_nonneg (add_nonneg (mul_nonneg (pow_nonneg hCρ _) (hCg 0))
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N)) hb)
      (add_nonneg (hD q) (hD 0)))) (add_nonneg (hP _ _) (hP _ _))

/-- The literal fixed-source residual at the middle order, retaining the
static contraction coefficient exactly as in the manuscript. The hypotheses
are only the primitive high/low estimates and numerical contraction; no final
source, iterate or residual bound is assumed. -/
theorem sourceResidual_fixedCutoff_middle_le_with_coefficient {n : ℕ}
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    (E : SmoothResidual n →ₗ[ℝ] SmoothResidual n)
    (Q : SmoothResidual n →ₗ[ℝ] SmoothResidual n →ₗ[ℝ] SmoothResidual n)
    (hQ : ∀ u v, Q u v = Q v u) (g : SmoothResidual n)
    (m₀ q N : ℕ) (hm₀ : 0 < m₀)
    {T R K h a b c₀ ω Cρ : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hK : 0 < K)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc₀ : 0 ≤ c₀) (hCρ : 0 ≤ Cρ)
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
    let D := fun s ↦ ∑ k ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ k s
    a+2*c₀*D m₀*h ≤ Cρ*R^(-ω) → Cρ*R^(-ω) ≤ 1 →
      residualSobolevSeminorm n m₀ (sourceResidual E Q g (sourceIterate E Q g N)) ≤
        finiteSourceResidualConstantWithCoefficient Cg CE CQ b Cρ m₀ q N*h*
          Real.sqrt (R^(-ω*(N : ℝ))+(R/K)^q) := by
  intro D hscaled hsmall
  have hP := sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ
  have hD (s : ℕ) : 0 ≤ D s := Finset.sum_nonneg fun k _ ↦ hP k s
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hcut : 0 ≤ (R/K)^q := pow_nonneg (div_nonneg hRp.le hK.le) _
  have hbase : 0 ≤ a+2*c₀*D m₀*h :=
    add_nonneg ha (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc₀) (hD m₀)) hh)
  have hlow := sourceResidual_fixedCutoff_seminorm_le (residualSobolevSeminorm n)
    Cg CE CQ hCg hCE hCQ E Q hQ g (2*m₀) m₀ q N (by omega)
    hT hR hTR hK hh hh1 ha hb hc₀ hg hlinear hquadratic hlowLinear hlowQuadratic
    (hscaled.trans hsmall)
  have hpow : (R^(-ω))^N = R^(-ω*(N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
  have hpower : (a+2*c₀*D m₀*h)^N ≤ Cρ^N*R^(-ω*(N : ℝ)) := by
    exact (pow_le_pow_left₀ hbase hscaled N).trans_eq (by rw [mul_pow,hpow])
  let ctail := 2*(N : ℝ)*b*(D q+D 0)
  have hctail : 0 ≤ ctail :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N)) hb)
      (add_nonneg (hD q) (hD 0))
  have hlow' : residualSobolevSeminorm n 0 (sourceResidual E Q g (sourceIterate E Q g N)) ≤
      (Cρ^N*Cg 0+ctail)*h*(R^(-ω*(N : ℝ))+(R/K)^q) := by
    apply hlow.trans
    have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower (hCg 0)) hh
    have hcross₁ := mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hCρ N) (hCg 0)) hh) hcut
    have hcross₂ := mul_nonneg (mul_nonneg hctail hh) (Real.rpow_nonneg hRp.le (-ω*(N : ℝ)))
    dsimp only [ctail] at hcross₂ ⊢
    nlinarith only [hp,hcross₁,hcross₂]
  have hprofile := sourceIterate_seminorm_profile (residualSobolevSeminorm n)
    Cg CE CQ hCg hCE hCQ E Q g (2*m₀) hT hR hTR hh hh1 hg hlinear hquadratic
  have hhigh : residualSobolevSeminorm n (2*m₀) (sourceResidual E Q g (sourceIterate E Q g N)) ≤
      (sourceIterateProfile Cg CE CQ (N+1) (2*m₀)+sourceIterateProfile Cg CE CQ N (2*m₀))*h := by
    rw [sourceResidual_eq_difference]
    have he := (map_sub_le_add (residualSobolevSeminorm n (2*m₀)) _ _).trans
      (add_le_add (hprofile (N+1) (2*m₀)) (hprofile N (2*m₀)))
    simpa only [Nat.sub_self,pow_zero,mul_one,add_mul] using he
  have hδ : 0 < R^(-ω*(N : ℝ))+(R/K)^q :=
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hRp _) hcut
  exact residualSobolevSeminorm_middle_le hm₀ _ hδ hlow' hhigh

end JanetCartan.PhysicalMean
end
