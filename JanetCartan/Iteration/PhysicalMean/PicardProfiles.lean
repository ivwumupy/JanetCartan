module

public import JanetCartan.Iteration.PhysicalMean.Precision
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# All-order profiles in the same fixed-cutoff finite Picard run

The constants below are chosen before the history, sample, source and fixed
input cutoff. They may depend on the FINITE Picard index; no high-order
contraction or cutoff adaptation is asserted. The input estimates are exactly
`block-normal`, `block-bilinear` and the revised original source forcing
profile, whose original-data producers remain explicit parent obligations
(`new:eq:source-bound`, `app:ch_mean_pairs:prop:mean-iteration`).
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalMean

/-- The all-order finite Picard profile. The quadratic budget is evaluated
on the previous profile only, never on an assumed successful iterate. -/
def sourceIterateProfile (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ ↦ 0
  | j+1 => fun s ↦ Cg s + sourceIterateProfile Cg CE CQ j s +
      CE s * (sourceIterateProfile Cg CE CQ j s + sourceIterateProfile Cg CE CQ j 0) +
      CQ (sourceIterateProfile Cg CE CQ j) s

/-- Every finite iterate constant is nonnegative, independently of source
scale, fixed cutoff, history and sample. -/
theorem sourceIterateProfile_nonneg (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s) (j s : ℕ) :
    0 ≤ sourceIterateProfile Cg CE CQ j s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    exact add_nonneg (add_nonneg (add_nonneg (hCg s) (ih s))
      (mul_nonneg (hCE s) (add_nonneg (ih s) (ih 0)))) (hCQ _ ih s)

/-- The SAME fixed operators generate actual all-order finite Picard
profiles. This proves the induction in `new:eq:source-bound` from primitive
linear, balanced quadratic and forcing estimates; no iterate profile is a
premise and no new cutoff is selected at any step. -/
theorem sourceIterate_seminorm_profile {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ Y)
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y) (g : Y)
    (s₀ : ℕ) {T R h : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R)
    (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hg : ∀ s, p s g ≤ Cg s*h*R^(s-s₀))
    (hlinear : ∀ u s, p s (E u) ≤ CE s*(p s u+T^(s-s₀)*p 0 u))
    (hquadratic : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ u : Y,
      (∀ s, p s u ≤ A s*h*R^(s-s₀)) → ∀ s,
      p s (Q u u) ≤ CQ A s*h^2*R^(s-s₀)) :
    ∀ j s, p s (sourceIterate E Q g j) ≤ sourceIterateProfile Cg CE CQ j s*h*R^(s-s₀) := by
  have hT0 := zero_le_one.trans hT
  have hR0 := zero_le_one.trans hR
  have hprof := sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ
  intro j
  induction j with
  | zero => intro s; simp [sourceIterate, sourceIterateProfile]
  | succ j ih =>
    intro s
    let D := sourceIterateProfile Cg CE CQ j
    let r := sourceIterate E Q g j
    have hpow : T^(s-s₀) ≤ R^(s-s₀) := pow_le_pow_left₀ hT0 hTR _
    have hzero : p 0 r ≤ D 0*h := by simpa only [Nat.zero_sub, pow_zero, mul_one] using ih 0
    have hlow : T^(s-s₀)*p 0 r ≤ D 0*h*R^(s-s₀) := by
      calc
        _ ≤ T^(s-s₀)*(D 0*h) := mul_le_mul_of_nonneg_left hzero (pow_nonneg hT0 _)
        _ ≤ R^(s-s₀)*(D 0*h) := mul_le_mul_of_nonneg_right hpow (mul_nonneg (hprof j 0) hh)
        _ = _ := by ring
    have he : p s (E r) ≤ CE s*(D s+D 0)*h*R^(s-s₀) := by
      apply (hlinear r s).trans
      exact (mul_le_mul_of_nonneg_left (add_le_add (ih s) hlow) (hCE s)).trans_eq (by ring)
    have hq : p s (Q r r) ≤ CQ D s*h*R^(s-s₀) := by
      apply (hquadratic D (hprof j) r ih s).trans
      have hsquare : h^2 ≤ h := by nlinarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare (hCQ D (hprof j) s)) (pow_nonneg hR0 _)
    change p s (g+(r-E r)-Q r r) ≤ _
    calc
      _ ≤ p s g + (p s r+p s (E r)) + p s (Q r r) :=
        (map_sub_le_add (p s) _ _).trans
          (add_le_add ((map_add_le_add (p s) _ _).trans
            (add_le_add le_rfl (map_sub_le_add (p s) _ _))) le_rfl)
      _ ≤ Cg s*h*R^(s-s₀) + (D s*h*R^(s-s₀)+CE s*(D s+D 0)*h*R^(s-s₀)) +
          CQ D s*h*R^(s-s₀) := add_le_add (add_le_add (hg s) (add_le_add (ih s) he)) hq
      _ = _ := by dsimp only [sourceIterateProfile, D]; ring

/-- A finite run has a single common profile chosen before the source data.
Only the finite Picard index is summed; no sample or frequency band is summed. -/
theorem sourceIterate_profile_le_finite_sum
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    {j J : ℕ} (hj : j ≤ J) (s : ℕ) :
    sourceIterateProfile Cg CE CQ j s ≤ ∑ k ∈ Finset.range (J+1), sourceIterateProfile Cg CE CQ k s :=
  Finset.single_le_sum (fun k _ ↦ sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ k s)
    (by simp only [Finset.mem_range]; omega)

/-- The residual difference estimate in an actual source Sobolev seminorm.
This version applies directly to smooth source fields and does not equip
all L² functions with an invalid finite higher-Sobolev norm. -/
theorem sourceResidual_seminorm_le {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (p : Seminorm ℝ Y) (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (hQ : ∀ u v, Q u v = Q v u) (g : Y) (J : ℕ)
    {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (ht : 0 ≤ t) (hsmall : a+c ≤ 1)
    (hlinear : ∀ j < J,
      let d := sourceIterate E Q g (j+1)-sourceIterate E Q g j
      p (d-E d) ≤ a*p d+t)
    (hquadratic : ∀ j < J,
      let d := sourceIterate E Q g (j+1)-sourceIterate E Q g j
      p (Q d (sourceIterate E Q g (j+1)+sourceIterate E Q g j)) ≤ c*p d) :
    p (sourceResidual E Q g (sourceIterate E Q g J)) ≤ (a+c)^J*p g+(J : ℝ)*t := by
  have hstep (j : ℕ) (hj : j < J) :
      p (sourceIterate E Q g (j+2)-sourceIterate E Q g (j+1)) ≤
        (a+c)*p (sourceIterate E Q g (j+1)-sourceIterate E Q g j)+t := by
    rw [sourceIterate_difference_succ E Q hQ]
    exact ((map_sub_le_add p _ _).trans (add_le_add (hlinear j hj) (hquadratic j hj))).trans_eq (by ring)
  have hbound : ∀ j ≤ J,
      p (sourceIterate E Q g (j+1)-sourceIterate E Q g j) ≤ (a+c)^j*p g+(j : ℝ)*t := by
    intro j
    induction j with
    | zero => intro _; simp [sourceIterate]
    | succ j ih =>
      intro hj
      have hp := mul_le_mul_of_nonneg_left (ih (by omega)) (add_nonneg ha hc)
      have htj : (a+c)*((j : ℝ)*t) ≤ (j : ℝ)*t :=
        mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) ht) hsmall
      have hn := hstep j (by omega)
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith
  rw [sourceResidual_eq_difference]
  exact hbound J le_rfl

/-- The actual finite run at the SAME fixed input cutoff has the low
residual precision budget. Its finite high profiles are PROVED by the
preceding induction, not supplied as a successful-source hypothesis. The
regular-source cutoff tail is kept separate from the low linear defect.
This is the analytic input of `exists_source_iteration_precision`. -/
theorem sourceResidual_fixedCutoff_seminorm_le {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ Y)
    (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y) (hQ : ∀ u v, Q u v = Q v u) (g : Y)
    (s₀ m₀ q J : ℕ) (hm₀ : m₀ ≤ s₀)
    {T R K h a b c₀ : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hK : 0 < K)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc₀ : 0 ≤ c₀)
    (hg : ∀ s, p s g ≤ Cg s*h*R^(s-s₀))
    (hlinear : ∀ u s, p s (E u) ≤ CE s*(p s u+T^(s-s₀)*p 0 u))
    (hquadratic : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ u : Y,
      (∀ s, p s u ≤ A s*h*R^(s-s₀)) → ∀ s,
      p s (Q u u) ≤ CQ A s*h^2*R^(s-s₀))
    (hlowLinear : ∀ u, p 0 (u-E u) ≤ a*p 0 u+(b/K^q)*(p q u+T^(q-s₀)*p 0 u))
    (hlowQuadratic : ∀ u v, p 0 (Q u v) ≤ c₀*p 0 u*p m₀ v) :
    let D := fun s ↦ ∑ k ∈ Finset.range (J+1), sourceIterateProfile Cg CE CQ k s
    a+2*c₀*D m₀*h ≤ 1 →
      p 0 (sourceResidual E Q g (sourceIterate E Q g J)) ≤
        (a+2*c₀*D m₀*h)^J*Cg 0*h+2*(J : ℝ)*b*(D q+D 0)*h*(R/K)^q := by
  intro D hsmall
  have hD (s : ℕ) : 0 ≤ D s := Finset.sum_nonneg fun k _ ↦
    sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ k s
  have hDm := hD m₀
  have hDq := hD q
  have hDz := hD 0
  have hT0 := zero_le_one.trans hT
  have hR0 := zero_le_one.trans hR
  have hr (j : ℕ) (hj : j ≤ J) (s : ℕ) :
      p s (sourceIterate E Q g j) ≤ D s*h*R^(s-s₀) := by
    apply (sourceIterate_seminorm_profile p Cg CE CQ hCg hCE hCQ E Q g s₀
      hT hR hTR hh hh1 hg hlinear hquadratic j s).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sourceIterate_profile_le_finite_sum Cg CE CQ hCg hCE hCQ hj s) hh)
      (pow_nonneg (zero_le_one.trans hR) _)
  have hd (j : ℕ) (hj : j < J) (s : ℕ) :
      p s (sourceIterate E Q g (j+1)-sourceIterate E Q g j) ≤ 2*D s*h*R^(s-s₀) :=
    ((map_sub_le_add (p s) _ _).trans (add_le_add (hr (j+1) (by omega) s) (hr j (by omega) s))).trans_eq (by ring)
  have hs (j : ℕ) (hj : j < J) :
      p m₀ (sourceIterate E Q g (j+1)+sourceIterate E Q g j) ≤ 2*D m₀*h := by
    have hsum := (map_add_le_add (p m₀) _ _).trans
      (add_le_add (hr (j+1) (by omega) m₀) (hr j (by omega) m₀))
    simpa only [Nat.sub_eq_zero_of_le hm₀, pow_zero, mul_one, two_mul, add_mul] using hsum
  have hlin (j : ℕ) (hj : j < J) :
      let d := sourceIterate E Q g (j+1)-sourceIterate E Q g j
      p 0 (d-E d) ≤ a*p 0 d+2*b*(D q+D 0)*h*(R/K)^q := by
    dsimp only
    apply (hlowLinear _).trans
    apply add_le_add le_rfl
    have hgq : p q (sourceIterate E Q g (j+1)-sourceIterate E Q g j) ≤ 2*D q*h*R^q :=
      (hd j hj q).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hR (Nat.sub_le _ _)) (by positivity))
    have hdz : p 0 (sourceIterate E Q g (j+1)-sourceIterate E Q g j) ≤ 2*D 0*h := by
      simpa only [Nat.zero_sub, pow_zero, mul_one] using hd j hj 0
    have hpt : T^(q-s₀) ≤ R^q :=
      (pow_le_pow_left₀ hT0 hTR _).trans (pow_le_pow_right₀ hR (Nat.sub_le _ _))
    have hgt : T^(q-s₀)*p 0 (sourceIterate E Q g (j+1)-sourceIterate E Q g j) ≤ 2*D 0*h*R^q := by
      calc
        _ ≤ T^(q-s₀)*(2*D 0*h) := mul_le_mul_of_nonneg_left hdz (pow_nonneg hT0 _)
        _ ≤ R^q*(2*D 0*h) := mul_le_mul_of_nonneg_right hpt (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (b/K^q)*(2*D q*h*R^q+2*D 0*h*R^q) :=
        mul_le_mul_of_nonneg_left (add_le_add hgq hgt) (by positivity)
      _ = _ := by rw [div_pow]; ring
  have hquad (j : ℕ) (hj : j < J) :
      let d := sourceIterate E Q g (j+1)-sourceIterate E Q g j
      p 0 (Q d (sourceIterate E Q g (j+1)+sourceIterate E Q g j)) ≤ (2*c₀*D m₀*h)*p 0 d := by
    dsimp only
    apply (hlowQuadratic _ _).trans
    exact (mul_le_mul_of_nonneg_left (hs j hj)
      (mul_nonneg hc₀ (apply_nonneg (p 0) _))).trans_eq (by ring)
  have hout := sourceResidual_seminorm_le (p 0) E Q hQ g J ha
    (show 0 ≤ 2*c₀*D m₀*h by positivity)
    (show 0 ≤ 2*b*(D q+D 0)*h*(R/K)^q by positivity) hsmall hlin hquad
  have hg0 : p 0 g ≤ Cg 0*h := by simpa only [Nat.zero_sub, pow_zero, mul_one] using hg 0
  have hgpow := mul_le_mul_of_nonneg_left hg0
    (pow_nonneg (show 0 ≤ a+2*c₀*D m₀*h by positivity) J)
  apply hout.trans
  calc
    _ ≤ (a+2*c₀*D m₀*h)^J*(Cg 0*h)+(J : ℝ)*(2*b*(D q+D 0)*h*(R/K)^q) :=
      add_le_add hgpow le_rfl
    _ = _ := by ring

end JanetCartan.PhysicalMean
