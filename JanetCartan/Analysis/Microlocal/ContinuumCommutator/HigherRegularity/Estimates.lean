module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.NormReconstruction
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.WeakDerivatives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.Bootstrap

/-!
# Recursive elliptic estimates on the existing periodic Sobolev scale

Combine the independently justified top weak derivatives with Fourier norm
reconstruction to supply `hstep` in `ContinuumInverse.Bootstrap`. The induction
uses the original coercive inverse and retains one high coefficient norm with
one fixed shift (`app:ch_background:eq:bg-commutator`,
`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-r-inverse`).
The actual matrix representation instantiates these commutators in `Assembly`.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.HigherRegularity

open PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The Sobolev-space norm and the existing graded norm agree on their common
L² element (`app:ch_background:eq:bg-r-inverse`). -/
private theorem norm_ofL2_eq_gradeNorm (s : ℕ) (v : PeriodicL2 n F)
    (hv : v ∈ periodicSobolevLevel n F s) :
    ‖ofL2 s v hv‖ = (periodicSobolevScale n F).gradeNorm s v := by
  rw [norm_eq, toL2_ofL2, (periodicSobolevScale n F).gradeNorm_eq hv]
  exact (periodicSobolevSeminorm_eq s ⟨v, hv⟩).symm

/-- The elliptic step constant depends on dimension, order, the coercive gap
and the low commutator constant, independently of the high coefficient budget
(`app:ch_background:prop:bg-inverse`). -/
def ellipticStepConstant (n s : ℕ) (c C : ℝ) : ℝ :=
  Real.sqrt (((n : ℝ) + 1) ^ (s + 1)) * (1 + c⁻¹ * (1 + C))

/-- Nonnegativity required by the quantitative induction
(`app:ch_background:eq:bg-r-inverse`). -/
theorem ellipticStepConstant_nonneg (n s : ℕ) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) : 0 ≤ ellipticStepConstant n s c C := by
  unfold ellipticStepConstant
  positivity

variable (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
  (E₁ Q₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
  (hself : IsSelfAdjoint E)
  (hE₁ : ∀ u, toL2 1 (E₁ u) = E (toL2 1 u))
  (hQ₁ : ∀ u, toL2 1 (Q₁ u) = E.inverse (toL2 1 u))
  {c : ℝ} (hc : 0 < c) (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫)

include hself hE₁ hQ₁ hc hgap

/-- The recursive a priori estimate on the actual Fourier Sobolev scale,
including the weak-derivative domain justification. This supplies `hstep` to
`ContinuumInverse.inverse_gradeNorm_le`; `A` occurs only once and only against
the original L² norm (`app:ch_background:eq:bg-commutator`,
`app:ch_background:eq:bg-r-inverse`). -/
theorem gradeNorm_succ_le_of_commutators
    (s : ℕ)
    (K : (is : List (Fin n)) → is.length = s + 1 →
      PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F)
    (hK : ∀ (is : List (Fin n)) (hlen : is.length = s + 1)
      (f : Torus n → F) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList is (E (toL2 s (ofSmooth s f hf)))
        (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is))) + K is hlen (ofSmooth s f hf)))
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbound : ∀ is hlen u, ‖K is hlen u‖ ≤ C * (‖u‖ + A * ‖toL2 s u‖))
    (v : PeriodicL2 n F) (hv : v ∈ periodicSobolevLevel n F s)
    (hev : E v ∈ periodicSobolevLevel n F (s + 1)) :
    (periodicSobolevScale n F).gradeNorm (s + 1) v ≤ ellipticStepConstant n s c C *
      ((periodicSobolevScale n F).gradeNorm (s + 1) (E v) +
        (periodicSobolevScale n F).gradeNorm s v + A * ‖v‖) := by
  let L := (periodicSobolevScale n F).gradeNorm s v
  let T := (periodicSobolevScale n F).gradeNorm (s + 1) (E v)
  have hL : 0 ≤ L := (periodicSobolevScale n F).gradeNorm_nonneg s v
  have hT : 0 ≤ T := (periodicSobolevScale n F).gradeNorm_nonneg (s + 1) (E v)
  have hN : 0 ≤ A * ‖v‖ := mul_nonneg hA (norm_nonneg v)
  have hi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hM : 0 ≤ c⁻¹ * (T + C * (L + A * ‖v‖)) := by positivity
  have htop : ∀ is : List (Fin n), is.length = s + 1 →
      ∃ w : PeriodicL2 n F, HasPeriodicWeakDerivativeList is v w ∧
        ‖w‖ ≤ c⁻¹ * (T + C * (L + A * ‖v‖)) := by
    intro is hlen
    cases is with
    | nil => simp at hlen
    | cons i is =>
      simpa only [toL2_ofL2, norm_ofL2_eq_gradeNorm] using
        exists_top_weakDerivative_norm_le E E₁ Q₁ hself hE₁ hQ₁ hc hgap s i is hlen
          (K (i :: is) hlen) (hK (i :: is) hlen) C A (hbound (i :: is) hlen)
          (ofL2 s v hv) (by simpa only [toL2_ofL2] using hev)
  have hreg := mem_succ_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hc hgap s K hK v hv hev
  have hb := gradeNorm_succ_le_of_top_weakDerivativeLists s v hreg _ hM htop
  have hsum : T + C * (L + A * ‖v‖) ≤ (1 + C) * (T + L + A * ‖v‖) := by
    nlinarith [mul_nonneg hC hT]
  calc
    _ ≤ Real.sqrt (((n : ℝ) + 1) ^ (s + 1)) *
        (L + c⁻¹ * (T + C * (L + A * ‖v‖))) := hb
    _ ≤ Real.sqrt (((n : ℝ) + 1) ^ (s + 1)) *
        ((T + L + A * ‖v‖) + c⁻¹ * ((1 + C) * (T + L + A * ‖v‖))) := by
      gcongr
      linarith
    _ = _ := by unfold ellipticStepConstant; ring


/-- The same coercive L² inverse satisfies the tame estimate at every order.
Both `hreg` and `hstep` are proved from the continuous differential commutators;
the constants are independent of the high profile `a` and the fixed shift `b`
(`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-r-inverse`).
`Assembly` supplies the commutators and their additive bounds from the actual
matrix representation and primitive amplitude bounds. -/
theorem inverse_gradeNorm_le_of_commutators
    (K : (s : ℕ) → (is : List (Fin n)) → is.length = s + 1 →
      PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F)
    (hK : ∀ (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1)
      (f : Torus n → F) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList is (E (toL2 s (ofSmooth s f hf)))
        (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is))) + K s is hlen (ofSmooth s f hf)))
    {C a : ℕ → ℝ} {b : ℕ} (hC : ∀ s, 0 ≤ C s) (ha : ∀ s, 0 ≤ a s)
    (ha_mono : Monotone a)
    (hbound : ∀ s is hlen u, ‖K s is hlen u‖ ≤
      C s * (‖u‖ + max 1 (a (s + 1 + b)) * ‖toL2 s u‖))
    (s : ℕ) {e : PeriodicL2 n F} (he : e ∈ periodicSobolevLevel n F s) :
    (periodicSobolevScale n F).gradeNorm s (E.inverse e) ≤
      ContinuumInverse.bootstrapConstant c
        (fun t ↦ ellipticStepConstant n (t - 1) c (C (t - 1))) s *
          ((periodicSobolevScale n F).gradeNorm s e + (1 + a (s + b)) * ‖e‖) := by
  apply ContinuumInverse.inverse_gradeNorm_le (periodicSobolevScale n F) E hc hgap
    (fun t ↦ ellipticStepConstant_nonneg n (t - 1) hc (hC (t - 1))) ha ha_mono
    (fun t ↦ mem_succ_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hc hgap t (K t) (hK t))
    _ s he
  intro t v hv hev
  have hA : 0 ≤ 1 + a (t + 1 + b) := by linarith [ha (t + 1 + b)]
  have hmax : max 1 (a (t + 1 + b)) ≤ 1 + a (t + 1 + b) :=
    max_le (by linarith [ha (t + 1 + b)]) (by linarith)
  simpa only [Nat.add_sub_cancel] using
    gradeNorm_succ_le_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hc hgap t (K t) (hK t)
      (hC t) hA (fun is hlen u ↦ (hbound t is hlen u).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right
          (mul_le_mul_of_nonneg_right hmax (norm_nonneg _)) _) (hC t))) v
      (antitone_periodicSobolevLevel (Nat.le_succ t) hv) hev

end JanetCartan.ContinuumCommutator.HigherRegularity
