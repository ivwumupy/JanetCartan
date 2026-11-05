module

public import JanetCartan.Analysis.Approximation.BallSmoothing
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.HighProfile

/-!
# The finite-moment smoother on the actual metric defect

Apply the literal Section 6 operator of `paper-v2.tex` to the source in
`main:lem:smoothing`, without replacing it by the legacy periodic cutoff.
The same tensor supplies the low bound, both independent tails, and the
normalized source. All supports and constants precede the varying data.

The generic analytic estimates retain arbitrary `t` and forcing exponent `a`.
The concrete history application uses the already proved local-target and
finite-prefix profile producer. That instance explicitly retains the legacy
history's `coefficientExponent`; it does not identify the two manuscripts'
iteration parameters or replace the existing current-mean source.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.DefectSmoothing
open BallSmoothing LocalSobolev

/-- The literal finite-moment smoother used in `paper-v2.tex`,
`main:lem:smoothing`; this is NOT the legacy periodic Fourier cutoff. -/
def finiteMomentTensor {n : ℕ} (D : LocalDomain) (R : ℝ) (m : ℕ)
    (e : MetricField n) : MetricField n :=
  affineSmoothing 0 D.coreRadius R m e

/-- Every finite accuracy has a positive integer smoothing order satisfying
the STRICT budget in `main:lem:smoothing`, even at zero accuracy. -/
theorem exists_finiteMoment_order {t : ℝ} (ht : t < 1) (Q : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ 2 * Q < (1 - t) * m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * Q / (1 - t))
  refine ⟨m + 1, by omega, ?_⟩
  have hstep : (m : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have h := (div_lt_iff₀ (sub_pos.mpr ht)).mp (hm.trans hstep)
  simpa only [mul_comm] using h

/-- The componentwise real operator preserves the symmetry of the original
signed tensor on the ball; it does not require a positivity hypothesis. -/
theorem finiteMomentTensor_isSymm {n : ℕ} (D : LocalDomain) {m : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : (2 : ℝ) * m ≤ R) {e : MetricField n}
    (he : ContinuousOn e (D.core n)) (hs : ∀ x ∈ D.core n, (e x).IsSymm)
    (x : Euclidean n) : (finiteMomentTensor D R m e x).IsSymm := by
  ext i j
  change affineSmoothing 0 D.coreRadius R m e x j i =
    affineSmoothing 0 D.coreRadius R m e x i j
  rw [affineSmoothing_matrix_apply 0 D.coreRadius_pos hm hR he,
    affineSmoothing_matrix_apply 0 D.coreRadius_pos hm hR he]
  apply congrFun (affineSmoothing_congr_closedBall 0 D.coreRadius_pos hm hR ?_) x
  intro y hy
  exact congrArg (fun M : MetricTensor n ↦ M i j) (hs y hy)

/-- The two independent tails in `main:lem:smoothing` give its exact
geometric-mean conclusion for any real accuracy and any admissible scale.
The weak budget below includes the manuscript's strict budget. -/
theorem finiteMoment_two_tail_bound {E A B δ R T t Q : ℝ} {m : ℕ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hR : 1 ≤ R) (hT : 0 ≤ T) (hTR : T ≤ R ^ t)
    (hbudget : 2 * Q ≤ (1 - t) * m)
    (hsmall : E ≤ A * δ ^ 2) (hhigh : E ≤ B * (T / R) ^ m) :
    E ≤ Real.sqrt (A * B) * δ * R ^ (-Q) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hscale : (T / R) ^ m ≤ R ^ (-2 * Q) := by
    calc
      (T / R) ^ m ≤ (R ^ t / R) ^ m :=
        pow_le_pow_left₀ (div_nonneg hT hRpos.le) (div_le_div_of_nonneg_right hTR hRpos.le) m
      _ = R ^ ((t - 1) * m) := by
        have heq : R ^ t / R = R ^ (t - 1) := by
          rw [Real.rpow_sub hRpos, Real.rpow_one]
        rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by nlinarith)
  have hhigh' := hhigh.trans (mul_le_mul_of_nonneg_left hscale hB)
  have hsquare : (R ^ (-Q)) ^ 2 = R ^ (-2 * Q) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hRpos.le]
    congr 1
    ring
  apply (sq_le_sq₀ hE (by positivity)).mp
  calc
    E ^ 2 ≤ (A * δ ^ 2) * (B * R ^ (-2 * Q)) := by
      simpa only [pow_two] using mul_le_mul hsmall hhigh' hE (mul_nonneg hA (sq_nonneg δ))
    _ = (Real.sqrt (A * B) * δ * R ^ (-Q)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hA hB), hsquare]
      ring

/-- Apply the constructed Section 6 operator to the original source profile.
Constants and one compact support are fixed before the source, scales and
smallness parameter. The high-source profile is an explicit intermediate
input; `exists_local_target_history_finiteMoment` below instantiates it from
primitive target data and genuine finite histories. -/
theorem exists_finiteMoment_source_bounds {n : ℕ} (D : LocalDomain)
    (m : ℕ) (hm : 1 ≤ m) (P : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) :
    ∃ (K : Set (Euclidean n)) (Rcut : ℝ) (L : ℕ → ℝ) (A B : ℝ),
      IsCompact K ∧ K ⊆ D.chart n ∧ 1 ≤ Rcut ∧ (2 : ℝ) * m ≤ Rcut ∧
      (∀ r, 0 ≤ L r) ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (R : ℝ), Rcut ≤ R → ∀ (e : MetricField n),
        ContDiffOn ℝ ∞ e (D.chart n) → ∀ (T δ : ℝ), 1 ≤ T →
        (∀ r, cNorm (D.core n) r e ≤ P r * T ^ r) →
        cNorm (D.core n) 0 e ≤ δ ^ 2 →
        ContDiff ℝ ∞ (finiteMomentTensor D R m e) ∧
        tsupport (finiteMomentTensor D R m e) ⊆ K ∧
        (∀ r, MemLp (iteratedFDeriv ℝ r (finiteMomentTensor D R m e)) 2 volume) ∧
        (∀ r, cNorm univ r (finiteMomentTensor D R m e) +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (finiteMomentTensor D R m e)) ≤
            L r * δ ^ 2 * R ^ r) ∧
        cNorm (D.core n) 0 (e - finiteMomentTensor D R m e) ≤ A * δ ^ 2 ∧
        cNorm (D.core n) 0 (e - finiteMomentTensor D R m e) ≤ B * (T / R) ^ m := by
  obtain ⟨K, Rcut, L, C, S, hK, hKD, hRone, hRm, hL, hC, hout, _⟩ :=
    exists_ballSmoothing (F := MetricTensor n) (0 : Euclidean n) D.coreRadius_pos
      isOpen_ball (closedBall_subset_ball D.coreRadius_lt_chartRadius) m hm
  refine ⟨K, Rcut, L, 1 + L 0, C * P m, hK, hKD, hRone, hRm, hL,
    add_nonneg zero_le_one (hL 0), mul_nonneg hC (hP m), ?_⟩
  intro R hR e he T δ _ hprofile hsmall
  let e₀ : smoothClosedBallData (F := MetricTensor n) (0 : Euclidean n) D.coreRadius :=
    ⟨e, fun x hx ↦ he.contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball D.coreRadius_lt_chartRadius hx))⟩
  obtain ⟨heq, hu, hsupp, hnorm, herr⟩ := hout R hR e₀
  rw [heq] at hu hsupp hnorm herr
  change ContDiff ℝ ∞ (finiteMomentTensor D R m e) at hu
  have hRnonneg : 0 ≤ R := zero_le_one.trans (hRone.trans hR)
  have hcompact : HasCompactSupport (finiteMomentTensor D R m e) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hlow (r : ℕ) : cNorm univ r (finiteMomentTensor D R m e) +
      cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (finiteMomentTensor D R m e)) ≤
        L r * δ ^ 2 * R ^ r := by
    exact ((hnorm r).2.trans (mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg (hL r) (pow_nonneg hRnonneg _)))).trans_eq (by ring)
  refine ⟨hu, hsupp, fun r ↦ (hnorm r).1, hlow, ?_, ?_⟩
  · have hrestrict : cNorm (D.core n) 0 (finiteMomentTensor D R m e) ≤
        cNorm univ 0 (finiteMomentTensor D R m e) := by
      apply cNorm_mono_set_of_bddAbove (subset_univ _)
      intro j _
      simpa only [image_univ] using
        ((hu.continuous_iteratedFDeriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
          (hcompact.iteratedFDeriv _).norm)
    have hsob : 0 ≤ cartesianJetNorm univ 0
        (fun j ↦ iteratedFDeriv ℝ j (finiteMomentTensor D R m e)) := Real.sqrt_nonneg _
    have hzero : cNorm univ 0 (finiteMomentTensor D R m e) ≤ L 0 * δ ^ 2 := by
      have hh := hlow 0
      simp only [pow_zero, mul_one] at hh
      linarith
    have htriangle := cNorm_add_le_of_contDiffAt (s := D.core n) (r := 0)
      (f := e) (g := -finiteMomentTensor D R m e) (isCompact_closedBall _ _)
      (fun x hx ↦ (e₀.property x hx).of_le (by simp))
      (fun _ _ ↦ hu.contDiffAt.neg.of_le (by simp))
    rw [cNorm_neg] at htriangle
    calc
      _ ≤ cNorm (D.core n) 0 e + cNorm (D.core n) 0 (finiteMomentTensor D R m e) := by
        simpa only [sub_eq_add_neg] using htriangle
      _ ≤ δ ^ 2 + L 0 * δ ^ 2 := add_le_add hsmall (hrestrict.trans hzero)
      _ = _ := by ring
  · exact (herr.trans (mul_le_mul_of_nonneg_left (hprofile m)
      (mul_nonneg hC (pow_nonneg (inv_nonneg.mpr hRnonneg) _)))).trans_eq (by
        rw [div_pow, div_eq_mul_inv, inv_pow]
        ring)

/-- Section 6's literal smoother applied to the original local target and
admissible finite history. The source profile is derived, not assumed.
This compatibility instance uses the existing history's `coefficientExponent`;
it does not identify those old iteration parameters with paper-v2 Sections 16–17.
Every support, threshold and constant precedes the target dilation and history.
The same output supplies the two tails and their arbitrary-accuracy consequence. -/
theorem exists_local_target_history_finiteMoment {n : ℕ}
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      ∃ (K : Set (Euclidean n)) (Rmin : ℝ) (L : ℕ → ℝ) (A B : ℝ),
        IsCompact K ∧ K ⊆ D.chart n ∧ 2 ≤ Rmin ∧ (2 : ℝ) * m ≤ Rmin ∧
        (∀ r, 0 ≤ L r) ∧ 0 ≤ A ∧ 0 ≤ B ∧
        ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, Rmin ≤ R₀ →
          ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
            (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
          let R := iterationScale R₀ growthExponent j
          let T := R ^ coefficientExponent
          let e := historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u
          ∀ δ : ℝ, 0 ≤ δ → cNorm (D.core n) 0 e ≤ δ ^ 2 →
          let eR := finiteMomentTensor D R m e
          ContDiff ℝ ∞ eR ∧ tsupport eR ⊆ K ∧
          (∀ r, MemLp (iteratedFDeriv ℝ r eR) 2 volume) ∧
          (∀ r, cNorm univ r eR +
            cartesianJetNorm univ r (fun a ↦ iteratedFDeriv ℝ a eR) ≤ L r * δ ^ 2 * R ^ r) ∧
          cNorm (D.core n) 0 (e - eR) ≤ A * δ ^ 2 ∧
          cNorm (D.core n) 0 (e - eR) ≤ B * (T / R) ^ m ∧
          ∀ Q : ℝ, 2 * Q ≤ (1 - coefficientExponent) * m →
            cNorm (D.core n) 0 (e - eR) ≤ Real.sqrt (A * B) * δ * R ^ (-Q) := by
  obtain ⟨s₀, hs₀, hs₁, hmaps, P, hP, hp⟩ :=
    exists_historyDefect_derivative_profile D G hρ hU h0 hg hg0 horder
  obtain ⟨K, Rcut, L, A, B, hK, hKD, _, hRm, hL, hA, hB, hb⟩ :=
    exists_finiteMoment_source_bounds (n := n) D m hm P hP
  refine ⟨s₀, hs₀, hs₁, K, max 2 Rcut, L, A, B, hK, hKD,
    le_max_left _ _, hRm.trans (le_max_right _ _), hL, hA, hB, ?_⟩
  intro s hs R₀ hR₀ j u ell hu
  dsimp only
  intro δ hδ hsmall
  let R := iterationScale R₀ growthExponent j
  have hR02 : 2 ≤ R₀ := (le_max_left _ _).trans hR₀
  have hR0R : R₀ ≤ R := Real.self_le_rpow_of_one_le (by linarith)
    (one_le_pow₀ (by norm_num [growthExponent]))
  have hR1 : 1 ≤ R := (by linarith : 1 ≤ R₀).trans hR0R
  have hT : 1 ≤ R ^ coefficientExponent :=
    Real.one_le_rpow hR1 (by norm_num [coefficientExponent])
  have ht : ContDiffOn ℝ ∞ (fun x ↦ g ((s * ρ) • x)) (D.chart n) :=
    hg.comp (contDiff_id.const_smul (s * ρ)).contDiffOn
      (fun x hx ↦ hmaps s hs x (Metric.ball_subset_closedBall hx))
  obtain ⟨huR, hsupp, hmem, hlow, hsmall', hhigh⟩ :=
    hb R (((le_max_right _ _).trans hR₀).trans hR0R) _
      (contDiffOn_historyDefect ht G.contDiff hu) (R ^ coefficientExponent) δ hT
      (hp s hs R₀ hR02 j u ell hu) hsmall
  refine ⟨huR, hsupp, hmem, hlow, hsmall', hhigh, ?_⟩
  intro Q hQ
  exact finiteMoment_two_tail_bound (cNorm_nonneg _ _ _) hA hB hδ hR1
    (zero_le_one.trans hT) le_rfl hQ hsmall' hhigh

/-- The normalized source following `main:eq:smoothing-combined` is the
SAME finite-moment output divided by `(δ R^a)^2`. Here `a` is arbitrary;
no old forcing exponent is substituted for the paper-v2 parameter.
The proof uses real linearity of the constructed operator, not an assumed
normalized-source estimate or a different smoothing choice. -/
theorem exists_finiteMoment_normalized_bounds {n : ℕ} (D : LocalDomain)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (Rcut : ℝ) (L : ℕ → ℝ), 1 ≤ Rcut ∧ (2 : ℝ) * m ≤ Rcut ∧
      (∀ r, 0 ≤ L r) ∧ ∀ R : ℝ, Rcut ≤ R → ∀ e : MetricField n,
        ContDiffOn ℝ ∞ e (D.chart n) → ∀ δ : ℝ, 0 < δ →
        cNorm (D.core n) 0 e ≤ δ ^ 2 → ∀ a : ℝ,
        let source := ((δ * R ^ a) ^ 2)⁻¹ • finiteMomentTensor D R m e
        ∀ r, cNorm univ r source +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j source) ≤
            L r * R ^ ((r : ℝ) - 2 * a) := by
  obtain ⟨_, Rcut, L, _, S, _, _, hRone, hRm, hL, _, hout, _⟩ :=
    exists_ballSmoothing (F := MetricTensor n) (0 : Euclidean n) D.coreRadius_pos
      isOpen_ball (closedBall_subset_ball D.coreRadius_lt_chartRadius) m hm
  refine ⟨Rcut, L, hRone, hRm, hL, ?_⟩
  intro R hR e he δ hδ hsmall a
  dsimp only
  intro r
  let e₀ : smoothClosedBallData (F := MetricTensor n) (0 : Euclidean n) D.coreRadius :=
    ⟨e, fun x hx ↦ he.contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball D.coreRadius_lt_chartRadius hx))⟩
  let q : ℝ := ((δ * R ^ a) ^ 2)⁻¹
  have hRpos : 0 < R := zero_lt_one.trans_le (hRone.trans hR)
  have hq : 0 < q := by dsimp [q]; positivity
  have hcancel : q * δ ^ 2 = R ^ (-(2 * a)) := by
    have hp : (R ^ a) ^ 2 = R ^ (2 * a) := by
      rw [mul_comm 2, Real.rpow_mul hRpos.le, Real.rpow_two]
    dsimp [q]
    rw [mul_pow, hp, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hδ.ne'),
      mul_one, Real.rpow_neg hRpos.le]
  have heq := (hout R hR e₀).1
  have hsame : S R hR (q • e₀) = q • finiteMomentTensor D R m e := by
    rw [map_smul, heq]
    rfl
  have hnorm := ((hout R hR (q • e₀)).2.2.2.1 r).2
  rw [hsame] at hnorm
  have hsource : cNorm (D.core n) 0 (q • e) ≤ R ^ (-(2 * a)) := by
    rw [cNorm_smul_of_contDiffAt (s := D.core n) (f := e) (r := 0)
        q (fun x hx ↦ (e₀.property x hx).of_le (by simp)),
      Real.norm_eq_abs, abs_of_pos hq]
    exact (mul_le_mul_of_nonneg_left hsmall hq.le).trans_eq hcancel
  calc
    _ ≤ L r * R ^ r * cNorm (D.core n) 0 (q • e) := hnorm
    _ ≤ L r * R ^ r * R ^ (-(2 * a)) :=
      mul_le_mul_of_nonneg_left hsource (mul_nonneg (hL r) (pow_nonneg hRpos.le _))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast R r, ← Real.rpow_add hRpos, sub_eq_add_neg]

end JanetCartan.DefectSmoothing
