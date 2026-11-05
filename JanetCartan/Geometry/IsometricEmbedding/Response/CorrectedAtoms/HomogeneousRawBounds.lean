module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RawFiniteBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RawTame
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointDensity

/-!
# Homogeneous raw bounds on the original scalar span

For `app:ch_response:eq:current-density-lipschitz`, normalize scalar differences
inside the original primitive class and apply the retained finite budgets.
The class must have a fixed positive margin `m < Mᵣ`; no domain, flow, reference
or scalar class is reselected. A limiting inequality in a positive scalar
handles the kernel of the initial-data seminorm without treating it as a norm.
The all-order variant retains one high scalar norm and multiplies the high
immersion norm by only the fixed order-fifteen scalar seminorm. Its constants
use fixed low geometry and precede all varying fields and histories.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.CorrectedAtoms
open PrimarySourceAdmission

/-- Constant base scalar budget for `app:ch_response:eq:current-density-lipschitz`. -/
private theorem cNorm_const_le {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set D) (s : ℕ) (v : E) : cNorm K s (fun _ ↦ v) ≤ ‖v‖ := by
  induction s with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨x, _, rfl⟩; exact le_rfl) (norm_nonneg _)
  | succ s ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun x : D ↦ ‖iteratedFDeriv ℝ (s+1) (fun _ : D ↦ v) x‖) '' K) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

/-- The lower constant itself belongs to the original primitive class. Thus the
initializer's positivity continuation provides the two nonzero vectors on its
own full flow domain, also when bounding a sign-changing element of the span
(`app:ch_waves:thm:leading`, `app:ch_response:eq:current-density-lipschitz`). -/
theorem lowerConstant_mem_primitiveInitialScalars {n : ℕ} (z₀ : Euclidean 3)
    (R : ℝ) {M m : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) :
    (fun _ ↦ m) ∈ primitiveInitialScalars (n := n) z₀ R M m := by
  refine ⟨contDiffOn_const, ?_, fun _ _ ↦ le_rfl⟩
  exact (cNorm_const_le _ 14 m).trans (by simpa only [Real.norm_eq_abs, abs_of_nonneg hm] using hmM)

/-- Smoothness of the original span on its unchanged initial chart
(`app:ch_response:cor:current-atoms`). -/
private theorem contDiffOn_initialScalarSpan {n : ℕ} {z₀ : Euclidean 3} {R M m : ℝ}
    (r : initialScalarSpan (n := n) z₀ R M m) :
    ContDiffOn ℝ ∞ (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) := by
  rcases r with ⟨r, hr⟩
  change ContDiffOn ℝ ∞ r _
  induction hr using Submodule.span_induction with
  | mem r hr => exact hr.1
  | zero => exact contDiffOn_const
  | add r s _ _ hr hs => exact hr.add hs
  | smul a r _ hr => exact hr.const_smul a

/-- A bounded primitive slice of the original scalar span controls its linear
images homogeneously, including the seminorm kernel. The finite budget is the
one consumed by `app:ch_response:eq:current-density-lipschitz`. -/
private theorem cNorm_scalarSpanLinearMap_le
    {n : ℕ} {z₀ : Euclidean 3} {R M m : ℝ}
    (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < M)
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : initialScalarSpan (n := n) z₀ R M m →ₗ[ℝ] (D → E))
    {K : Set D} (hK : IsCompact K) (s d : ℕ) (hd : 14 ≤ d)
    (hreg : ∀ r, ∀ x ∈ K, ContDiffAt ℝ s (L r) x)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ r : initialScalarSpan (n := n) z₀ R M m,
      (r : Euclidean (n - 1) × Euclidean 3 → ℝ) ∈ primitiveInitialScalars z₀ R M m →
      cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) d
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ) ≤ M → cNorm K s (L r) ≤ C)
    (r : initialScalarSpan (n := n) z₀ R M m) :
    cNorm K s (L r) ≤ (4 * C / (M - m)) *
      cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) d
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ) := by
  let I := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
  let p := cNorm I d (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
  let b := (M + m) / 2
  let δ := (M - m) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hbM : b ≤ M := by dsimp [b]; linarith
  have hbm : m ≤ b := by dsimp [b]; linarith
  have hbδ : b + δ = M := by dsimp [b, δ]; ring
  have hbδm : b - δ = m := by dsimp [b, δ]; ring
  have hconst (k : ℕ) : cNorm I k (fun _ ↦ b) ≤ b := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb] using cNorm_const_le I k b
  have hbase : (fun _ : Euclidean (n - 1) × Euclidean 3 ↦ b) ∈
      primitiveInitialScalars z₀ R M m :=
    ⟨contDiffOn_const, (hconst 14).trans hbM, fun _ _ ↦ hbm⟩
  let base : initialScalarSpan (n := n) z₀ R M m := ⟨_, Submodule.subset_span hbase⟩
  have hbaseBound : cNorm K s (L base) ≤ C := hbound base hbase ((hconst d).trans hbM)
  have hI : I ⊆ ball ((0 : Euclidean (n - 1)), z₀) (R / 4) :=
    closedBall_subset_ball (by linarith)
  have hrAt (x) (hx : x ∈ I) :
      ContDiffAt ℝ d (r : Euclidean (n - 1) × Euclidean 3 → ℝ) x :=
    ((contDiffOn_initialScalarSpan r).contDiffAt (isOpen_ball.mem_nhds (hI hx))).of_le (by simp)
  have hp : 0 ≤ p := cNorm_nonneg _ _ _
  have htbound (t : ℝ) (ht : p < t) : cNorm K s (L r) ≤ (4 * C / (M - m)) * t := by
    have ht0 : 0 < t := hp.trans_lt ht
    have hscale : 0 < δ / t := div_pos hδ ht0
    have hpδ : (δ / t) * p ≤ δ := by
      have hh := mul_le_mul_of_nonneg_left ht.le hscale.le
      simpa only [div_mul_cancel₀ _ ht0.ne'] using hh
    let q := base + (δ / t) • r
    have hqnorm : cNorm I d (q : Euclidean (n - 1) × Euclidean 3 → ℝ) ≤ M := by
      change cNorm I d ((fun _ ↦ b) + (δ / t) •
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)) ≤ M
      apply (cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
        (fun _ _ ↦ contDiffAt_const) (fun x hx ↦ (hrAt x hx).const_smul (δ / t))).trans
      change cNorm I d (fun _ ↦ b) + cNorm I d
        ((δ / t) • (r : Euclidean (n - 1) × Euclidean 3 → ℝ)) ≤ M
      rw [cNorm_smul_of_contDiffAt _ hrAt, Real.norm_eq_abs, abs_of_pos hscale]
      exact (add_le_add (hconst d) hpδ).trans_eq hbδ
    have hq : (q : Euclidean (n - 1) × Euclidean 3 → ℝ) ∈
        primitiveInitialScalars z₀ R M m := by
      refine ⟨contDiffOn_initialScalarSpan q, (cNorm_mono_order hd).trans hqnorm, ?_⟩
      intro x hx
      have hrx : ‖(r : Euclidean (n - 1) × Euclidean 3 → ℝ) x‖ ≤ p := by
        simpa only [norm_iteratedFDeriv_zero] using
          norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _) hrAt
            (ball_subset_closedBall hx) (Nat.zero_le d)
      have hsx : ‖(δ / t) * (r : Euclidean (n - 1) × Euclidean 3 → ℝ) x‖ ≤ δ := by
        rw [norm_mul, Real.norm_eq_abs (δ / t), abs_of_pos hscale]
        exact (mul_le_mul_of_nonneg_left hrx hscale.le).trans hpδ
      have hl := (abs_le.mp hsx).1
      change m ≤ b + (δ / t) * (r : Euclidean (n - 1) × Euclidean 3 → ℝ) x
      linarith
    have hqBound := hbound q hq hqnorm
    have hdiff : cNorm K s (L q - L base) ≤ 2 * C := by
      have hadd := cNorm_add_le_of_contDiffAt hK (hreg q)
        (fun x hx ↦ (hreg base x hx).neg)
      change cNorm K s (L q + -(L base)) ≤ cNorm K s (L q) + cNorm K s (-(L base)) at hadd
      rw [cNorm_neg] at hadd
      have hsum : cNorm K s (L q) + cNorm K s (L base) ≤ 2 * C := by linarith
      simpa only [sub_eq_add_neg] using hadd.trans hsum
    have heq : L q - L base = (δ / t) • L r := by
      dsimp [q]
      rw [map_add, map_smul]
      abel
    rw [heq, cNorm_smul_of_contDiffAt _ (hreg r), Real.norm_eq_abs, abs_of_pos hscale] at hdiff
    have he : (4 * C / (M - m)) * t = 2 * C / (δ / t) := by
      dsimp [δ]
      field_simp
      ring
    rw [he]
    exact (le_div_iff₀ hscale).mpr (by nlinarith [hdiff])
  have hfactor : 0 < 4 * C / (M - m) := by positivity
  rw [mul_comm]
  apply (div_le_iff₀ hfactor).mp
  apply le_of_forall_gt_imp_ge_of_dense
  intro t ht
  exact (div_le_iff₀ hfactor).mpr (by nlinarith [htbound t ht])

/-- Scalar normalization preserves one high initial norm and multiplies the
high geometry cost by only the fixed low initial seminorm. It stays inside
the original primitive scalar class, including its seminorm kernel
(`app:ch_response:eq:current-atomic-offset`). -/
private theorem cNorm_scalarSpanLinearMap_oneHigh_le
    {n : ℕ} {z₀ : Euclidean 3} {R M m : ℝ}
    (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < M)
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : initialScalarSpan (n := n) z₀ R M m →ₗ[ℝ] (D → E))
    {K : Set D} (hK : IsCompact K) (s d : ℕ)
    (hreg : ∀ r, ∀ x ∈ K, ContDiffAt ℝ s (L r) x)
    {C H : ℝ} (hC : 0 < C) (hH : 0 ≤ H)
    (hbound : ∀ r : initialScalarSpan (n := n) z₀ R M m,
      (r : Euclidean (n-1) × Euclidean 3 → ℝ) ∈ primitiveInitialScalars z₀ R M m →
      cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) 15 (r : Euclidean (n-1) × Euclidean 3 → ℝ) ≤ M →
      cNorm K s (L r) ≤ C * (1 + H +
        cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) d (r : Euclidean (n-1) × Euclidean 3 → ℝ)))
    (r : initialScalarSpan (n := n) z₀ R M m) :
    cNorm K s (L r) ≤ C * (1 + 4 * (1 + M) / (M-m)) *
      (cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) d (r : Euclidean (n-1) × Euclidean 3 → ℝ) +
        (1 + H) * cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) 15 (r : Euclidean (n-1) × Euclidean 3 → ℝ)) := by
  let I := closedBall ((0 : Euclidean (n-1)), z₀) (R/8)
  let p := cNorm I 15 (r : Euclidean (n-1) × Euclidean 3 → ℝ)
  let q := cNorm I d (r : Euclidean (n-1) × Euclidean 3 → ℝ)
  let b := (M+m)/2
  let δ := (M-m)/2
  let A := C * (1 + 4 * (1+M)/(M-m))
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hM : 0 ≤ M := hm.trans hgap.le
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hbM : b ≤ M := by dsimp [b]; linarith
  have hbm : m ≤ b := by dsimp [b]; linarith
  have hbδ : b+δ = M := by dsimp [b,δ]; ring
  have hbδm : b-δ = m := by dsimp [b,δ]; ring
  have hp : 0 ≤ p := cNorm_nonneg _ _ _
  have hq : 0 ≤ q := cNorm_nonneg _ _ _
  have hA : 0 < A := by dsimp [A]; positivity
  have hCA : C ≤ A := by
    dsimp [A]
    have : 0 ≤ 4 * (1+M)/(M-m) := by positivity
    nlinarith only [hC, this]
  have hDA : 2 * C * (1+M) / δ ≤ A := by
    have he : 2 * C * (1+M) / δ = C * (4 * (1+M)/(M-m)) := by
      dsimp [δ]
      field_simp [ne_of_gt (sub_pos.mpr hgap)]
      ring
    rw [he]
    dsimp [A]
    nlinarith only [hC]
  have hconst (k : ℕ) : cNorm I k (fun _ ↦ b) ≤ b := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb] using cNorm_const_le I k b
  have hbase : (fun _ : Euclidean (n-1) × Euclidean 3 ↦ b) ∈ primitiveInitialScalars z₀ R M m :=
    ⟨contDiffOn_const, (hconst 14).trans hbM, fun _ _ ↦ hbm⟩
  let base : initialScalarSpan (n := n) z₀ R M m := ⟨_, Submodule.subset_span hbase⟩
  have hbaseBound : cNorm K s (L base) ≤ C * (1+H+b) :=
    (hbound base hbase ((hconst 15).trans hbM)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hconst d]) hC.le)
  have hI : I ⊆ ball ((0 : Euclidean (n-1)), z₀) (R/4) := closedBall_subset_ball (by linarith)
  have hrAt (k : ℕ) (x) (hx : x ∈ I) : ContDiffAt ℝ k (r : Euclidean (n-1) × Euclidean 3 → ℝ) x :=
    ((contDiffOn_initialScalarSpan r).contDiffAt (isOpen_ball.mem_nhds (hI hx))).of_le (by simp)
  have htbound (t : ℝ) (ht : p < t) : cNorm K s (L r) ≤ A * q + A * (1+H) * t := by
    have ht0 : 0 < t := hp.trans_lt ht
    have hscale : 0 < δ/t := div_pos hδ ht0
    have hpδ : (δ/t)*p ≤ δ := by
      have hh := mul_le_mul_of_nonneg_left ht.le hscale.le
      simpa only [div_mul_cancel₀ _ ht0.ne'] using hh
    let u := base + (δ/t) • r
    have huNorm (k : ℕ) : cNorm I k (u : Euclidean (n-1) × Euclidean 3 → ℝ) ≤ b + (δ/t)*cNorm I k (r : Euclidean (n-1) × Euclidean 3 → ℝ) := by
      change cNorm I k ((fun _ ↦ b) + (δ/t) • (r : Euclidean (n-1) × Euclidean 3 → ℝ)) ≤ _
      apply (cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
        (fun _ _ ↦ contDiffAt_const) (fun x hx ↦ (hrAt k x hx).const_smul (δ/t))).trans
      change cNorm I k (fun _ ↦ b) +
        cNorm I k ((δ/t) • (r : Euclidean (n-1) × Euclidean 3 → ℝ)) ≤ _
      rw [cNorm_smul_of_contDiffAt _ (hrAt k), Real.norm_eq_abs, abs_of_pos hscale]
      linarith only [hconst k]
    have huLow : cNorm I 15 (u : Euclidean (n-1) × Euclidean 3 → ℝ) ≤ M := by
      linarith only [huNorm 15, hpδ, hbδ]
    have hu : (u : Euclidean (n-1) × Euclidean 3 → ℝ) ∈ primitiveInitialScalars z₀ R M m := by
      refine ⟨contDiffOn_initialScalarSpan u, (cNorm_mono_order (by omega : 14 ≤ 15)).trans huLow, ?_⟩
      intro x hx
      have hrx : ‖(r : Euclidean (n-1) × Euclidean 3 → ℝ) x‖ ≤ p := by
        simpa only [norm_iteratedFDeriv_zero] using norm_iteratedFDeriv_le_cNorm_of_contDiffAt
          (isCompact_closedBall _ _) (hrAt 15) (ball_subset_closedBall hx) (Nat.zero_le 15)
      have hsx : ‖(δ/t) * (r : Euclidean (n-1) × Euclidean 3 → ℝ) x‖ ≤ δ := by
        rw [norm_mul, Real.norm_eq_abs (δ/t), abs_of_pos hscale]
        exact (mul_le_mul_of_nonneg_left hrx hscale.le).trans hpδ
      have hl := (abs_le.mp hsx).1
      change m ≤ b + (δ/t) * (r : Euclidean (n-1) × Euclidean 3 → ℝ) x
      linarith only [hl, hbδm]
    have huBound : cNorm K s (L u) ≤ C * (1+H+(b+(δ/t)*q)) := (hbound u hu huLow).trans
      (mul_le_mul_of_nonneg_left (by linarith only [huNorm d]) hC.le)
    have hdiff := cNorm_add_le_of_contDiffAt hK (hreg u) (fun x hx ↦ (hreg base x hx).neg)
    change cNorm K s (L u + -(L base)) ≤ cNorm K s (L u) + cNorm K s (-(L base)) at hdiff
    rw [cNorm_neg] at hdiff
    have heq : L u + -(L base) = (δ/t) • L r := by
      dsimp [u]; rw [map_add, map_smul]; abel
    rw [heq, cNorm_smul_of_contDiffAt _ (hreg r), Real.norm_eq_abs, abs_of_pos hscale] at hdiff
    have hbound' : (δ/t) * cNorm K s (L r) ≤ C * (2*(1+H+b) + (δ/t)*q) := by
      nlinarith only [hdiff, huBound, hbaseBound]
    have hdiv : cNorm K s (L r) ≤ C*q + (2*C*(1+H+b)/δ)*t := by
      apply (mul_le_mul_iff_right₀ hscale).mp
      have hEq : (δ/t) * (C*q + (2*C*(1+H+b)/δ)*t) =
          C * (2*(1+H+b) + (δ/t)*q) := by field_simp [hδ.ne', ht0.ne']; ring
      rw [hEq]
      exact hbound'
    apply hdiv.trans
    have hgeom : 1+H+b ≤ (1+M)*(1+H) := by nlinarith only [hbM, hH, hM]
    have hcost : 2*C*(1+H+b)/δ ≤ A*(1+H) := by
      calc
        _ ≤ (2*C*((1+M)*(1+H)))/δ := by gcongr
        _ = (2*C*(1+M)/δ)*(1+H) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDA (by linarith)
    exact add_le_add (mul_le_mul_of_nonneg_right hCA hq)
      (mul_le_mul_of_nonneg_right hcost ht0.le)
  have hcoeff : 0 < A*(1+H) := mul_pos hA (by linarith)
  have hdense : (cNorm K s (L r)-A*q)/(A*(1+H)) ≤ p := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    apply (div_le_iff₀ hcoeff).mpr
    linarith only [htbound t ht]
  have hh := (div_le_iff₀ hcoeff).mp hdense
  change cNorm K s (L r) ≤ A * (q+(1+H)*p)
  nlinarith only [hh]

open RawPrimary RawPrimary.FiniteJetSlices RawPrimary.AmplitudeGrades
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer AmbientResponse ProjectedStressFrame

/-- Homogeneous leading and raw-error bounds on the SAME initial scalar span.
The hypotheses are the retained leading/correction budgets from
`RetainedCorrection.exists_finite_retained_corrected_family_before_geometry`;
the finite polynomial estimate and scalar normalization discharge the amplitude
bounds. Constants are fixed before the immersion, flows, scalar and frequency.
The joint order `s` uses only initial and immersion jets through `s+16`.
Consumer: `app:ch_response:eq:current-density-lipschitz`. -/
theorem exists_retainedRawDensity_homogeneousBounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (z₀ : Euclidean 3) {R Mᵣ m : ℝ} (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < Mᵣ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ C₀ Kpr : ℕ → ℝ, (∀ j, 0 < C₀ j) ∧ (∀ j, 0 < Kpr j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      (∀ w ∈ Ω, w.1 ∈ U) → (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) →
      ∀ s : ℕ,
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ j ≤ s + 1,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) →
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ j ≤ s + 2,
        cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ j * (1 + cNorm K (j + 14) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) →
      (∀ j ≤ s + 16, cNorm K j F ≤ AF j) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      cNorm (closedBall a ρ) s (fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤
        C₀ s * cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (s + 16)
          (r : Euclidean (n - 1) × Euclidean 3 → ℝ) ∧
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r τ -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ Kpr s * τ *
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (s + 16)
            (r : Euclidean (n - 1) × Euclidean 3 → ℝ) := by
  let I := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
  obtain ⟨C, hC, hfinite⟩ := exists_retainedRawDensity_finiteBounds (N := N) T a hρ
    hK hKU hball hspace hphase I hγ hκ AF (fun _ ↦ Mᵣ) E Γ hAF
    (fun _ ↦ hm.trans hgap.le) hE hΓ
  refine ⟨fun s ↦ 8 * C s / (Mᵣ - m), fun s ↦ 4 * C s / (Mᵣ - m),
    fun s ↦ div_pos (mul_pos (by norm_num) (hC s)) (sub_pos.mpr hgap),
    fun s ↦ div_pos (mul_pos (by norm_num) (hC s)) (sub_pos.mpr hgap), ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y Ω hΩ hflow hspaceΩ hphaseΩ hnonzero hα s hleadBudget hcorrectionBudget hpF τ hτ hτ₁ r
  have hJO : closedBall a ρ ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hflow
  obtain ⟨ψ, hψ, _hrange, _hc, hψO, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff (isCompact_closedBall a ρ) hΩ hJO
  obtain ⟨Apr, A₀, hmaps⟩ := exists_cutoffRawAmplitudeLinearMaps T Q F row col Φ Y
    hΩ hspaceΩ hphaseΩ hF hi hrank hnonzero hα ψ hψO hτ.ne'
  have hαspan (b : initialScalarSpan (n := n) z₀ R Mᵣ m) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα b.property
  have he (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      (Apr b =ᶠ[𝓝 w] fullDerivativeAmplitude T Q F row col Φ Y b τ) ∧
      (A₀ b =ᶠ[𝓝 w] fullLeadingPrincipalMatrix T Q F row col Φ Y b) := by
    rw [(hmaps b).1, (hmaps b).2]
    have hh (f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Matrix (Fin N) (Fin n) ℂ) :
        (fun y ↦ ψ y • f y) =ᶠ[𝓝 w] f := by
      filter_upwards [isOpen_interior.mem_nhds (hplateau hw)] with y hy
      have hp := (interior_subset : interior {x | ψ x = 1} ⊆ {x | ψ x = 1}) hy
      change ψ y = 1 at hp
      simp only [hp, one_smul]
    exact ⟨hh _, hh _⟩
  have hlreg (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      ContDiffAt ℝ s (A₀ b) w := by
    rw [(hmaps b).2]
    exact (hψ.contDiffAt.smul ((contDiffOn_retainedLeadingPrincipalMatrix T Q F row col Φ Y b
      hΩ hspaceΩ hphaseΩ hF hi hrank (hαspan b)).contDiffAt (hΩ.mem_nhds (hJO hw)))).of_le (by simp)
  have hpreg (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      ContDiffAt ℝ s (Apr b) w := by
    rw [(hmaps b).1]
    exact (hψ.contDiffAt.smul ((contDiffOn_retainedDerivativeAmplitude T Q F row col Φ Y b
      hΩ hspaceΩ hphaseΩ hF hi hrank (hαspan b) hnonzero hτ.ne').contDiffAt
        (hΩ.mem_nhds (hJO hw)))).of_le (by simp)
  have hb (b : initialScalarSpan (n := n) z₀ R Mᵣ m)
      (hb : (b : Euclidean (n - 1) × Euclidean 3 → ℝ) ∈ primitiveInitialScalars z₀ R Mᵣ m)
      (hp : cNorm I (s + 16) (b : Euclidean (n - 1) × Euclidean 3 → ℝ) ≤ Mᵣ) :
      cNorm (closedBall a ρ) s (A₀ b) ≤ 2 * C s ∧
      cNorm (closedBall a ρ) s ((Apr - A₀) b) ≤ τ * C s := by
    rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ (he b w hw).2) s,
      LinearMap.sub_apply, GeometricProfile.cNorm_eq_of_eventuallyEq
        (fun w hw ↦ (he b w hw).1.sub (he b w hw).2) s]
    exact hfinite F hF hi hrank hmetric hnormal hlow row col Φ Y b Ω hΩ hflow
      (contDiffOn_fullLeadingCovector T Q F row col Φ Y b hspaceΩ hphaseΩ (hα b hb))
      (contDiffOn_fullCorrectionCovector_of_leading_outputs T Q F row col Φ Y b
        hΩ hspaceΩ hphaseΩ hF hi (hα b hb) hnonzero)
      s (hleadBudget b hb) (hcorrectionBudget b hb) hpF
      (fun j hj ↦ (cNorm_mono_order hj).trans hp) τ hτ hτ₁ s le_rfl
  have hl := cNorm_scalarSpanLinearMap_le hR hm hgap A₀ (isCompact_closedBall a ρ)
    s (s + 16) (by omega) hlreg (mul_pos (by norm_num) (hC s))
    (fun b hb' hp ↦ (hb b hb' hp).1) r
  have hp := cNorm_scalarSpanLinearMap_le hR hm hgap (Apr - A₀) (isCompact_closedBall a ρ)
    s (s + 16) (by omega) (fun b w hw ↦ (hpreg b w hw).sub (hlreg b w hw))
    (mul_pos hτ (hC s)) (fun b hb' hp ↦ (hb b hb' hp).2) r
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ (he r w hw).2) s] at hl
  rw [LinearMap.sub_apply, GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun w hw ↦ (he r w hw).1.sub (he r w hw).2) s] at hp
  constructor
  · convert hl using 1
    ring
  · convert hp using 1
    ring

/-- All-order homogeneous raw bounds on the original scalar span, with one
high scalar norm and the actual high geometry cost multiplying only the fixed
low seminorm. The constants precede immersion, histories, flows and frequency.
This supplies the raw/leading inputs of `PreparedDiscrepancy.TameFamily` and
the fixed-shift offset of `app:ch_response:cor:current-atoms`. -/
theorem exists_retainedRawAmplitude_homogeneousOneHigh_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (z₀ : Euclidean 3) {R Mᵣ m : ℝ} (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < Mᵣ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (M : ℝ) (hM : 0 ≤ M) (E Γ : ℕ → ℝ)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      (∀ w ∈ Ω, w.1 ∈ U) → (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) →
      cNorm K 15 F ≤ M →
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) →
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ j,
        cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ j * (1 + cNorm K (j + 14) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ s,
      ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      let I := closedBall ((0 : Euclidean (n-1)), z₀) (R/8)
      let H := cNorm I (s+16) (r : _ → ℝ) + (1 + cNorm K (s+16) F) * cNorm I 15 (r : _ → ℝ)
      cNorm (closedBall a ρ) s (fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ C s * H ∧
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r τ) ≤ 2 * C s * H ∧
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r τ -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ τ * C s * H := by
  let I := closedBall ((0 : Euclidean (n-1)), z₀) (R/8)
  obtain ⟨C, hC, hraw⟩ := exists_retainedRawAmplitude_oneHigh_bounds (N := N) T a hρ
    hK hKU hball hspace hphase I hγ hκ M Mᵣ hM (hm.trans hgap.le) E Γ hE hΓ
  let D := fun s ↦ C s * (1 + 4 * (1+Mᵣ)/(Mᵣ-m))
  have hD (s) : 0 < D s := by
    have := hC s
    have : 0 ≤ Mᵣ := hm.trans hgap.le
    dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y Ω hΩ hflow hspaceΩ hphaseΩ hnonzero hα hFM hleadBudget hcorrectionBudget τ hτ hτ₁ s r
  have hJO : closedBall a ρ ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hflow
  obtain ⟨ψ, hψ, _hrange, _hc, hψO, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff (isCompact_closedBall a ρ) hΩ hJO
  obtain ⟨Apr, A₀, hmaps⟩ := exists_cutoffRawAmplitudeLinearMaps T Q F row col Φ Y
    hΩ hspaceΩ hphaseΩ hF hi hrank hnonzero hα ψ hψO hτ.ne'
  have hαspan (b : initialScalarSpan (n := n) z₀ R Mᵣ m) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα b.property
  have he (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      (Apr b =ᶠ[𝓝 w] fullDerivativeAmplitude T Q F row col Φ Y b τ) ∧
      (A₀ b =ᶠ[𝓝 w] fullLeadingPrincipalMatrix T Q F row col Φ Y b) := by
    rw [(hmaps b).1, (hmaps b).2]
    have hh (f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Matrix (Fin N) (Fin n) ℂ) :
        (fun y ↦ ψ y • f y) =ᶠ[𝓝 w] f := by
      filter_upwards [isOpen_interior.mem_nhds (hplateau hw)] with y hy
      have hp := (interior_subset : interior {x | ψ x = 1} ⊆ {x | ψ x = 1}) hy
      change ψ y = 1 at hp
      simp only [hp, one_smul]
    exact ⟨hh _, hh _⟩
  have hlreg (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      ContDiffAt ℝ s (A₀ b) w := by
    rw [(hmaps b).2]
    exact (hψ.contDiffAt.smul ((contDiffOn_retainedLeadingPrincipalMatrix T Q F row col Φ Y b
      hΩ hspaceΩ hphaseΩ hF hi hrank (hαspan b)).contDiffAt (hΩ.mem_nhds (hJO hw)))).of_le (by simp)
  have hpreg (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      ContDiffAt ℝ s (Apr b) w := by
    rw [(hmaps b).1]
    exact (hψ.contDiffAt.smul ((contDiffOn_retainedDerivativeAmplitude T Q F row col Φ Y b
      hΩ hspaceΩ hphaseΩ hF hi hrank (hαspan b) hnonzero hτ.ne').contDiffAt
        (hΩ.mem_nhds (hJO hw)))).of_le (by simp)
  have hb (b : initialScalarSpan (n := n) z₀ R Mᵣ m)
      (hb : (b : Euclidean (n-1) × Euclidean 3 → ℝ) ∈ primitiveInitialScalars z₀ R Mᵣ m)
      (hp : cNorm I 15 (b : _ → ℝ) ≤ Mᵣ) :
      cNorm (closedBall a ρ) s (A₀ b) ≤ C s * (1 + cNorm K (s+16) F + cNorm I (s+16) (b : _ → ℝ)) ∧
      cNorm (closedBall a ρ) s ((Apr-A₀) b) ≤ (τ*C s) * (1 + cNorm K (s+16) F + cNorm I (s+16) (b : _ → ℝ)) := by
    rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ (he b w hw).2) s,
      LinearMap.sub_apply, GeometricProfile.cNorm_eq_of_eventuallyEq
        (fun w hw ↦ (he b w hw).1.sub (he b w hw).2) s]
    have hh := hraw F hF hi hrank hmetric hnormal hlow row col Φ Y b Ω hΩ hflow
      (contDiffOn_fullLeadingCovector T Q F row col Φ Y b hspaceΩ hphaseΩ (hα b hb))
      (contDiffOn_fullCorrectionCovector_of_leading_outputs T Q F row col Φ Y b
        hΩ hspaceΩ hphaseΩ hF hi (hα b hb) hnonzero)
      hFM hp (hleadBudget b hb) (hcorrectionBudget b hb) τ hτ hτ₁ s
    exact ⟨hh.1, hh.2.2⟩
  have hl := cNorm_scalarSpanLinearMap_oneHigh_le hR hm hgap A₀ (isCompact_closedBall a ρ)
    s (s+16) hlreg (hC s) (cNorm_nonneg K (s+16) F) (fun b hb' hp ↦ (hb b hb' hp).1) r
  have hp := cNorm_scalarSpanLinearMap_oneHigh_le hR hm hgap (Apr-A₀) (isCompact_closedBall a ρ)
    s (s+16) (fun b w hw ↦ (hpreg b w hw).sub (hlreg b w hw))
    (mul_pos hτ (hC s)) (cNorm_nonneg K (s+16) F) (fun b hb' hp ↦ (hb b hb' hp).2) r
  let H := cNorm I (s+16) (r : _ → ℝ) + (1 + cNorm K (s+16) F) * cNorm I 15 (r : _ → ℝ)
  have hl' : cNorm (closedBall a ρ) s (A₀ r) ≤ D s * H := hl
  have hp' : cNorm (closedBall a ρ) s ((Apr-A₀) r) ≤ τ * D s * H := by
    convert hp using 1
    dsimp [D, H]
    ring
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (cNorm_nonneg _ _ _)
      (mul_nonneg (by linarith [cNorm_nonneg K (s+16) F]) (cNorm_nonneg _ _ _))
  have hadd := cNorm_add_le_of_contDiffAt (isCompact_closedBall a ρ) (hlreg r)
    (fun w hw ↦ (hpreg r w hw).sub (hlreg r w hw))
  have heq : A₀ r + ((Apr-A₀) r) = Apr r := by rw [LinearMap.sub_apply]; abel
  change cNorm (closedBall a ρ) s (A₀ r + ((Apr-A₀) r)) ≤ _ at hadd
  rw [heq] at hadd
  change cNorm (closedBall a ρ) s (Apr r) ≤ cNorm (closedBall a ρ) s (A₀ r) +
    cNorm (closedBall a ρ) s ((Apr-A₀) r) at hadd
  have hsmall : τ * D s * H ≤ D s * H := by nlinarith only [mul_le_mul_of_nonneg_right hτ₁ (mul_nonneg (hD s).le hH)]
  have hr' : cNorm (closedBall a ρ) s (Apr r) ≤ 2 * D s * H := by
    linarith only [hadd, hl', hp', hsmall]
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ (he r w hw).2) s] at hl'
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ (he r w hw).1) s] at hr'
  rw [LinearMap.sub_apply, GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun w hw ↦ (he r w hw).1.sub (he r w hw).2) s] at hp'
  exact ⟨hl', hr', hp'⟩

/-- Transfer the fixed response's primitive finite and one-high jet estimates
to the whole original scalar span. The linear map agrees with the demodulated
derivative on a neighborhood of the observation compact. Normalization stays
within the prescribed positive class and handles the kernel of its initial
seminorm. The two explicit constants precede the target and history when the
primitive constants do; the one-high estimate retains its geometric term.
Consumers: initialized density Lipschitz and the tame preparation discrepancy
(`app:ch_response:eq:current-density-lipschitz`, `app:ch_response:eq:current-atomic-offset`). -/
theorem cNorm_fullPrimaryResponseDerivativeAmplitude_of_primitive_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {z₀ : Euclidean 3} {R M m : ℝ} (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < M)
    (s d : ℕ) (hd : 14 ≤ d) {Cf Ct : ℝ} (hCf : 0 < Cf) (hCt : 0 < Ct)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    {Ω O J : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R M m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hO : IsOpen O) (hOΩ : O ⊆ Ω) (hJ : IsCompact J) (hJO : J ⊆ O)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsrc : ∀ w ∈ O, ∀ x ∈ tsupport χ, (x, w.2) ∈ Ω)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    {τ : ℝ} (hτ : 0 < τ)
    (hresp : ∀ r : initialScalarSpan (n := n) z₀ R M m,
      ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) O) :
    let I := closedBall ((0 : Euclidean (n-1)), z₀) (R / 8)
    let A := fun r ↦ fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ
    ((∀ r ∈ primitiveInitialScalars (n := n) z₀ R M m, cNorm I d r ≤ M →
      cNorm J s (A r) ≤ Cf * τ) →
      ∀ r : initialScalarSpan (n := n) z₀ R M m,
        cNorm J s (A r) ≤ (4 * Cf / (M-m)) * τ * cNorm I d (r : _ → ℝ)) ∧
    (∀ H : ℝ, 0 ≤ H →
      (∀ r ∈ primitiveInitialScalars (n := n) z₀ R M m, cNorm I 15 r ≤ M →
        cNorm J s (A r) ≤ Ct * τ * (1 + H + cNorm I d r)) →
      ∀ r : initialScalarSpan (n := n) z₀ R M m,
        cNorm J s (A r) ≤ (Ct * (1 + 4 * (1+M)/(M-m))) * τ *
          (cNorm I d (r : _ → ℝ) + (1+H) * cNorm I 15 (r : _ → ℝ))) := by
  intro I A
  obtain ⟨ψ, _, _, _, hψ, hplateau⟩ := CompatibleResponse.exists_compact_family_cutoff hJ hO hJO
  have hdresp (r : initialScalarSpan (n := n) z₀ R M m) (w) (hw : w ∈ tsupport ψ) :
      DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1 :=
    (((hresp r).contDiffAt (hO.mem_nhds (hψ hw))).comp w.1
      (f := fun x : Euclidean n ↦ (x, w.2)) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
        (by simp)
  obtain ⟨_, _, L, hL⟩ := exists_cutoffFullAmplitudeLinearMaps T Q F row col Φ Y
    hΩ hspace hphase hF hi hrank hnonzero hα χ hχ hc B ψ (hψ.trans hOΩ)
    (fun w hw ↦ hsrc w (hψ hw)) hτ.ne' hdresp
  have hagree (r : initialScalarSpan (n := n) z₀ R M m) (w) (hw : w ∈ J) :
      L r =ᶠ[𝓝 w] A r := by
    rw [(hL r).2.2]
    filter_upwards [isOpen_interior.mem_nhds (hplateau hw)] with y hy
    have he := (interior_subset : interior {z | ψ z = 1} ⊆ {z | ψ z = 1}) hy
    change ψ y = 1 at he
    simp only [A, he, one_smul]
  have hn (r : initialScalarSpan (n := n) z₀ R M m) :
      cNorm J s (L r) = cNorm J s (A r) := GeometricProfile.cNorm_eq_of_eventuallyEq (hagree r) s
  have hreg (r : initialScalarSpan (n := n) z₀ R M m) (w) (hw : w ∈ J) :
      ContDiffAt ℝ s (L r) w :=
    (((contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r hO
      (fun y hy ↦ hphase y (hOΩ hy)) χ B τ (hresp r)).contDiffAt
        (hO.mem_nhds (hJO hw))).of_le (by simp)).congr_of_eventuallyEq (hagree r w hw)
  constructor
  · intro hf r
    have hh := cNorm_scalarSpanLinearMap_le hR hm hgap L hJ s d hd hreg (mul_pos hCf hτ)
      (fun v hv hjet ↦ (hn v).trans_le (hf v hv hjet)) r
    rw [hn] at hh
    exact hh.trans_eq (by ring)
  · intro H hH ht r
    have hh := cNorm_scalarSpanLinearMap_oneHigh_le hR hm hgap L hJ s d hreg (mul_pos hCt hτ) hH
      (fun v hv hjet ↦ (hn v).trans_le (ht v hv hjet)) r
    rw [hn] at hh
    exact hh.trans_eq (by ring)

end JanetCartan.CorrectedAtoms
