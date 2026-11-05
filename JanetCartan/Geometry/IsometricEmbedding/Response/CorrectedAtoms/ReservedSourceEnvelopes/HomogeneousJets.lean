module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.HomogeneousRawBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReservedSourceEnvelopes.FiniteJets

/-!
# Homogeneous joint jets of the original full strain

The actual projected WKB reconstruction supplies a primitive one-high bound.
Linearity on the original scalar span then removes its additive constant,
using the same positive scalar class and its fixed margin. The seminorm kernel
is handled by a limiting inequality, without changing the scalar domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms.ReservedSourceEnvelopes
open PrimarySourceAdmission

private theorem source_cNorm_const_le {D E : Type*}
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


private theorem source_contDiffOn_initialScalarSpan {n : ℕ} {z₀ : Euclidean 3} {R M m : ℝ}
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


private theorem source_scalarSpan_oneHigh_le
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
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb] using source_cNorm_const_le I k b
  have hbase : (fun _ : Euclidean (n-1) × Euclidean 3 ↦ b) ∈ primitiveInitialScalars z₀ R M m :=
    ⟨contDiffOn_const, (hconst 14).trans hbM, fun _ _ ↦ hbm⟩
  let base : initialScalarSpan (n := n) z₀ R M m := ⟨_, Submodule.subset_span hbase⟩
  have hbaseBound : cNorm K s (L base) ≤ C * (1+H+b) :=
    (hbound base hbase ((hconst 15).trans hbM)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hconst d]) hC.le)
  have hI : I ⊆ ball ((0 : Euclidean (n-1)), z₀) (R/4) := closedBall_subset_ball (by linarith)
  have hrAt (k : ℕ) (x) (hx : x ∈ I) : ContDiffAt ℝ k (r : Euclidean (n-1) × Euclidean 3 → ℝ) x :=
    ((source_contDiffOn_initialScalarSpan r).contDiffAt (isOpen_ball.mem_nhds (hI hx))).of_le (by simp)
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
      refine ⟨source_contDiffOn_initialScalarSpan u, (cNorm_mono_order (by omega : 14 ≤ 15)).trans huLow, ?_⟩
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


open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
  LeadingWave.FullModulation ProjectedStressFrame InitialScalarCalculus ResponsePrimarySources ResponseTransfer
  ResponseSourceExtension

private theorem exists_local_fullStrain_linearMap
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (τ : ℝ) :
    ∃ L : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin n) (Fin n) ℂ),
      ∀ r w, w ∈ Ω → L r w = fullPrimaryStrainAmplitude T Q F row col Φ Y r τ w := by
  classical
  have hαspan (r : initialScalarSpan (n := n) z₀ R Mᵣ m) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα r.property
  have hatom (r : initialScalarSpan (n := n) z₀ R Mᵣ m) : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2)) Ω :=
    contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
      hΩ hspace hphase hF hi hrank (hαspan r) hnonzero
  have hd (r : initialScalarSpan (n := n) z₀ R Mᵣ m)
      (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (hw : w ∈ Ω) :
      DifferentiableAt ℝ (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 := by
    have h := ((hatom r).contDiffAt (hΩ.mem_nhds hw)).comp w.1
      (f := fun x : Euclidean n ↦ (x, w.2)) (contDiffAt_id.prodMk contDiffAt_const)
    exact h.differentiableAt (by simp)
  let L : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
      ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun r w ↦ if w ∈ Ω then fullPrimaryStrainAmplitude T Q F row col Φ Y r τ w else 0
      map_add' := by
        intro r s
        funext w
        by_cases hw : w ∈ Ω
        · simp only [ite_eq_left hw, Pi.add_apply]
          have he : (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ
                ((r + s : initialScalarSpan (n := n) z₀ R Mᵣ m) : Euclidean (n - 1) × Euclidean 3 → ℝ)
                  w.2.1 (x, w.2.2)) =ᶠ[𝓝 w.1]
              (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) +
                (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ s w.2.1 (x, w.2.2)) := by
            filter_upwards [(hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hw]
              with x hx
            exact fullPrimaryAtom_initial_add T Q F row col Φ Y hΩ hspace hphase
              hF hi hnonzero τ (r := r) (s := s) (hαspan r) (hαspan s) (w := (x, w.2)) hx
          simp only [fullPrimaryStrainAmplitude,
            (complexLinearizedMetric_eventuallyEq F he).self_of_nhds,
            complexLinearizedMetric_add F (hd r w hw) (hd s w hw), smul_add]
        · simp only [ite_eq_right hw, Pi.add_apply, add_zero]
      map_smul' := by
        intro t r
        funext w
        by_cases hw : w ∈ Ω
        · simp only [ite_eq_left hw, Pi.smul_apply]
          have he : (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ
                ((t • r : initialScalarSpan (n := n) z₀ R Mᵣ m) : Euclidean (n - 1) × Euclidean 3 → ℝ)
                  w.2.1 (x, w.2.2)) =ᶠ[𝓝 w.1]
              t • (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) := by
            filter_upwards [(hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hw]
              with x hx
            exact fullPrimaryAtom_initial_smul T Q F row col Φ Y hΩ hspace hphase
              hF hi hnonzero τ (r := r) (hαspan r) t (w := (x, w.2)) hx
          simp only [fullPrimaryStrainAmplitude,
            (complexLinearizedMetric_eventuallyEq F he).self_of_nhds,
            complexLinearizedMetric_real_smul F (hd r w hw) t]
          exact smul_comm _ _ _
        · simp only [ite_eq_right hw, Pi.smul_apply, smul_zero] }
  exact ⟨L, fun r w hw ↦ ite_eq_left hw⟩

/-- The actual cubic WKB strain has homogeneous one-high scalar bounds on
the original scalar span. The primitive correction estimate is the output of
`RetainedCorrection.exists_retained_cell_correction_bounds`; no full-strain
estimate is an input. Only scalar and immersion orders through `s+16` occur.
The same full phase, transport and correction are retained, and the constant
is chosen before all varying geometry, scalars and frequency
(`app:ch_waves:eq:WKB-strain`, `app:ch_response:eq:response-graded-source`). -/
theorem exists_retained_fullStrain_homogeneous_joint_bounds
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hx : MapsTo Prod.fst (closedBall a ρ) K)
    (M : ℝ)
    (z₀ : Euclidean 3) {R Mᵣ m : ℝ} (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < Mᵣ)
    {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (Γ : ℕ → ℝ) (hΓ : ∀ j, 0 < Γ j) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
        Q.1 = projectedStress F → IsOpen Ω → closedBall a ρ ⊆ Ω → MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 15 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
          ambientStrainFrameThreshold hn) →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ w ∈ Ω,
          conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
              nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ j,
          cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ j * (1 + cNorm K (j + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) →
        ∀ τ : ℝ, 0 < τ → ∀ s : ℕ,
        ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
        let Kr := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
        cNorm (closedBall a ρ) s (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) ≤
          C s * τ ^ 3 * (cNorm Kr (s + 16) (r : _ → ℝ) +
            (1 + cNorm K (s + 16) F) * cNorm Kr 16 (r : _ → ℝ)) := by
  let Llow := Γ 1 * (1 + M + Mᵣ)
  obtain ⟨D, hD, hreconstruct⟩ := AmbientStrain.exists_projected_reconstruction_bounds
    hn a hρ hK hx M Llow hκmet hκnormal
  let Cprimitive := fun s ↦ 2 * D s * (1 + Γ (s + 1))
  have hCprimitive (s : ℕ) : 0 < Cprimitive s := by
    dsimp only [Cprimitive]
    exact mul_pos (mul_pos (by norm_num) (hD s)) (by linarith [hΓ (s + 1)])
  let factor := 1 + 4 * (1 + Mᵣ) / (Mᵣ - m)
  have hfactor : 0 < factor := by
    have hMr : 0 ≤ Mᵣ := hm.trans hgap.le
    dsimp only [factor]
    positivity
  refine ⟨fun s ↦ Cprimitive s * factor, fun s ↦ mul_pos (hCprimitive s) hfactor, ?_⟩
  intro F Q row col Φ Y Ω hQ hΩ hball hΩK hphase hF hi hrank hFM hmet hnormal hframe
    hnonzero hα htransport hcorrection τ hτ s r Kr
  have hspace : ∀ w ∈ Ω, w.1 ∈ U := fun w hw ↦ hKU (hΩK hw)
  have hαspan (b : initialScalarSpan (n := n) z₀ R Mᵣ m) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα b.property
  obtain ⟨L, hL⟩ := exists_local_fullStrain_linearMap T Q F row col Φ Y
    hΩ hspace hphase hF hi hrank hnonzero hα τ
  have he (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      L b =ᶠ[𝓝 w] fullPrimaryStrainAmplitude T Q F row col Φ Y b τ :=
    Filter.eventually_of_mem (hΩ.mem_nhds (hball hw)) (fun y hy ↦ hL b y hy)
  have hrawSmooth (b : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      ContDiffOn ℝ ∞ (fullPrimaryStrainAmplitude T Q F row col Φ Y b τ) Ω :=
    contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y b τ
      hΩ hspace hphase hF hi hrank (hαspan b) hnonzero
  have hreg (b : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ closedBall a ρ) :
      ContDiffAt ℝ s (L b) w :=
    (((hrawSmooth b).contDiffAt (hΩ.mem_nhds (hball hw))).of_le (by simp)).congr_of_eventuallyEq
      (he b w hw)
  have hprimitive (b : initialScalarSpan (n := n) z₀ R Mᵣ m)
      (hb : (b : Euclidean (n - 1) × Euclidean 3 → ℝ) ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m)
      (hbLow : cNorm Kr 15 (b : _ → ℝ) ≤ Mᵣ) :
      cNorm (closedBall a ρ) s (L b) ≤ (Cprimitive s * τ ^ 3) *
        (1 + cNorm K (s + 16) F + cNorm Kr (s + 16) (b : _ → ℝ)) := by
    let correction := fullCorrectionCovector T Q F row col Φ Y b
    have hcorrectionSmooth : ContDiffOn ℝ ∞ correction Ω :=
      contDiffOn_fullCorrectionCovector_of_leading_outputs T Q F row col Φ Y b
        hΩ hspace hphase hF hi (hα b hb) hnonzero
    have hcorrectionLow : cNorm (closedBall a ρ) 1 correction ≤ Llow := by
      apply (hcorrection b hb 1).trans
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hFM) hbLow) (hΓ 1).le
    obtain ⟨hEbound, hEregular⟩ := hreconstruct U Ω hU hΩ hKU hball hspace F correction
      hF hi hrank hcorrectionSmooth ((cNorm_mono_order (by omega)).trans hFM)
      hcorrectionLow hmet hnormal hframe s
    let E := fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      WKB.stressReconstruction (projectedStress F y.1)
        (fun i ↦ complexReducedOperator F (projectedStress F) (fun x ↦ correction (x, y.2)) y.1 i)
    have hec (w) (hw : w ∈ closedBall a ρ) :
        fullPrimaryStrainAmplitude T Q F row col Φ Y b τ =ᶠ[𝓝 w] (2 * τ ^ 3) • E := by
      filter_upwards [hΩ.mem_nhds (hball hw)] with y hy
      have hh := fullPrimaryAtom_demodulated_strain_of_leading_outputs T Q row col Φ Y b
        hn F hQ hK hKU hframe hΩ hspace hphase hF hi hrank (hα b hb)
        hnonzero (htransport b hb) hy (hΩK hy) hτ.ne'
      have hfactor : ((2 : ℂ) * (τ : ℂ) ^ 3) = ((2 * τ ^ 3 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hfactor, Complex.coe_smul] at hh
      simpa only [E, correction, hQ, Pi.smul_apply] using hh
    rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ he b w hw) s,
      GeometricProfile.cNorm_eq_of_eventuallyEq hec s,
      cNorm_smul_of_contDiffAt (2 * τ ^ 3) (fun w hw ↦ (hEregular w hw).of_le (by simp)),
      Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) (pow_pos hτ _))]
    let H := 1 + cNorm K (s + 16) F + cNorm Kr (s + 16) (b : _ → ℝ)
    have hgeom : 1 + cNorm K (s + 2) F ≤ H := by
      dsimp only [H]
      have hh := cNorm_mono_order (f := F) (s := K) (show s + 2 ≤ s + 16 by omega)
      linarith [cNorm_nonneg Kr (s + 16) (b : _ → ℝ)]
    have hcorrectionHigh : cNorm (closedBall a ρ) (s + 1) correction ≤ Γ (s + 1) * H := by
      apply (hcorrection b hb (s + 1)).trans
      apply mul_le_mul_of_nonneg_left _ (hΓ (s + 1)).le
      exact add_le_add (add_le_add le_rfl (cNorm_mono_order (by omega)))
        (cNorm_mono_order (by omega))
    have htotal : cNorm (closedBall a ρ) s E ≤ D s * (1 + Γ (s + 1)) * H :=
      hEbound.trans ((mul_le_mul_of_nonneg_left (add_le_add hgeom hcorrectionHigh) (hD s).le).trans_eq
        (by ring))
    exact (mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ 2 * τ ^ 3)).trans_eq
      (by dsimp only [Cprimitive, H]; ring)
  have hnormal := source_scalarSpan_oneHigh_le hR hm hgap L (isCompact_closedBall a ρ)
    s (s + 16) hreg (mul_pos (hCprimitive s) (pow_pos hτ _))
    (cNorm_nonneg K (s + 16) F) hprimitive r
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦ he r w hw) s] at hnormal
  apply hnormal.trans
  have hlow : cNorm Kr 15 (r : _ → ℝ) ≤ cNorm Kr 16 (r : _ → ℝ) := cNorm_mono_order (by omega)
  calc
    _ = (Cprimitive s * factor) * τ ^ 3 *
        (cNorm Kr (s + 16) (r : _ → ℝ) + (1 + cNorm K (s + 16) F) * cNorm Kr 15 (r : _ → ℝ)) := by
      dsimp only [factor]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hlow (by linarith [cNorm_nonneg K (s + 16) F])))
      (mul_nonneg (mul_nonneg (hCprimitive s).le hfactor.le) (pow_nonneg hτ.le _))

end JanetCartan.CorrectedAtoms.ReservedSourceEnvelopes
