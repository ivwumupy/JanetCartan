module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.PhaseBounds.Extraction
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.PhaseBounds.Homogeneity

/-!
# Actual scalar primitive endpoints from phase seminorms

Step 3 of `app:ch_regular_base:thm:actual-calculus`, before
`app:ch_regular_base:eq:fio-input`: the matrix and inverse entries are bounded
by a phase seminorm with the fixed shift two. The constant is chosen before
the phase. Its only phase-dependent inputs are a fixed low phase bound and
the actual zeroth-order inverse gap. The normalized profile assembly consumes
this result together with `normalized_scalarPrimitive_regular`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n : ℕ}

/-- The actual mixed matrix has normalized smoothness and finite normalized
seminorms, derived from ordinary phase geometry in Step 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem normalized_mixedPhaseMatrix_regular
    {S : Euclidean n → Euclidean n → ℝ} {X D : Set (Euclidean n)}
    (hX : IsOpen X) (hD : IsOpen D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hh : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    {K U : Set (Point n)} (hU : IsOpen U) (hKU : K ⊆ U)
    (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D) (k : ℕ) :
    (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ ∞
      (normalizedField R (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2)) U) ∧
    BoundedNormalizedSeminorm K k (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) ∧
    normalizedSeminorm K k (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) =
      cNorm K k (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) := by
  have hi (R : ℝ) (hR : 1 ≤ R) :
      Set.EqOn (normalizedField R (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2))
        (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) U := by
    intro p hp
    exact mixedPhaseMatrix_dilation_eq_on hX hD hcone hS hh
      (lt_of_lt_of_le zero_lt_one hR) (hchart p hp).1 (hchart p hp).2
  refine ⟨?_, normalizedSeminorm_eq_cNorm_of_invariant hU hKU _ hi k⟩
  intro R hR
  exact (contDiffOn_joint_mixedPhaseMatrix hX hD hS hchart).congr (hi R hR)

/-- The scalar endpoint comparison for the actual normalized primitive
profiles in `app:ch_regular_base:eq:fio-input`. The derivative shift is exactly
two for every `k`. Constants precede the phase and all its high seminorms;
only the low `C²` bound and the actual inverse gap enter them. Smoothness and
homogeneity are required locally on an open position chart and positive cone.
No high inverse-jet or interpolation hypothesis is used. -/
theorem exists_normalizedSeminorm_scalarPrimitive_le_phase
    (z : Point n) {ρ : ℝ} (hρ : 0 < ρ) {U : Set (Point n)}
    (hU : IsOpen U) (hball : Metric.closedBall z ρ ⊆ U)
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (k : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Euclidean n → Euclidean n → ℝ,
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      cNorm (Metric.closedBall z ρ) 2 (fun p : Point n ↦ S p.1.1 p.2) ≤ M →
      (∀ p ∈ U, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ p ∈ Metric.closedBall z ρ, ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      ∀ a : ScalarIndex n,
        normalizedSeminorm (Metric.closedBall z ρ) k (uncurry (scalarPrimitive S a)) ≤
          C * (1 + cNorm (Metric.closedBall z ρ) (k + 2)
            (fun p : Point n ↦ S p.1.1 p.2)) := by
  obtain ⟨C₀, hC₀, hm₀⟩ := exists_cNorm_mixedPhaseMatrix_le_phase n 0
  obtain ⟨Cₖ, hCₖ, hmₖ⟩ := exists_cNorm_mixedPhaseMatrix_le_phase n k
  obtain ⟨E, hE, he⟩ := exists_cNorm_phaseMatrixEntry_le n k
  obtain ⟨I, hI, hi⟩ := exists_cNorm_inverse_tame_on (ι := Fin n) z hρ hU hball k
    (mul_nonneg hC₀.le hM) B
  refine ⟨E * (1 + I) * (1 + Cₖ), by positivity, ?_⟩
  intro S hS hh hlow hu hgap a
  let K := Metric.closedBall z ρ
  let P := fun p : Point n ↦ S p.1.1 p.2
  let F := fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2
  have hP : ContDiffOn ℝ ∞ P U := by
    intro p hp
    exact ((hS.contDiffAt ((hX.prod hD).mem_nhds (hchart p hp))).comp p
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F U := contDiffOn_joint_mixedPhaseMatrix hX hD hS hchart
  have hF₀ : cNorm K 0 F ≤ C₀ * M :=
    (hm₀ K U (isCompact_closedBall z ρ) hU hball S hP).trans
      (mul_le_mul_of_nonneg_left hlow hC₀.le)
  have hFk : cNorm K k F ≤ Cₖ * cNorm K (k + 2) P :=
    hmₖ K U (isCompact_closedBall z ρ) hU hball S hP
  have hInv : cNorm K k (fun p ↦ (F p)⁻¹) ≤ I * (1 + cNorm K k F) :=
    hi F hF hF₀ (fun p hp ↦ (Matrix.isUnit_iff_isUnit_det _).mpr (hu p (hball hp))) hgap
  have hInvSmooth (p) (hp : p ∈ K) : ContDiffAt ℝ ∞ (fun p ↦ (F p)⁻¹) p := by
    have ht := (contDiffAt_mixedPhaseMatrix_inverse_of_phase S (p.1.1, p.2)
      (hS.contDiffAt ((hX.prod hD).mem_nhds (hchart p (hball hp))))
      (hu p (hball hp))).comp (f := fun q : Point n ↦ (q.1.1, q.2)) p
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact ht
  rw [(normalized_scalarPrimitive_regular hX hD hcone hS hh hU hball hchart hu a k).2.2]
  have hH := cNorm_nonneg K (k + 2) P
  have hbound : 1 + cNorm K k F ≤ (1 + Cₖ) * (1 + cNorm K (k + 2) P) := by
    nlinarith
  have hplain : cNorm K k F ≤ (1 + I) * ((1 + Cₖ) * (1 + cNorm K (k + 2) P)) := by
    apply (le_add_of_nonneg_left zero_le_one).trans hbound |>.trans
    exact le_mul_of_one_le_left (by positivity) (by linarith)
  have hinverse : cNorm K k (fun p ↦ (F p)⁻¹) ≤
      (1 + I) * ((1 + Cₖ) * (1 + cNorm K (k + 2) P)) := by
    apply hInv.trans
    exact (mul_le_mul_of_nonneg_left hbound hI.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  change cNorm K k (fun p ↦ if a.1 then ((F p)⁻¹ a.2.1 a.2.2 : ℂ)
    else (F p a.2.1 a.2.2 : ℂ)) ≤ _
  cases ha : a.1 with
  | false =>
    have hb := (he K (isCompact_closedBall z ρ) F
      (fun p hp ↦ hF.contDiffAt (hU.mem_nhds (hball hp))) a.2.1 a.2.2).trans
        (mul_le_mul_of_nonneg_left hplain hE.le)
    simpa [uncurry, scalarPrimitive, ha, F, K, P, mul_assoc] using hb
  | true =>
    have hb := (he K (isCompact_closedBall z ρ) (fun p ↦ (F p)⁻¹)
      hInvSmooth a.2.1 a.2.2).trans (mul_le_mul_of_nonneg_left hinverse hE.le)
    simpa [uncurry, scalarPrimitive, ha, F, K, P, mul_assoc] using hb

end JanetCartan.FourierIntegral.PrimitiveProfiles
