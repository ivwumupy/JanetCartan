module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Smooth
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Jets

/-!
# Bounds for the full matrix cross-normal amplitude

These bounds concern the Frobenius norm of the literal full amplitude in
`app:ch_regular_base:eq:actual-normal-amplitude`. They make no operator-norm
assumption. Conic symbol estimates and coefficient one-high bounds require
additional deductions from the weighted primitive jets.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- The zeroth full-amplitude Frobenius bound follows directly from the
Jacobian gap and the two original matrix values. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem norm_crossNormalAmplitude_le
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (x y ξ : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ |(J x y (η x y ξ)).det|) :
    ‖crossNormalAmplitude A B η J x y ξ‖ ≤
      δ⁻¹ * ‖A x (η x y ξ)‖ * ‖B y (η x y ξ)‖ := by
  unfold crossNormalAmplitude crossNormalNumerator
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_abs]
  calc
    _ ≤ δ⁻¹ * (‖A x (η x y ξ)‖ * ‖(B y (η x y ξ)).conjTranspose‖) :=
      mul_le_mul (inv_anti₀ hδ hgap) (Matrix.frobenius_norm_mul _ _)
        (norm_nonneg _) (inv_nonneg.mpr hδ.le)
    _ = _ := by rw [Matrix.frobenius_norm_conjTranspose, mul_assoc]

/-- The same pointwise bound holds for the literal zero extension, including
points off the chart. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem norm_extendedCrossNormalAmplitude_le
    (Ω : Set (NormalVariables n))
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (q : NormalVariables n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : q ∈ Ω → δ ≤ |(J q.1 q.2.1 (η q.1 q.2.1 q.2.2)).det|) :
    ‖extendedCrossNormalAmplitude Ω A B η J q‖ ≤
      δ⁻¹ * ‖A q.1 (η q.1 q.2.1 q.2.2)‖ * ‖B q.2.1 (η q.1 q.2.1 q.2.2)‖ := by
  by_cases hq : q ∈ Ω
  · rw [extendedCrossNormalAmplitude, indicator_of_mem hq]
    exact norm_crossNormalAmplitude_le A B η J _ _ _ hδ (hgap hq)
  · rw [extendedCrossNormalAmplitude, indicator_of_notMem hq, norm_zero]
    positivity

/-- The original joint input array for the normal amplitude, before applying
any nonlinear operation or inverse chart. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
def normalInputCoefficients
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (q : NormalVariables n) := (J q.1 q.2.1 q.2.2, (A q.1 q.2.2, B q.2.1 q.2.2))

/-- The fixed finite-dimensional coefficient operation in the normal
amplitude (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def normalAmplitudeCoefficient
    (p : (Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ)) :
    Matrix (Fin r) (Fin r) ℂ := |p.1.det|⁻¹ • (p.2.1 * p.2.2.conjTranspose)

private theorem normalAmplitudeCoefficient_contDiffAt
    {p : (Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ)}
    (hp : p.1.det ≠ 0) : ContDiffAt ℝ ∞ normalAmplitudeCoefficient p := by
  have hs : ContDiff ℝ ∞
      (fun a : Matrix (Fin r) (Fin r) ℂ ↦ a.conjTranspose) :=
    (Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ).toContinuousLinearEquiv.contDiff
  exact ((NormalComparison.contDiffAt_reciprocalAbsNormalJacobian hp).comp p
    contDiffAt_fst).smul (contDiffAt_snd.fst.mul (hs.contDiffAt.comp p contDiffAt_snd.snd))

/-- Uniform finite jets of the fixed coefficient operation on bounded inputs
with a determinant gap. Constants precede the actual phase and amplitudes.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_normalAmplitudeCoefficient_jet_bound (N : ℕ) (M : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ p : (Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ),
      ‖p‖ ≤ M → δ ≤ |p.1.det| → ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k normalAmplitudeCoefficient p‖ ≤ C := by
  let K : Set ((Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ)) :=
    {p | ‖p‖ ≤ M ∧ δ ≤ |p.1.det|}
  have hc : IsCompact K := (isCompact_closedBall (0 : (Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ)) M).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (ContinuousLinearMap.continuous_det.comp continuous_fst).abs))
    (fun p hp ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1)
  have hb (k : ℕ) : ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k normalAmplitudeCoefficient p‖ ≤ C := by
    apply hc.exists_bound_of_continuousOn (f := iteratedFDeriv ℝ k (@normalAmplitudeCoefficient n r))
    intro p hp
    exact ((normalAmplitudeCoefficient_contDiffAt (abs_pos.mp (hδ.trans_le hp.2))).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  choose C hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), |C k|, by positivity, ?_⟩
  intro p hp hgap k hk
  have hs := Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i))
    (Finset.mem_range.mpr (by omega : k < N + 1))
  have h := hC k p ⟨hp, hgap⟩
  linarith [le_abs_self (C k)]

/-- Finite joint Frobenius jets of the full amplitude from the original joint
matrix/Jacobian jets and the supplied inverse-coordinate jets. Constants are
chosen before all fields. This finite bound is polynomial, and is not yet the
one-high coefficient estimate. Source: `app:ch_regular_base:eq:actual-normal-amplitude`.
The array in `hinput` consists only of primitive inputs, not of the numerator,
reciprocal determinant, or transformed amplitude. -/
theorem exists_crossNormalAmplitude_finiteJet_bound (N : ℕ) (M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0,
      ∀ (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
        (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
        (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
        (Ω W : Set (NormalVariables n)),
        IsOpen Ω → IsOpen W →
        ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω →
        MapsTo (normalInverseCoordinates η) Ω W →
        ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W →
        (∀ q ∈ W, δ ≤ |(J q.1 q.2.1 q.2.2).det|) →
        (∀ q ∈ W, ∀ i ≤ N, ‖iteratedFDeriv ℝ i (normalInputCoefficients A B J) q‖ ≤ M) →
        (∀ q ∈ Ω, ∀ i, 1 ≤ i → i ≤ N →
          ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) q‖ ≤ L) →
        ∀ q ∈ Ω, ∀ k ≤ N,
          ‖iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
            crossNormalAmplitude A B η J z.1 z.2.1 z.2.2) q‖ ≤ C := by
  obtain ⟨R, hR, hbound⟩ := exists_normalAmplitudeCoefficient_jet_bound (n := n) (r := r) N M hδ
  let P := (N.factorial : ℝ) * R * (max 1 M)^N
  let C := (N.factorial : ℝ) * P * (max 1 L)^N
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro A B η J Ω W hΩ hW hη hmap hinput hgap hjet hinv q hq k hk
  let V : Set ((Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ)) := {p | p.1.det ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage
    (ContinuousLinearMap.continuous_det.comp continuous_fst)
  have hcoeff : ContDiffOn ℝ ∞ (@normalAmplitudeCoefficient n r) V :=
    fun p hp ↦ (normalAmplitudeCoefficient_contDiffAt hp).contDiffWithinAt
  have hmap' : MapsTo (normalInputCoefficients A B J) W V :=
    fun z hz ↦ abs_pos.mp (hδ.trans_le (hgap z hz))
  have hb (z) (hz : z ∈ W) (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (normalAmplitudeCoefficient ∘ normalInputCoefficients A B J) z‖ ≤ P := by
    apply (NormalComparison.InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
      hW hV hinput hcoeff hmap' hz i
      (fun j hj ↦ hbound _ (by simpa using hjet z hz 0 (Nat.zero_le N))
        (hgap z hz) j (hj.trans hi))
      (fun j _ hj ↦ hjet z hz j (hj.trans hi))).trans
    dsimp [P]
    have hf : (i.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hi
    gcongr
    exact le_max_left _ _
  have hf := NormalComparison.InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
    hΩ hW hη (hcoeff.comp hinput hmap') hmap hq k
    (fun i hi ↦ hb _ (hmap hq) i (hi.trans hk))
    (fun i hi hik ↦ hinv q hq i hi (hik.trans hk))
  change ‖iteratedFDeriv ℝ k
    ((normalAmplitudeCoefficient ∘ normalInputCoefficients A B J) ∘ normalInverseCoordinates η) q‖ ≤ _
  apply hf.trans
  apply le_trans _ (le_max_right 1 C)
  dsimp [C]
  have hfac : (k.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hk
  have hP : 0 ≤ P := by dsimp [P]; positivity
  gcongr
  exact le_max_left _ _

/-- The finite joint input-jet bound holds globally for the literal buffered
zero extension. All chart-boundary jets vanish by the support construction.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`.
This is a uniform finite bound, not the fixed-shift one-high assertion. -/
theorem exists_extendedCrossNormalAmplitude_finiteJet_bound (N : ℕ) (M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0,
      ∀ (S : Euclidean n → Euclidean n → ℝ)
        (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
        (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
        (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
        (Ω W K : Set (NormalVariables n)),
        IsOpen Ω → IsOpen W →
        ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω →
        MapsTo (normalInverseCoordinates η) Ω W →
        ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W →
        (∀ q ∈ W, δ ≤ |(J q.1 q.2.1 q.2.2).det|) →
        (∀ q ∈ W, ∀ i ≤ N, ‖iteratedFDeriv ℝ i (normalInputCoefficients A B J) q‖ ≤ M) →
        (∀ q ∈ Ω, ∀ i, 1 ≤ i → i ≤ N →
          ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) q‖ ≤ L) →
        (∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q) →
        (∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K) →
        IsClosed (normalForwardCoordinates S '' K) →
        normalForwardCoordinates S '' K ⊆ Ω →
        ∀ q, ∀ k ≤ N,
          ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) q‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_crossNormalAmplitude_finiteJet_bound
    (n := n) (r := r) N M L hδ
  refine ⟨C, hC, ?_⟩
  intro S A B η J Ω W K hΩ hW hη hmap hinput hgap hjet hinv
    hright hsupp hclosed hbuffer q k hk
  by_cases hq : q ∈ Ω
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq A B η J hΩ hq k]
    exact hbound A B η J Ω W hΩ hW hη hmap hinput hgap hjet hinv q hq k hk
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero S A B η J
      hmap hright hsupp hclosed hbuffer hq k, norm_zero]
    exact hC.le

end JanetCartan.FourierIntegral
