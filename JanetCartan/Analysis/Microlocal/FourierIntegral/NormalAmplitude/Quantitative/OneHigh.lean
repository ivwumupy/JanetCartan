module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Bounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh.Interpolation

/-!
# One-high bounds for the actual full matrix normal amplitude

On fixed normalized shell charts, the original `J,A,B` array and the supplied
inverse preserving both positions satisfy baseline-one joint interpolation
profiles. Two applications of the partition budget prove the Frobenius bound
linear in the common high norm. The determinant gap and zeroth input bound fix
the range of the nonlinear coefficient operation, including matrix order and
conjugate transpose. No transformed-amplitude jet is an input.

Sources: `app:ch_regular_base:lem:buffered-interpolation`,
`app:ch_regular_base:eq:actual-normal-amplitude`, and
`app:ch_regular_base:eq:actual-one-high`.

The actual primitive profiles are obligations of `jc-hamilton-phase`,
`jc-compatible-phase-geometry`, and `jc-normal-inverse-coefficients`; the consumer
`jc-deduce-fio-normal-amplitude` must instantiate them. If their fixed derivative
shifts are at most β, take H = 1 + the coefficient Sobolev norm at s + β.
This proof introduces no further derivative shift. The interpolation helper
supplies the profiles from buffered primitive C¹ and Cˢ bounds.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open NormalOneHigh
variable {n r : ℕ}

/-- One-high Frobenius jets of the actual cross-normal from primitive joint
interpolation profiles. Constants precede the fields and H. Both physical
positions are retained. Source: `app:ch_regular_base:eq:actual-one-high`.
The zeroth input bound and order-one profiles are fixed low bounds. -/
theorem exists_crossNormalAmplitude_oneHigh_bound (s : ℕ) (hs : 2 ≤ s)
    (M : ℝ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0,
      ∀ (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
        (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
        (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
        (Ω W : Set (NormalVariables n)) (H : ℝ),
        1 ≤ H → IsOpen Ω → IsOpen W →
        ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω →
        MapsTo (normalInverseCoordinates η) Ω W →
        ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W →
        (∀ q ∈ W, δ ≤ |(J q.1 q.2.1 q.2.2).det|) →
        (∀ q ∈ W, ‖normalInputCoefficients A B J q‖ ≤ M) →
        (∀ q ∈ W, ∀ i, 1 ≤ i → i ≤ s →
          ‖iteratedFDeriv ℝ i (normalInputCoefficients A B J) q‖ ≤
            a i * H ^ (((i : ℝ) - 1) / (s - 1))) →
        (∀ q ∈ Ω, ∀ i, 1 ≤ i → i ≤ s →
          ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) q‖ ≤
            b i * H ^ (((i : ℝ) - 1) / (s - 1))) →
        ∀ q ∈ Ω, ∀ k ≤ s,
          ‖iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
            crossNormalAmplitude A B η J z.1 z.2.1 z.2.2) q‖ ≤ C * H := by
  obtain ⟨R, hR, hbound⟩ := exists_normalAmplitudeCoefficient_jet_bound
    (n := n) (r := r) s M hδ
  let c := compositionBudget (fun _ ↦ R) a
  let d := compositionBudget c b
  have hc : ∀ i, 0 ≤ c i := compositionBudget_nonneg (fun _ ↦ hR.le) ha
  have hd : ∀ i, 0 ≤ d i := compositionBudget_nonneg hc hb
  let C := R + ∑ i ∈ Finset.range (s + 1), d i
  have hRC : R ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hd i))
  refine ⟨C, hR.trans_le hRC, ?_⟩
  intro A B η J Ω W H hH hΩ hW hη hmap hinput hgap hzero hjet hinv q hq k hk
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hspos : (0 : ℝ) < s - 1 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hcoeff (z) (hz : z ∈ W) :
      ContDiffAt ℝ ∞ (@normalAmplitudeCoefficient n r) (normalInputCoefficients A B J z) := by
    have hstar : ContDiff ℝ ∞
        (fun a : Matrix (Fin r) (Fin r) ℂ ↦ a.conjTranspose) :=
      (Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ).toContinuousLinearEquiv.contDiff
    have hdet : (normalInputCoefficients A B J z).1.det ≠ 0 :=
      abs_pos.mp (hδ.trans_le (hgap z hz))
    exact ((NormalComparison.contDiffAt_reciprocalAbsNormalJacobian hdet).comp
      (normalInputCoefficients A B J z) contDiffAt_fst).smul
      (contDiffAt_snd.fst.mul (hstar.contDiffAt.comp _ contDiffAt_snd.snd))
  have hfirst (z) (hz : z ∈ W) (i : ℕ) (hi : 1 ≤ i) (his : i ≤ s) :
      ‖iteratedFDeriv ℝ i (normalAmplitudeCoefficient ∘ normalInputCoefficients A B J) z‖ ≤
        c i * H ^ (((i : ℝ) - 1) / (s - 1)) := by
    apply norm_iteratedFDeriv_comp_le_profile
      (hinput.contDiffAt (hW.mem_nhds hz)) (hcoeff z hz) hi his hHpos
      (fun _ ↦ R) a (fun _ ↦ hR.le)
    · intro j hj hjs
      apply (hbound _ (hzero z hz) (hgap z hz) j hjs).trans
      apply le_mul_of_one_le_right hR.le
      apply Real.one_le_rpow hH
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hj)) hspos.le
    · exact hjet z hz
  change ‖iteratedFDeriv ℝ k
    ((normalAmplitudeCoefficient ∘ normalInputCoefficients A B J) ∘ normalInverseCoordinates η) q‖ ≤ _
  by_cases hk0 : k = 0
  · subst k
    simp only [norm_iteratedFDeriv_zero]
    exact (show ‖normalAmplitudeCoefficient (normalInputCoefficients A B J
      (normalInverseCoordinates η q))‖ ≤ R by
        simpa using hbound _ (hzero _ (hmap hq)) (hgap _ (hmap hq)) 0 (Nat.zero_le s)).trans
      (hRC.trans (le_mul_of_one_le_right (hR.le.trans hRC) hH))
  · have hcomp := norm_iteratedFDeriv_comp_le_profile
      (hη.contDiffAt (hΩ.mem_nhds hq))
      ((hcoeff _ (hmap hq)).comp _ (hinput.contDiffAt (hW.mem_nhds (hmap hq))))
      (show 1 ≤ k by omega) hk hHpos c b hc
      (hfirst _ (hmap hq)) (hinv q hq)
    apply hcomp.trans
    have hdC : d k ≤ C := by
      have := Finset.single_le_sum (fun i _ ↦ hd i)
        (Finset.mem_range.mpr (by omega : k < s + 1))
      dsimp [C]
      linarith
    have hp : H ^ (((k : ℝ) - 1) / (s - 1)) ≤ H := by
      calc
        _ ≤ H ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hH
          ((div_le_one hspos).mpr (sub_le_sub_right (by exact_mod_cast hk) 1))
        _ = H := Real.rpow_one H
    exact mul_le_mul hdC hp (Real.rpow_nonneg hHpos.le _) (hR.le.trans hRC)

/-- The one-high bound holds globally for the buffered literal zero extension.
All boundary and exterior jets vanish by the original support and inverse law.
Source: `app:ch_regular_base:eq:actual-one-high`. -/
theorem exists_extendedCrossNormalAmplitude_oneHigh_bound (s : ℕ) (hs : 2 ≤ s)
    (M : ℝ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0,
      ∀ (S : Euclidean n → Euclidean n → ℝ)
        (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
        (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
        (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
        (Ω W K : Set (NormalVariables n)) (H : ℝ),
        1 ≤ H → IsOpen Ω → IsOpen W →
        ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω →
        MapsTo (normalInverseCoordinates η) Ω W →
        ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W →
        (∀ q ∈ W, δ ≤ |(J q.1 q.2.1 q.2.2).det|) →
        (∀ q ∈ W, ‖normalInputCoefficients A B J q‖ ≤ M) →
        (∀ q ∈ W, ∀ i, 1 ≤ i → i ≤ s →
          ‖iteratedFDeriv ℝ i (normalInputCoefficients A B J) q‖ ≤
            a i * H ^ (((i : ℝ) - 1) / (s - 1))) →
        (∀ q ∈ Ω, ∀ i, 1 ≤ i → i ≤ s →
          ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) q‖ ≤
            b i * H ^ (((i : ℝ) - 1) / (s - 1))) →
        (∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q) →
        (∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K) →
        IsClosed (normalForwardCoordinates S '' K) →
        normalForwardCoordinates S '' K ⊆ Ω →
        ∀ q, ∀ k ≤ s,
          ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) q‖ ≤ C * H := by
  obtain ⟨C, hC, hbound⟩ := exists_crossNormalAmplitude_oneHigh_bound
    (n := n) (r := r) s hs M a b ha hb hδ
  refine ⟨C, hC, ?_⟩
  intro S A B η J Ω W K H hH hΩ hW hη hmap hinput hgap hzero hjet hinv
    hright hsupp hclosed hbuffer q k hk
  by_cases hq : q ∈ Ω
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq A B η J hΩ hq k]
    exact hbound A B η J Ω W H hH hΩ hW hη hmap hinput hgap hzero hjet hinv q hq k hk
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero S A B η J
      hmap hright hsupp hclosed hbuffer hq k, norm_zero]
    exact mul_nonneg hC.le (zero_le_one.trans hH)

/-- Orders zero and one require only fixed low bounds and have no high-norm
factor. Source: `app:ch_regular_base:eq:actual-one-high`. -/
theorem exists_crossNormalAmplitude_lowJet_bound (M L : ℝ)
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
        (∀ q ∈ W, ∀ i ≤ 1, ‖iteratedFDeriv ℝ i (normalInputCoefficients A B J) q‖ ≤ M) →
        (∀ q ∈ Ω, ∀ i, 1 ≤ i → i ≤ 1 →
          ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) q‖ ≤ L) →
        ∀ q ∈ Ω, ∀ k ≤ 1,
          ‖iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
            crossNormalAmplitude A B η J z.1 z.2.1 z.2.2) q‖ ≤ C := by
  exact exists_crossNormalAmplitude_finiteJet_bound 1 M L hδ

/-- Orders zero and one of the buffered literal extension are uniformly
bounded by fixed low data. Source: `app:ch_regular_base:eq:actual-one-high`. -/
theorem exists_extendedCrossNormalAmplitude_lowJet_bound (M L : ℝ)
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
        (∀ q ∈ W, ∀ i ≤ 1, ‖iteratedFDeriv ℝ i (normalInputCoefficients A B J) q‖ ≤ M) →
        (∀ q ∈ Ω, ∀ i, 1 ≤ i → i ≤ 1 →
          ‖iteratedFDeriv ℝ i (normalInverseCoordinates η) q‖ ≤ L) →
        (∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q) →
        (∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K) →
        IsClosed (normalForwardCoordinates S '' K) →
        normalForwardCoordinates S '' K ⊆ Ω →
        ∀ q, ∀ k ≤ 1,
          ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) q‖ ≤ C := by
  exact exists_extendedCrossNormalAmplitude_finiteJet_bound 1 M L hδ

/-- On fixed buffered working balls, the primitive C¹ and Cˢ bounds themselves
imply one-high bounds for both the actual matrix amplitude and its literal zero
extension. Thus no interpolation profile or transformed-amplitude bound is an
extra input here. For `app:ch_regular_base:eq:actual-one-high`, the producers
supply the two Cˢ estimates with H = 1 + ‖a‖ at Sobolev order s + β; β is unchanged
by this theorem. The constant T may depend on s and fixed low data, but not H.
Source: `app:ch_regular_base:lem:buffered-interpolation`. -/
theorem exists_normalAmplitude_oneHigh_bound_of_cNorm
    (s : ℕ) (hs : 2 ≤ s) (x y : NormalVariables n) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) {U V : Set (NormalVariables n)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hx : Metric.closedBall x ρ ⊆ U) (hy : Metric.closedBall y τ ⊆ V)
    {M L T δ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hT : 1 ≤ T) (hδ : 0 < δ) :
    ∃ C > 0,
      ∀ (S : Euclidean n → Euclidean n → ℝ)
        (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
        (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
        (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
        (Ω W K : Set (NormalVariables n)) (H : ℝ),
        1 ≤ H → IsOpen Ω → IsOpen W →
        W ⊆ Metric.closedBall x ρ → Ω ⊆ Metric.closedBall y τ →
        ContDiffOn ℝ ∞ (normalInputCoefficients A B J) U →
        ContDiffOn ℝ ∞ (normalInverseCoordinates η) V →
        MapsTo (normalInverseCoordinates η) Ω W →
        (∀ q ∈ W, δ ≤ |(J q.1 q.2.1 q.2.2).det|) →
        cNorm (Metric.closedBall x ρ) 1 (normalInputCoefficients A B J) ≤ M →
        cNorm (Metric.closedBall y τ) 1 (normalInverseCoordinates η) ≤ L →
        1 + cNorm (Metric.closedBall x ρ) s (normalInputCoefficients A B J) ≤ T * H →
        1 + cNorm (Metric.closedBall y τ) s (normalInverseCoordinates η) ≤ T * H →
        (∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q) →
        (∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K) →
        IsClosed (normalForwardCoordinates S '' K) →
        normalForwardCoordinates S '' K ⊆ Ω →
        (∀ q ∈ Ω, ∀ k ≤ s,
          ‖iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
            crossNormalAmplitude A B η J z.1 z.2.1 z.2.2) q‖ ≤ C * H) ∧
        (∀ q, ∀ k ≤ s,
          ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) q‖ ≤ C * H) := by
  obtain ⟨a, ha, hpa⟩ := exists_primitiveJet_profile_closedBall
    (F := (Euclidean n →L[ℝ] Euclidean n) ×
      (Matrix (Fin r) (Fin r) ℂ × Matrix (Fin r) (Fin r) ℂ))
    x hρ hU hx hs hM hT
  obtain ⟨b, hb, hpb⟩ := exists_primitiveJet_profile_closedBall
    (F := NormalVariables n) y hτ hV hy hs hL hT
  obtain ⟨C, hC, hbound⟩ := exists_crossNormalAmplitude_oneHigh_bound
    (n := n) (r := r) s hs M (fun _ ↦ a) (fun _ ↦ b)
    (fun _ ↦ zero_le_one.trans ha) (fun _ ↦ zero_le_one.trans hb) hδ
  refine ⟨C, hC, ?_⟩
  intro S A B η J Ω W K H hH hΩ hW hWx hΩy hinput hη hmap hgap
    hlow hlowη hhigh hhighη hright hsupp hclosed hbuffer
  obtain ⟨hzero, hjet⟩ := hpa _ H hinput hH hlow hhigh
  obtain ⟨_, hinv⟩ := hpb _ H hη hH hlowη hhighη
  have hchart := hbound A B η J Ω W H hH hΩ hW
    (hη.mono (hΩy.trans hy)) hmap (hinput.mono (hWx.trans hx)) hgap
    (fun q hq ↦ hzero q (hWx hq))
    (fun q hq ↦ hjet q (hWx hq)) (fun q hq ↦ hinv q (hΩy hq))
  refine ⟨hchart, ?_⟩
  intro q k hk
  by_cases hq : q ∈ Ω
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq A B η J hΩ hq k]
    exact hchart q hq k hk
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero S A B η J
      hmap hright hsupp hclosed hbuffer hq k, norm_zero]
    exact mul_nonneg hC.le (zero_le_one.trans hH)

end JanetCartan.FourierIntegral
