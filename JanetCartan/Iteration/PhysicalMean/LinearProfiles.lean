module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalMean.InverseMomentProfile
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliaryTame
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Norms
public import JanetCartan.Iteration.PhysicalMean.AggregateSource
public import JanetCartan.Iteration.PhysicalForwardMean.Sampled
public import JanetCartan.Iteration.PhysicalMean.NativeCross
public import JanetCartan.Iteration.PhysicalMean.ScalarInput

/-!
# Sharp source profiles for the same uncut linear mean operator

The linear input to `sourceIterate_seminorm_profile` must preserve the one-high
form in `app:ch_mean_pairs:eq:block-normal`. Weighted source moments are
interpolated before their finite derivative budgets are summed. The scale
never multiplies the highest source norm. The auxiliary output below is the
literal uncut image AND exterior correction on the supplied current inverse.
The current paired raw estimate and its positive-density profile retain their
original producers; no bound for the linear response itself is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open MeasureTheory Set
open scoped ContDiff BigOperators Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean ContinuumRow PeriodicSobolevSpace Pseudodifferential
open PhysicalForwardMean PeriodicLocalL2 AmplitudeBound AmplitudeBound.PaperEstimates
open ContinuumCommutator.ImageChannel.Differential

/-- The actual singleton-source Sobolev seminorm used by
`sourceIterate_seminorm_profile` (`new:eq:source-bound`). -/
def residualSobolevSeminorm (n s : ℕ) : Seminorm ℝ (SmoothResidual n) :=
  SmoothPeriodicFamily.sobolevSeminorm (fun _ : Unit ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one) s

/-- The smooth source seminorm is exactly its original L²-class grade norm. -/
theorem residualSobolevSeminorm_eq_gradeNorm {n : ℕ} (s : ℕ) (e : SmoothResidual n) :
    residualSobolevSeminorm n s e =
      (periodicSobolevScale n (Euclidean n)).gradeNorm s (smoothResidualToL2 n e) := by
  rw [smoothResidualToL2_gradeNorm]
  exact (DensityDiscrepancy.densitySobolevSeminorm_eq_norm s e).trans
    (DensityDiscrepancy.norm_densitySobolevRealization s e)

/-- At order zero the same source seminorm is the original L² norm, with no
localization, finite-dimensional, or frequency-cutoff constant. -/
theorem residualSobolevSeminorm_zero {n : ℕ} (e : SmoothResidual n) :
    residualSobolevSeminorm n 0 e = ‖smoothResidualToL2 n e‖ := by
  rw [residualSobolevSeminorm_eq_gradeNorm, GradedScale.gradeNorm_zero]

/-- The singleton-source norm equals the Fourier norm of its SAME L² class. -/
theorem residualSobolevSeminorm_eq_periodicSobolevNorm {n : ℕ}
    (s : ℕ) (e : SmoothResidual n) :
    residualSobolevSeminorm n s e = periodicSobolevNorm s (smoothResidualToL2 n e) := by
  rw [residualSobolevSeminorm_eq_gradeNorm,
    (periodicSobolevScale n (Euclidean n)).gradeNorm_eq (smoothResidualToL2_mem e s)]
  exact periodicSobolevSeminorm_eq s _

private theorem reserved_interpolation_exponent_le {s i : ℕ} (hi : i ≤ s) (s₀ : ℕ) :
    ((s-i-s₀ : ℕ) : ℝ) ≤ ((s-s₀ : ℕ) : ℝ) * (1 - (i : ℝ) / s) := by
  by_cases hs : s = 0
  · have hi0 : i = 0 := by omega
    simp [hs, hi0]
  have hspos : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hi' : (i : ℝ) ≤ s := by exact_mod_cast hi
  have hfrac : 0 ≤ 1 - (i : ℝ) / s := sub_nonneg.mpr ((div_le_one hspos).mpr hi')
  by_cases hsmall : s-i ≤ s₀
  · rw [Nat.sub_eq_zero_of_le hsmall, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hfrac
  have h₀ : s₀ ≤ s-i := by omega
  have h₁ : s₀ ≤ s := by omega
  rw [Nat.cast_sub h₀, Nat.cast_sub hi, Nat.cast_sub h₁]
  rw [show 1 - (i : ℝ) / s = ((s : ℝ) - i) / s by field_simp,
    ← mul_div_assoc, le_div_iff₀ hspos]
  nlinarith [mul_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
    (Nat.cast_nonneg s₀ : (0 : ℝ) ≤ s₀)]

/-- One weighted source moment is absorbed without attaching a scale power
to the highest source norm (`app:ch_mean_pairs:eq:block-normal`). This applies
weighted Fourier interpolation to the genuine Sobolev class, including `s=0`. -/
theorem source_moment_weight_le {n : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (s₀ : ℕ) {s i : ℕ} (hi : i ≤ s) (e : OutputL2 n)
    (he : e ∈ periodicSobolevLevel n (Euclidean n) s) :
    T^(s-i-s₀) * periodicSobolevNorm i e ≤
      periodicSobolevNorm s e + T^(s-s₀)*‖e‖ := by
  have hT0 := zero_le_one.trans hT
  have hiNorm := periodic_gradeNorm_weighted_interpolate hi
    (pow_nonneg hT0 (s-s₀)) (ofL2 s e he)
  rw [toL2_ofL2, norm_eq, toL2_ofL2,
    (periodicSobolevScale n (Euclidean n)).gradeNorm_eq
      (antitone_periodicSobolevLevel hi he)] at hiNorm
  change (T^(s-s₀)) ^ (1 - (i : ℝ) / s) * periodicSobolevSeminorm i ⟨e, _⟩ ≤ _ at hiNorm
  rw [periodicSobolevSeminorm_eq] at hiNorm
  have hp : T^(s-i-s₀) ≤ (T^(s-s₀)) ^ (1 - (i : ℝ) / s) := by
    simpa only [Real.rpow_natCast, Real.rpow_natCast_mul hT0] using
      Real.rpow_le_rpow_of_exponent_le hT (reserved_interpolation_exponent_le hi s₀)
  exact (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)).trans hiNorm

/-- The complete finite source moment budget has only the derivative count
`s+1`, never a sample, band, or native-frequency count. -/
theorem source_moment_tame_le {n : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (s₀ s : ℕ) (e : OutputL2 n)
    (he : e ∈ periodicSobolevLevel n (Euclidean n) s) :
    (∑ i ∈ Finset.range (s+1), T^(s-i-s₀)*periodicSobolevNorm i e) ≤
      ((s : ℝ)+1)*(periodicSobolevNorm s e + T^(s-s₀)*‖e‖) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range (s+1), (periodicSobolevNorm s e + T^(s-s₀)*‖e‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact source_moment_weight_le hT s₀ (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) e he
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- Insert the SAME current inverse into the weighted source moment budget,
then interpolate the original source, not its image under the inverse. The
inverse bound is the existing current-normal producer; no linear-output bound
is a premise (`app:ch_mean_pairs:eq:block-normal`). -/
theorem inverseSource_moment_tame_le {n : ℕ}
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    {T : ℝ} (hT : 1 ≤ T) (s₀ s : ℕ) (e : OutputL2 n)
    (he : e ∈ periodicSobolevLevel n (Euclidean n) s)
    (hinverse : ∀ i, i ≤ s → periodicSobolevNorm i (Q₀ e) ≤
      C i*(periodicSobolevNorm i e + T^(i-s₀)*‖e‖)) :
    (∑ i ∈ Finset.range (s+1), T^(s-i-s₀)*periodicSobolevNorm i (Q₀ e)) ≤
      (((s : ℝ)+2)*(∑ i ∈ Finset.range (s+1), C i)*((s : ℝ)+1)) *
        (periodicSobolevNorm s e + T^(s-s₀)*‖e‖) := by
  apply (inverseSource_moment_sum_le Q₀ e C hC s s₀ hT hinverse).trans
  exact (mul_le_mul_of_nonneg_left (source_moment_tame_le hT s₀ s e he)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ hC i))).trans_eq (by ring)

/-- The actual uncut auxiliary part has the sharp linear source profile.
Its constant is selected before the current coefficients, masks, inverse,
carrier family, source, and any sampled row. The paired premise is exactly the
current inverse/raw producer, not a bound for the auxiliary output. Primitive
image-factor and exterior jets spend reserve `s₀+1`, once, before the source
norm is inserted (`app:ch_mean_pairs:eq:block-normal`). -/
theorem exists_uncutAuxiliary_source_profile {n : ℕ} {ι : Type*} [Fintype ι]
    {M : ℝ} (hM : 0 ≤ M) (Craw Ccoef : ℕ → ℝ)
    (hCraw : ∀ s, 0 ≤ Craw s) (hCcoef : ∀ s, 0 ≤ Ccoef s) (s₀ : ℕ) :
    ∃ CE : ℕ → ℝ, (∀ s, 0 ≤ CE s) ∧
      ∀ (T : ℝ), 1 ≤ T →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc ψ : C(Torus n, ℝ))
        (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
        (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
        (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)),
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ M) →
      (∀ s a j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ Ccoef s*T^(s-s₀)) →
      (∀ j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1-ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ M) →
      (∀ s j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1-ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ Ccoef s*T^(s-s₀)) →
      ∀ (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
        (hreg : ∀ (e : SmoothResidual n) (j : ℕ),
          (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
            (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ι j),
      (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
        (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q₀ w) +
          (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s
            ((augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint (Q₀ w)) ≤
        Craw s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-s₀)*‖w‖)) →
      ∀ (e : SmoothResidual n) (s : ℕ),
        residualSobolevSeminorm n s
          (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e) ≤
        CE s*(residualSobolevSeminorm n s e + T^(s-s₀)*‖smoothResidualToL2 n e‖) := by
  choose D hD hbound using fun s ↦
    exists_preparationAuxiliaryCorrection_tame_bound (n := n) (ι := ι) s hM
  refine ⟨fun s ↦ D s*(Craw s+2*(1+Ccoef s)*Craw 0), ?_, ?_⟩
  · intro s
    exact mul_nonneg (hD s) (add_nonneg (hCraw s)
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hCcoef s])) (hCraw 0)))
  intro T hT c hc χmeas χsrc ψ hm hs hψ hlow hhigh hextLow hextHigh U Q₀ hreg hpair e s
  let raw := (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
    (Q₀ (smoothResidualToL2 n e))
  let R := residualSobolevSeminorm n s e + T^(s-s₀)*‖smoothResidualToL2 n e‖
  have hT0 := zero_le_one.trans hT
  have hcoef0 := hCcoef s
  have hrawC0 := hCraw 0
  have hRs : 0 ≤ residualSobolevSeminorm n s e := apply_nonneg _ _
  have hRlow : T^(s-s₀)*‖smoothResidualToL2 n e‖ ≤ R := le_add_of_nonneg_left hRs
  have hraws : (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s raw ≤ Craw s*R := by
    have hb := (le_add_of_nonneg_left
      ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s
        (Q₀ (smoothResidualToL2 n e)))).trans (hpair s _ (smoothResidualToL2_mem e s))
    simpa only [← residualSobolevSeminorm_eq_gradeNorm] using hb
  have hraw0 : ‖raw‖ ≤ 2*Craw 0*‖smoothResidualToL2 n e‖ := by
    have hb := (le_add_of_nonneg_left
      ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg 0
        (Q₀ (smoothResidualToL2 n e)))).trans (hpair 0 _ (smoothResidualToL2_mem e 0))
    simp only [GradedScale.gradeNorm_zero, Nat.zero_sub, pow_zero, one_mul] at hb
    exact hb.trans_eq (by ring)
  have hcoef : 1+Ccoef s*T^(s-s₀) ≤ (1+Ccoef s)*T^(s-s₀) := by
    have hp : 1 ≤ T^(s-s₀) := one_le_pow₀ hT
    nlinarith
  have hlowPart : (1+Ccoef s*T^(s-s₀))*‖raw‖ ≤ 2*(1+Ccoef s)*Craw 0*R := by
    calc
      _ ≤ ((1+Ccoef s)*T^(s-s₀))*(2*Craw 0*‖smoothResidualToL2 n e‖) :=
        mul_le_mul hcoef hraw0 (norm_nonneg _) (by positivity)
      _ = (2*(1+Ccoef s)*Craw 0)*(T^(s-s₀)*‖smoothResidualToL2 n e‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hRlow (by positivity)
  have hout := hbound s c hc χmeas χsrc ψ hm hs hψ (Ccoef s*T^(s-s₀))
    (mul_nonneg (hCcoef s) (pow_nonneg hT0 _)) hlow (hhigh s) hextLow (hextHigh s)
    U Q₀ hreg e
  exact (hout.trans (mul_le_mul_of_nonneg_left (add_le_add hraws hlowPart) (hD s))).trans_eq
    (by dsimp only [R]; ring)

/-- Exact-order transfer from the physical Cartesian words of the SAME real
vector field to its original centered periodization. The constant contains
only dimension and derivative-order counts, not sample/band counts or a
Sobolev embedding shift (`app:ch_mean_pairs:eq:block-normal`,
`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem periodicSobolevNorm_vectorPeriodization_le_coordinate_bound {n N : ℕ}
    (s : ℕ) {r M : ℝ} (hr : r < 1/2) (hM : 0 ≤ M)
    (f : Euclidean n → Euclidean N) (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r})
    (hcoord : ∀ ds : List (Fin n), ds.length ≤ s →
      MemLp (BallExtension.cartesianCoordinateDerivList ds f) 2 volume ∧
      lpNorm (BallExtension.cartesianCoordinateDerivList ds f) 2 volume ≤ M) :
    periodicSobolevNorm s (UniformStep.Periodization.vectorPeriodization f) ≤
      (Real.sqrt (s.factorial : ℝ)*((sobolevMultiindices n s).card : ℝ))*M := by
  open LocalSobolev BallExtension in
  have hcart : cartesianJetNorm univ s (fun j ↦ iteratedFDeriv ℝ j f) ≤
      ((sobolevMultiindices n s).card : ℝ)*M := by
    have hjet (α : Fin n → ℕ) :
        cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α =
          cartesianCoordinateDerivList (sobolevDerivativeList α) f := by
      funext x
      have h := cartesianCoordinateDerivList_eq_iteratedFDerivWithin
        isOpen_univ hf.contDiffOn (sobolevDerivativeList α) (mem_univ x)
      dsimp only at h
      rw [iteratedFDerivWithin_univ] at h
      exact h.symm
    have hsingle (α : Option (Fin n) → ℕ) (hα : α ∈ sobolevMultiindices n s) :
        lpNorm (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
          (fun i ↦ α (some i))) 2 volume ≤ M ∧
        MemLp (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
          (fun i ↦ α (some i))) 2 volume := by
      rw [hjet]
      have hlength : (sobolevDerivativeList (fun i ↦ α (some i))).length ≤ s := by
        rw [sobolevDerivativeList_length]
        have hh := mem_sobolevMultiindices.mp hα
        omega
      exact ⟨(hcoord _ hlength).2, (hcoord _ hlength).1⟩
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hM, ?_⟩
    calc
      cartesianJetEnergy univ s (fun j ↦ iteratedFDeriv ℝ j f) =
          ∑ α ∈ sobolevMultiindices n s,
            (lpNorm (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
              (fun i ↦ α (some i))) 2 volume)^2 := by
        unfold cartesianJetEnergy
        apply Finset.sum_congr rfl
        intro α hα
        simp only [Measure.restrict_univ]
        symm
        simpa only [toReal_eLpNorm] using
          eLpNorm_toReal_sq_eq_integral_norm_sq (hsingle α hα).2
      _ ≤ (∑ α ∈ sobolevMultiindices n s,
            lpNorm (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
              (fun i ↦ α (some i))) 2 volume)^2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ by
          rw [← toReal_eLpNorm]; exact ENNReal.toReal_nonneg)
      _ ≤ (∑ _α ∈ sobolevMultiindices n s, M)^2 := by
        apply pow_le_pow_left₀
        · exact Finset.sum_nonneg fun _ _ ↦ by rw [← toReal_eLpNorm]; exact ENNReal.toReal_nonneg
        · exact Finset.sum_le_sum fun α hα ↦ (hsingle α hα).1
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  exact ((UniformStep.Periodization.periodicSobolevNorm_vectorPeriodization_le hr hs hf s).trans
    (mul_le_mul_of_nonneg_left hcart (Real.sqrt_nonneg _))).trans_eq (by ring)

private theorem nested_source_moment_le {T : ℝ} (hT : 1 ≤ T)
    (s₀ : ℕ) {s d q : ℕ} (hds : d ≤ s) (hqd : q ≤ d)
    (H : ℕ → ℝ) (hH : ∀ i, 0 ≤ H i) :
    T^(d-q-s₀)*(∑ i ∈ Finset.range (q+1), T^(q-i-s₀)*H i) ≤
      ∑ i ∈ Finset.range (s+1), T^(s-i-s₀)*H i := by
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum fun i hi ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : q+1 ≤ s+1))
      (fun i _ _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (hH i)))
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ = (T^(d-q-s₀)*T^(q-i-s₀))*H i := by ring
    _ ≤ T^(d-i-s₀)*H i := mul_le_mul_of_nonneg_right
      (by
        rw [← pow_add]
        apply pow_le_pow_right₀ hT
        have hh := sourceGrade_add_le (d-q) (q-i) s₀
        omega) (hH i)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hT (by omega : d-i-s₀ ≤ s-i-s₀)) (hH i)

private theorem coordinateWord_clm {n : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin n)) :
    BallExtension.cartesianCoordinateDerivList ds (L ∘ f) =
      L ∘ BallExtension.cartesianCoordinateDerivList ds f := by
  funext x
  have hword := BallExtension.cartesianCoordinateDerivList_eq_iteratedFDerivWithin
    isOpen_univ hf.contDiffOn ds (Set.mem_univ x)
  have hcomp := BallExtension.cartesianCoordinateDerivList_eq_iteratedFDerivWithin
    isOpen_univ (L.contDiff.comp hf).contDiffOn ds (Set.mem_univ x)
  dsimp only at hword hcomp
  rw [iteratedFDerivWithin_univ] at hword hcomp
  rw [hcomp, L.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  exact congrArg L hword.symm

private theorem scalar_coordinateWord_eq {n : ℕ} {f : Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (ds : List (Fin n)) :
    BallExtension.cartesianCoordinateDerivList ds f = euclideanCoordinateDerivList ds f := by
  funext x
  have hword := BallExtension.cartesianCoordinateDerivList_eq_iteratedFDerivWithin
    isOpen_univ hf.contDiffOn ds (mem_univ x)
  dsimp only at hword
  rw [iteratedFDerivWithin_univ] at hword
  have h := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv hf ds.get x
  rw [List.ofFn_get] at h
  rw [hword, h]
  simp only [EuclideanSpace.basisFun_apply]

private theorem vector_lpNorm_le_sum {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : MemLp f 2 volume) : lpNorm f 2 volume ≤ ∑ i, lpNorm (fun x ↦ f x i) 2 volume := by
  classical
  let F : Euclidean n → ℝ := ∑ i, fun x ↦ ‖f x i‖
  have hFi (i : Fin N) := (hf.eval_piLp i).norm
  have hF : MemLp F 2 volume := memLp_finsetSum' _ (fun i _ ↦ hFi i)
  have hpoint (x : Euclidean n) : ‖f x‖ ≤ 1*‖F x‖ := by
    simp only [F, Finset.sum_apply]
    rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
      EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)
  have hb := LocalSobolev.eLpNorm_toReal_le_mul_of_bound hf.aestronglyMeasurable hF
    zero_le_one hpoint
  simp only [toReal_eLpNorm, one_mul] at hb
  apply hb.trans
  apply (lpNorm_sum_le (fun i _ ↦ hFi i) (by norm_num)).trans_eq
  exact Finset.sum_congr rfl (fun i _ ↦ lpNorm_norm (hf.eval_piLp i).aestronglyMeasurable 2)

private def realScalarFamily {n : ℕ} (W : Fin n → Euclidean n → ℂ) :
    Euclidean n → Euclidean n := fun x ↦ WithLp.toLp 2 (fun i ↦ 2*(W i x).re)

private theorem realScalarFamily_smooth {n : ℕ} (W : Fin n → Euclidean n → ℂ)
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) : ContDiff ℝ ∞ (realScalarFamily W) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp (hW i))

private theorem realScalarFamily_support {n : ℕ} (W : Fin n → Euclidean n → ℂ)
    {K : Set (Euclidean n)} (hK : IsClosed K) (hW : ∀ i, tsupport (W i) ⊆ K) :
    tsupport (realScalarFamily W) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  apply hx
  ext i
  change 2*(W i x).re = 0
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hxK (hW i h))]
  simp

private theorem realScalarFamily_word_bound {n : ℕ} (W : Fin n → Euclidean n → ℂ)
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (ds : List (Fin n)) {M : ℝ}
    (hcoord : ∀ i, MemLp (euclideanCoordinateDerivList ds (W i)) 2 volume ∧
      lpNorm (euclideanCoordinateDerivList ds (W i)) 2 volume ≤ M) :
    MemLp (BallExtension.cartesianCoordinateDerivList ds (realScalarFamily W)) 2 volume ∧
      lpNorm (BallExtension.cartesianCoordinateDerivList ds (realScalarFamily W)) 2 volume ≤
        (2*(n : ℝ))*M := by
  have hg := realScalarFamily_smooth W hW
  let L : ℂ →L[ℝ] ℝ := (2 : ℝ) • Complex.reCLM
  have heq (i : Fin n) :
      (fun x ↦ BallExtension.cartesianCoordinateDerivList ds (realScalarFamily W) x i) =
        L ∘ euclideanCoordinateDerivList ds (W i) := by
    have hp := coordinateWord_clm (EuclideanSpace.proj (𝕜 := ℝ) i) hg ds
    have hr := coordinateWord_clm L (hW i) ds
    change BallExtension.cartesianCoordinateDerivList ds (L ∘ W i) = _ at hp
    rw [hr, scalar_coordinateWord_eq (hW i) ds] at hp
    exact hp.symm
  have hm (i : Fin n) : MemLp
      (fun x ↦ BallExtension.cartesianCoordinateDerivList ds (realScalarFamily W) x i) 2 volume := by
    rw [heq i]
    exact L.comp_memLp' (hcoord i).1
  have hb (i : Fin n) : lpNorm
      (fun x ↦ BallExtension.cartesianCoordinateDerivList ds (realScalarFamily W) x i) 2 volume ≤ 2*M := by
    rw [heq i]
    have hpoint (x : Euclidean n) :
        ‖(L ∘ euclideanCoordinateDerivList ds (W i)) x‖ ≤
          2*‖euclideanCoordinateDerivList ds (W i) x‖ := by
      change ‖(2 : ℝ)*(euclideanCoordinateDerivList ds (W i) x).re‖ ≤ _
      rw [norm_mul, Real.norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _) (by norm_num)
    have h := LocalSobolev.eLpNorm_toReal_le_mul_of_bound
      (L.comp_memLp' (hcoord i).1).aestronglyMeasurable (hcoord i).1 (by norm_num) hpoint
    simp only [toReal_eLpNorm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hcoord i).2 (by norm_num))
  have hmem := MemLp.of_eval_piLp hm
  refine ⟨hmem, (vector_lpNorm_le_sum hmem).trans ?_⟩
  exact (Finset.sum_le_sum (fun i _ ↦ hb i)).trans_eq (by simp; ring)

/-- The fixed physical-coordinate budget for the complete native forward
row. Only physical dimension and derivative orders are counted; the constant
precedes the native measure, samples, bands and source. -/
def realForwardSobolevConstant (n : ℕ) (Rbox : ℝ) (a p : ℕ → ℝ) (s : ℕ) : ℝ :=
  Real.sqrt (s.factorial : ℝ)*((sobolevMultiindices n s).card : ℝ)*(2*(n : ℝ)) *
    ∑ j ∈ Finset.range (s+1), forwardDerivativeConstant n Rbox a p j

/-- Nonnegativity of the fixed full forward budget. -/
theorem realForwardSobolevConstant_nonneg (n : ℕ) (Rbox : ℝ) (a p : ℕ → ℝ) (s : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ realForwardSobolevConstant n Rbox a p s := by
  unfold realForwardSobolevConstant
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ ↦ forwardDerivativeConstant_nonneg n Rbox a p j ha hp)

/-- The FULL aggregate native real row maps its original radial input moments
to the SAME periodic Sobolev order. This constructs the smooth representative,
uses the original scalar branch operators, and proves its equality with the
native row. Neither a forward derivative bound nor a successful response is a
premise. The native halfweight remains in `m`; integer radial powers are added
only to the common aggregate input (`app:ch_mean_pairs:eq:block-normal`). -/
theorem nativeRealForward_sobolev_bound {n : ℕ} {ι : Type*}
    [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    (μ : Measure (ι × Euclidean (n-1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n-1)) → Euclidean n → ℝ)
    (Φ : ι → Euclidean (n-1) → Euclidean n → ℝ)
    (a : Fin n → Unit → ι → Euclidean (n-1) → Euclidean n → ℂ)
    (m : (ι × Euclidean (n-1)) → ℝ)
    (hφ : Continuous (Function.uncurry φ))
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (ha : ∀ i j k, ContDiff ℝ ∞ (Function.uncurry (a i j k)))
    (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ u, m u ≠ 0 → 1 ≤ ‖u.2‖)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (has : ∀ i j k η, tsupport (a i j k η) ⊆ K)
    (hagree : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x)
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) {Rbox : ℝ} (hRbox : Rbox < 1/2)
    (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s₀ : ℕ} {T : ℝ} (hT : 1 ≤ T) (B p : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hp : ∀ j, 0 ≤ p j)
    (hamp : ∀ i j k η, m (k,η) ≠ 0 → ∀ x ∈ K, ∀ t,
      ‖iteratedFDeriv ℝ t (a i j k η) x‖ ≤ B t*T^(t-(s₀+(n/2+1))))
    (hphase : ∀ k η, m (k,η) ≠ 0 → ∀ x ∈ K, ∀ t, 1 ≤ t →
      ‖iteratedFDeriv ℝ t (fun y ↦ Φ k η y/‖η‖) x‖ ≤ p t*T^(t-1-(s₀+(n/2+1))))
    (T₀ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT₀ : ∀ v : Lp ℂ 2 μ, T₀ v =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x z*v z ∂μ)
    (s : ℕ) (v : Lp ℂ 2 μ)
    (hweight : ∀ q ≤ s, MemLp (fun z ↦ (‖z.2‖ : ℂ)^q*v z) 2 μ) :
    let entries := sampledMomentMatrixEntry μ φ m a hφ hm hms ha hK has
    let S := nativeScalarRowsToVector μ (fun i ↦ entries i ())
    let w := transferOutputOperator (realQuadratureChannel S) v
    w ∈ periodicSobolevLevel n (Euclidean n) s ∧
      periodicSobolevNorm s w ≤ realForwardSobolevConstant n Rbox B p s*‖T₀‖ *
        ∑ q ∈ Finset.range (s+1), T^(s-q-s₀)*lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*v z) 2 μ := by
  classical
  intro entries S w
  let W : Fin n → Euclidean n → ℂ := fun i x ↦ ∫ z,
    physicalForwardKernel φ m (fun z y ↦ star (a i () z.1 z.2 y)) x z*v z ∂μ
  have hW (i : Fin n) := sampledForward_physical_coordinate_bounds μ φ Φ
    (fun k η x ↦ star (a i () k η x)) m hφ hΦ
    (fun k ↦ Complex.conjCLE.contDiff.comp (ha i () k)) hm hms hhigh
    hK (fun k η ↦ (tsupport_comp_subset (map_zero Complex.conjCLE) (a i () k η)).trans
      (has i () k η)) hagree χ hχ hχs hχK
    Rbox hbox hT B p hB hp
    (fun k η hk x hx t ↦ (Complex.conjLIE.norm_iteratedFDeriv_comp_left (a i () k η) x t).trans_le
      (hamp i () k η hk x hx t)) hphase T₀ hT₀ v
  let D := ∑ j ∈ Finset.range (s+1), forwardDerivativeConstant n Rbox B p j
  let M := ∑ q ∈ Finset.range (s+1), T^(s-q-s₀)*lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*v z) 2 μ
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ forwardDerivativeConstant_nonneg n Rbox B p j hB hp
  have hM : 0 ≤ M := Finset.sum_nonneg fun q _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) lpNorm_nonneg
  have hWbound (ds : List (Fin n)) (hds : ds.length ≤ s) (i : Fin n) :
      MemLp (euclideanCoordinateDerivList ds (W i)) 2 volume ∧
      lpNorm (euclideanCoordinateDerivList ds (W i)) 2 volume ≤ D*‖T₀‖*M := by
    refine ⟨(hW i).2.2.1 ds, ?_⟩
    have hb := (hW i).2.2.2 ds (fun q hq ↦ hweight q (hq.trans hds))
    simp only [toReal_eLpNorm] at hb
    have hmoment : (∑ q ∈ Finset.range (ds.length+1),
        T^(ds.length-q-s₀)*lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*v z) 2 μ) ≤ M := by
      apply (Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT (by omega : ds.length-q-s₀ ≤ s-q-s₀)) lpNorm_nonneg).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun q _ _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) lpNorm_nonneg)
    have hconst : forwardDerivativeConstant n Rbox B p ds.length ≤ D :=
      Finset.single_le_sum (fun j _ ↦ forwardDerivativeConstant_nonneg n Rbox B p j hB hp)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hds))
    exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_right hconst (norm_nonneg _)) hmoment
      (Finset.sum_nonneg fun q _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) lpNorm_nonneg)
      (mul_nonneg hD (norm_nonneg _)))
  let f := realScalarFamily W
  have hf : ContDiff ℝ ∞ f := realScalarFamily_smooth W (fun i ↦ (hW i).1)
  have hfs : tsupport f ⊆ {x | ∀ i, |x i| ≤ Rbox} :=
    (realScalarFamily_support W hK.isClosed (fun i ↦ (hW i).2.1)).trans hbox
  have hSa : S v =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦ W i x) := by
    have hcoord (i : Fin n) : (fun x ↦ S v x i) =ᵐ[volume] W i := by
      apply (finiteL2Coordinates_apply_ae volume (S v) i).symm.trans
      change finiteL2CoordinateIsometry volume (S v) i =ᵐ[volume] W i
      rw [nativeScalarRowsToVector_coordinate μ (fun i ↦ entries i ()) v i]
      simpa only [entries, sampledMomentMatrixEntry, W, physicalForwardKernel, star_star] using
        sampledMomentOperator_ae_kernel μ φ m (fun z ↦ a i () z.1 z.2) hφ hm
          (continuous_originalSampledAmplitude (a i ()) (ha i ())) hms hK
          (fun z ↦ has i () z.1 z.2) v
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    ext i
    exact hx i
  have hreal : realQuadratureChannel S v =ᵐ[volume] f := by
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (l2RealPart volume (S v)),
      (euclideanRealPart (ι := Fin n)).coeFn_compLpL (S v), hSa] with x hsm hre hval
    change ((2 : ℝ) • l2RealPart volume (S v)) x = f x
    rw [hsm]
    simp only [Pi.smul_apply]
    rw [show l2RealPart volume (S v) x = euclideanRealPart (S v x) from hre, hval]
    rfl
  have hperiod : w =ᵐ[volume] UniformStep.Periodization.vectorPeriodization f :=
    (toTorus_coe (𝕜 := ℝ) (realQuadratureChannel S v)).trans
      (measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp hreal.restrict)
  let g : SmoothResidual n := ⟨fun z _ ↦ UniformStep.Periodization.vectorPeriodization f z,
    fun _ ↦ UniformStep.Periodization.isSmoothPeriodic_vectorPeriodization hRbox hfs hf⟩
  have hge : smoothResidualToL2 n g = w := by
    apply Lp.ext
    exact (SmoothPeriodicFamily.componentL2_coe_ae () g).trans hperiod.symm
  rw [← hge]
  refine ⟨smoothResidualToL2_mem g s, ?_⟩
  rw [← residualSobolevSeminorm_eq_periodicSobolevNorm,
    residualSobolevSeminorm_eq_gradeNorm, smoothResidualToL2_gradeNorm]
  change periodicSobolevNorm s (UniformStep.Periodization.vectorPeriodization f) ≤ _
  have hbudget : 0 ≤ (2*(n : ℝ))*(D*‖T₀‖*M) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hD (norm_nonneg _)) hM)
  have hb := periodicSobolevNorm_vectorPeriodization_le_coordinate_bound s hRbox
    hbudget f hf hfs
    (fun ds hds ↦ realScalarFamily_word_bound W (fun i ↦ (hW i).1) ds (hWbound ds hds))
  exact hb.trans_eq (by dsimp only [realForwardSobolevConstant, D, M]; ring)

/-- The literal fixed-source operator is its UNCUT auxiliary output plus the
SAME native sampled normal. The sole row premise is exact original-kernel
unitary realization, not a norm bound. Every source mask, coefficient, full
corrected raw response and current inverse is unchanged
(`new:eq:mean-operators`). -/
theorem fixedSourceLinear_toL2_eq_nativeNormal
    {n : ℕ} {ι ν m X : Type*} [Fintype ι] [Fintype ν] [Fintype m] [MeasurableSpace X]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ν s)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (hraw : ∀ i v, smoothResidualToL2 n
      (CanonicalChange.smoothRawCrossResponse base C hC G i v) = A i v)
    (μ : Measure X) (eInput : Lp ℂ 2 μ ≃ₗᵢ[ℝ] PiLp 2 Raw)
    (Rnative : Lp ℂ 2 μ →L[ℝ] OutputL2 n)
    (hrow : (CanonicalRow.weightedRow weight A).comp
      eInput.toContinuousLinearEquiv.toContinuousLinearMap = Rnative)
    (e : SmoothResidual n) :
    smoothResidualToL2 n (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg
      weight base C hC A G e) =
      preparationAuxiliaryOutput (imageChannel c χmeas χsrc) ψ (Q₀ (smoothResidualToL2 n e)) +
        Rnative (Rnative.adjoint (Q₀ (smoothResidualToL2 n e))) := by
  rw [fixedSourceLinear_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg weight base C hC A G hweight hraw]
  simp only [uncutSampledNormal, add_apply, ContinuousLinearMap.comp_apply]
  congr 1
  rw [← hrow, ContinuousLinearMap.adjoint_comp, eInput.adjoint_eq_symm]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply]

/-- Fixed all-order linear-wave constant. The only summed labels are
integer derivative orders. The tester budget is fixed before samples,
bands, history, current coefficients, source and final physical cutoff. -/
def nativeLinearSourceConstant {n : ℕ}
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B p Cinv : ℕ → ℝ)
    (Ctest : ℝ) (s : ℕ) : ℝ :=
  realForwardSobolevConstant n Rbox B p s *
    (∑ q ∈ Finset.range (s+1), nativeAggregateSourceConstant χ hχ hc hs Rbox B Cinv q) *
      Ctest^2*((s : ℝ)+1)

/-- Nonnegativity of the actual aggregate linear-wave budget. -/
theorem nativeLinearSourceConstant_nonneg {n : ℕ}
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (Rbox : ℝ) (B p Cinv : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hp : ∀ j, 0 ≤ p j) (hCinv : ∀ j, 0 ≤ Cinv j)
    (Ctest : ℝ) (s : ℕ) : 0 ≤ nativeLinearSourceConstant χ hχ hc hs Rbox B p Cinv Ctest s := by
  unfold nativeLinearSourceConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (realForwardSobolevConstant_nonneg n Rbox B p s hB hp)
    (Finset.sum_nonneg fun q _ ↦ nativeAggregateSourceConstant_nonneg χ hχ hc hs Rbox B Cinv hB hCinv q))
    (sq_nonneg _)) (by positivity)

/-- The SAME native full measured normal after the SAME current inverse has
the required one-high Sobolev source profile. Both analytic producers are
actually applied: original aggregate CurrentAdjoint integer moments through
`nativeRealMeasuredInverseAdjoint_radial_bounds`, and the full aggregate
scalar forward branches through `nativeRealForward_sobolev_bound`. The two
moment sums are collapsed sharply BEFORE interpolation. In particular the
highest source norm is not multiplied by a positive scale power, and no
individual field at order `s+1` or Sobolev embedding occurs
(`app:ch_mean_pairs:eq:block-normal`, `new:eq:source-bound`). -/
theorem nativeRealMeasuredNormal_source_profile {n : ℕ} {ι : Type*}
    [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    (μ : Measure (ι × Euclidean (n-1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : (ι × Euclidean (n-1)) → Euclidean n → ℝ)
    (Φ : ι → Euclidean (n-1) → Euclidean n → ℝ)
    (a : Fin n → ι → Euclidean (n-1) → Euclidean n → ℂ)
    (m : (ι × Euclidean (n-1)) → ℝ)
    (hφ : Continuous (Function.uncurry φ))
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (ha : ∀ i k, ContDiff ℝ ∞ (Function.uncurry (a i k)))
    (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ u, m u ≠ 0 → 1 ≤ ‖u.2‖)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (has : ∀ i k η, tsupport (a i k η) ⊆ K)
    (hagree : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x)
    (L : ι → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (hL : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n-1) × Euclidean n ↦ L i p.1 h p.2))
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ halfOpenCell n) (hχK : ∀ x ∈ K, χ x = 1)
    {Rbox : ℝ} (hRbox : Rbox < 1/2) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (Tfull : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ v : Lp ℂ 2 μ, Tfull v =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x z*v z ∂μ)
    (hφsmooth : ∀ z, ContDiff ℝ ∞ (φ z))
    (hphaseL : ∀ z, m z ≠ 0 → ∀ h x, x ∈ K →
      inner ℝ h z.2 = fderiv ℝ (φ z) x (L z.1 z.2 h x))
    {s₀ : ℕ} {T : ℝ} (hT : 1 ≤ T) (B p Cinv : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hp : ∀ j, 0 ≤ p j) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hamp : ∀ i k η, m (k,η) ≠ 0 → ∀ x ∈ K, ∀ t,
      ‖iteratedFDeriv ℝ t (a i k η) x‖ ≤ B t*T^(t-(s₀+(n/2+1))))
    (hcoeff : ∀ k η, m (k,η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ t,
      ‖iteratedFDeriv ℝ t (L k η h) x‖ ≤ B t*T^(t-(s₀+(n/2+1))))
    (hphase : ∀ k η, m (k,η) ≠ 0 → ∀ x ∈ K, ∀ t, 1 ≤ t →
      ‖iteratedFDeriv ℝ t (fun y ↦ Φ k η y/‖η‖) x‖ ≤ p t*T^(t-1-(s₀+(n/2+1))))
    {Ctest : ℝ} (hCtest : 0 ≤ Ctest) (htest : ‖Tfull‖ ≤ Ctest)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : SmoothResidual n)
    (hregular : ∀ s, Q₀ (smoothResidualToL2 n e) ∈ periodicSobolevLevel n (Euclidean n) s)
    (hinverse : ∀ k : ℕ, periodicSobolevNorm k (Q₀ (smoothResidualToL2 n e)) ≤
      Cinv k*(periodicSobolevNorm k (smoothResidualToL2 n e) +
        T^(k-s₀)*‖smoothResidualToL2 n e‖)) (s : ℕ) :
    let S := nativeMeasuredRow μ φ m a hφ hm hms ha hK has
    let R := transferOutputOperator (realQuadratureChannel S)
    let w := R (R.adjoint (Q₀ (smoothResidualToL2 n e)))
    w ∈ periodicSobolevLevel n (Euclidean n) s ∧
      periodicSobolevNorm s w ≤ nativeLinearSourceConstant χ hχ hχc hχs Rbox B p Cinv Ctest s *
        (residualSobolevSeminorm n s e + T^(s-s₀)*‖smoothResidualToL2 n e‖) := by
  classical
  intro S R w
  let u := smoothResidualToL2 n e
  let raw := nativeRealMeasuredInverseAdjoint μ φ m a hφ hm hms ha hK has Q₀ u
  have hmom (q : ℕ) := nativeRealMeasuredInverseAdjoint_radial_bounds μ φ m a hφ hm hms ha hK has
    L hL χ hχ hχc hχs hχK Rbox hbox Tfull hTfull hφsmooth hphaseL B hB q s₀ hT hamp hcoeff
    Q₀ u hregular Cinv hCinv (fun k _ ↦ hinverse k)
  have hforward := nativeRealForward_sobolev_bound μ φ Φ (fun i (_ : Unit) ↦ a i) m hφ hΦ
    (fun i _ ↦ ha i) hm hms hhigh hK (fun i _ ↦ has i) hagree χ hχ.continuous hχc hχK hRbox hbox
    hT B p hB hp (fun i _ ↦ hamp i) hphase Tfull hTfull s raw (fun q _ ↦ (hmom q).1)
  change w ∈ periodicSobolevLevel n (Euclidean n) s ∧ periodicSobolevNorm s w ≤ _ at hforward
  refine ⟨hforward.1, ?_⟩
  let Cq := nativeAggregateSourceConstant χ hχ hχc hχs Rbox B Cinv
  let Csum := ∑ q ∈ Finset.range (s+1), Cq q
  let M := ∑ k ∈ Finset.range (s+1), T^(s-k-s₀)*periodicSobolevNorm k u
  have hCq (q : ℕ) : 0 ≤ Cq q := nativeAggregateSourceConstant_nonneg χ hχ hχc hχs Rbox B Cinv hB hCinv q
  have hCs : 0 ≤ Csum := Finset.sum_nonneg fun q _ ↦ hCq q
  have hM : 0 ≤ M := Finset.sum_nonneg fun k _ ↦
    mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (Real.sqrt_nonneg _)
  have hconv : (∑ q ∈ Finset.range (s+1),
      T^(s-q-s₀)*lpNorm (fun z ↦ (‖z.2‖ : ℂ)^q*raw z) 2 μ) ≤ Csum*‖Tfull‖*M := by
    calc
      _ ≤ ∑ q ∈ Finset.range (s+1), Cq q*‖Tfull‖*M := by
        apply Finset.sum_le_sum
        intro q hq
        calc
          _ ≤ T^(s-q-s₀)*(Cq q*‖Tfull‖*
              ∑ k ∈ Finset.range (q+1), T^(q-k-s₀)*periodicSobolevNorm k u) :=
            mul_le_mul_of_nonneg_left (hmom q).2.1 (pow_nonneg (zero_le_one.trans hT) _)
          _ = Cq q*‖Tfull‖*(T^(s-q-s₀)*
              ∑ k ∈ Finset.range (q+1), T^(q-k-s₀)*periodicSobolevNorm k u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (nested_source_moment_le hT s₀ le_rfl (Nat.le_of_lt_succ (Finset.mem_range.mp hq))
              (fun k ↦ periodicSobolevNorm k u) (fun _ ↦ (Real.sqrt_nonneg _)))
            (mul_nonneg (hCq q) (norm_nonneg _))
      _ = _ := by dsimp only [Csum]; rw [Finset.sum_mul, Finset.sum_mul]
  have hF := realForwardSobolevConstant_nonneg n Rbox B p s hB hp
  have hsource := source_moment_tame_le hT s₀ s u (smoothResidualToL2_mem e s)
  rw [residualSobolevSeminorm_eq_periodicSobolevNorm]
  have htest2 : ‖Tfull‖^2 ≤ Ctest^2 := pow_le_pow_left₀ (norm_nonneg _) htest 2
  calc
    _ ≤ realForwardSobolevConstant n Rbox B p s*‖Tfull‖*(Csum*‖Tfull‖*M) :=
      hforward.2.trans (mul_le_mul_of_nonneg_left hconv (mul_nonneg hF (norm_nonneg _)))
    _ = (realForwardSobolevConstant n Rbox B p s*Csum*‖Tfull‖^2)*M := by ring
    _ ≤ (realForwardSobolevConstant n Rbox B p s*Csum*Ctest^2) *
        (((s : ℝ)+1)*(periodicSobolevNorm s u + T^(s-s₀)*‖u‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htest2 (mul_nonneg hF hCs)) hsource hM
        (mul_nonneg (mul_nonneg hF hCs) (pow_nonneg hCtest _))
    _ = _ := by dsimp only [nativeLinearSourceConstant, Csum, Cq, u]; ring

/-- The actual all-order linear input for the fixed-cutoff Picard source
profiles. `CE` is chosen BEFORE history, current coefficients/inverse, native
measure, samples, corrected fields, source and final physical cutoff. The
proof applies BOTH the original UNCUT image/exterior auxiliary producer and
the FULL aggregate measured-wave producer. The literal current normal
identity is retained in the conclusion. Primitive coefficient and positive
current-density inputs retain their original upstream producers; this does
not assert their still-open actual-history instantiation
(`new:eq:mean-operators`, `new:eq:source-bound`). -/
theorem exists_fixedSourceLinear_source_profile {n : ℕ} {ν : Type*} [Fintype ν]
    {M : ℝ} (hM : 0 ≤ M) (Craw Ccoef B p : ℕ → ℝ)
    (hCraw : ∀ s, 0 ≤ Craw s) (hCcoef : ∀ s, 0 ≤ Ccoef s)
    (hB : ∀ s, 0 ≤ B s) (hp : ∀ s, 0 ≤ p s)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ halfOpenCell n) {Rbox : ℝ} (hRbox : Rbox < 1/2)
    {Ctest : ℝ} (hCtest : 0 ≤ Ctest) :
    let s₀ := RevisedScales.sourceOrder n
    ∃ CE : ℕ → ℝ, (∀ s, 0 ≤ CE s) ∧
      ∀ (T : ℝ), 1 ≤ T →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
        (χmeas χsrc ψ : C(Torus n, ℝ))
        (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
        (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
        (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)),
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ M) →
      (∀ s a j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ Ccoef s*T^(s-s₀)) →
      (∀ j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1-ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ M) →
      (∀ s j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1-ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ Ccoef s*T^(s-s₀)) →
      ∀ (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
        (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
          (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
            (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ν s),
      (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
        Q₀ w ∈ periodicSobolevLevel n (Euclidean n) s) →
      (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
        (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q₀ w) +
          (CarrierSobolev.augmentedInputSobolevScale n ν).gradeNorm s
            ((augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint (Q₀ w)) ≤
        Craw s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-s₀)*‖w‖)) →
      ∀ {ι σ m : Type*} [Fintype ι] [Fintype m] [Fintype σ] [MetricSpace σ]
        [DiscreteTopology σ] [MeasurableSpace σ] [BorelSpace σ]
        {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
        [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
        (weight : ι → ℝ), (∀ i, 0 ≤ weight i) →
      ∀ (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
        (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
        (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
        (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ)),
      (∀ i v, smoothResidualToL2 n
        (CanonicalChange.smoothRawCrossResponse base C hC G i v) = A i v) →
      ∀ (μ : Measure (σ × Euclidean (n-1))) [IsLocallyFiniteMeasure μ] [SFinite μ]
        (eInput : Lp ℂ 2 μ ≃ₗᵢ[ℝ] PiLp 2 Raw)
        (φ : (σ × Euclidean (n-1)) → Euclidean n → ℝ)
        (Φ : σ → Euclidean (n-1) → Euclidean n → ℝ)
        (a : Fin n → σ → Euclidean (n-1) → Euclidean n → ℂ)
        (mask : (σ × Euclidean (n-1)) → ℝ)
        (hφ : Continuous (Function.uncurry φ))
        (_hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
        (ha : ∀ i k, ContDiff ℝ ∞ (Function.uncurry (a i k)))
        (hmask : Continuous mask) (hmaskc : HasCompactSupport mask),
      (∀ u, mask u ≠ 0 → 1 ≤ ‖u.2‖) →
      ∀ (K : Set (Euclidean n)) (hK : IsCompact K)
        (has : ∀ i k η, tsupport (a i k η) ⊆ K),
      (∀ u, mask u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x) →
      ∀ (L : σ → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n),
      (∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n-1) × Euclidean n ↦ L i p.1 h p.2)) →
      (∀ x ∈ K, χ x = 1) → (∀ x ∈ K, ∀ i, |x i| ≤ Rbox) →
      ∀ (Tfull : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n))),
      (∀ v : Lp ℂ 2 μ, Tfull v =ᵐ[volume] fun x ↦ ∫ z,
        sampledMomentKernel φ mask (fun _ y ↦ (χ y : ℂ)) x z*v z ∂μ) →
      (∀ z, ContDiff ℝ ∞ (φ z)) →
      (∀ z, mask z ≠ 0 → ∀ h x, x ∈ K →
        inner ℝ h z.2 = fderiv ℝ (φ z) x (L z.1 z.2 h x)) →
      (∀ i k η, mask (k,η) ≠ 0 → ∀ x ∈ K, ∀ t,
        ‖iteratedFDeriv ℝ t (a i k η) x‖ ≤ B t*T^(t-(s₀+(n/2+1)))) →
      (∀ k η, mask (k,η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ t,
        ‖iteratedFDeriv ℝ t (L k η h) x‖ ≤ B t*T^(t-(s₀+(n/2+1)))) →
      (∀ k η, mask (k,η) ≠ 0 → ∀ x ∈ K, ∀ t, 1 ≤ t →
        ‖iteratedFDeriv ℝ t (fun y ↦ Φ k η y/‖η‖) x‖ ≤ p t*T^(t-1-(s₀+(n/2+1)))) →
      ‖Tfull‖ ≤ Ctest →
      (CanonicalRow.weightedRow weight A).comp eInput.toContinuousLinearEquiv.toContinuousLinearMap =
        transferOutputOperator (realQuadratureChannel
          (nativeMeasuredRow μ φ mask a hφ hmask hmaskc ha hK has)) →
      ∀ (e : SmoothResidual n) (s : ℕ),
        residualSobolevSeminorm n s
          (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg weight base C hC A G e) ≤
          CE s*(residualSobolevSeminorm n s e + T^(s-s₀)*‖smoothResidualToL2 n e‖) ∧
        smoothResidualToL2 n
          (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg weight base C hC A G e) =
          uncutSampledNormal c χmeas χsrc ψ weight A (Q₀ (smoothResidualToL2 n e)) := by
  intro s₀
  obtain ⟨Caux, hCaux, haux⟩ := exists_uncutAuxiliary_source_profile (n := n) (ι := ν)
    hM Craw Ccoef hCraw hCcoef s₀
  let Cwave := nativeLinearSourceConstant χ hχ hχc hχs Rbox B p Craw Ctest
  have hCwave (s : ℕ) : 0 ≤ Cwave s :=
    nativeLinearSourceConstant_nonneg χ hχ hχc hχs Rbox B p Craw hB hp hCraw Ctest s
  refine ⟨fun s ↦ Caux s+Cwave s, fun s ↦ add_nonneg (hCaux s) (hCwave s), ?_⟩
  intro T hT c hc χmeas χsrc ψ hm hs hψ hlow hhigh hextLow hextHigh U Q₀ hreg hQreg hpair
    ι σ m _ _ _ _ _ _ _ Raw _ _ _ weight hweight base C hC A G hraw μ _ _ eInput φ Φ a mask
    hφ hΦ ha hmask hmaskc hfreq K hK has hagree L hL hχK hbox Tfull hTfull hφsmooth hphaseL
    hamp hcoeff hphase htest hrow e s
  let Z := preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e
  let E := fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg weight base C hC A G
  let R := transferOutputOperator (realQuadratureChannel
    (nativeMeasuredRow μ φ mask a hφ hmask hmaskc ha hK has))
  have hQ (k : ℕ) := hQreg k (smoothResidualToL2 n e) (smoothResidualToL2_mem e k)
  have hinverse (k : ℕ) : periodicSobolevNorm k (Q₀ (smoothResidualToL2 n e)) ≤
      Craw k*(periodicSobolevNorm k (smoothResidualToL2 n e) + T^(k-s₀)*‖smoothResidualToL2 n e‖) := by
    have hb := (le_add_of_nonneg_right
      ((CarrierSobolev.augmentedInputSobolevScale n ν).gradeNorm_nonneg k
        ((augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint (Q₀ (smoothResidualToL2 n e))))).trans
      (hpair k _ (smoothResidualToL2_mem e k))
    rw [(periodicSobolevScale n (Euclidean n)).gradeNorm_eq (hQ k),
      (periodicSobolevScale n (Euclidean n)).gradeNorm_eq (smoothResidualToL2_mem e k)] at hb
    change periodicSobolevSeminorm k ⟨Q₀ (smoothResidualToL2 n e), hQ k⟩ ≤
      Craw k*(periodicSobolevSeminorm k ⟨smoothResidualToL2 n e, smoothResidualToL2_mem e k⟩ +
        T^(k-s₀)*‖smoothResidualToL2 n e‖) at hb
    simpa only [periodicSobolevSeminorm_eq] using hb
  have hwave := nativeRealMeasuredNormal_source_profile μ φ Φ a mask hφ hΦ ha hmask hmaskc hfreq
    hK has hagree L hL χ hχ hχc hχs hχK hRbox hbox Tfull hTfull hφsmooth hphaseL hT B p Craw
    hB hp hCraw hamp hcoeff hphase hCtest htest Q₀ e hQ hinverse s
  have hZ := haux T hT c hc χmeas χsrc ψ hm hs hψ hlow hhigh hextLow hextHigh U Q₀ hreg hpair e s
  have hwhole := fixedSourceLinear_toL2_eq_nativeNormal c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg
    weight hweight base C hC A G hraw μ eInput R hrow e
  have hZreal : smoothResidualToL2 n Z =
      preparationAuxiliaryOutput (imageChannel c χmeas χsrc) ψ (Q₀ (smoothResidualToL2 n e)) :=
    preparationAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e
  let W := E e - Z
  have hW : smoothResidualToL2 n W = R (R.adjoint (Q₀ (smoothResidualToL2 n e))) := by
    dsimp only [W]
    rw [map_sub, hwhole, hZreal]
    exact add_sub_cancel_left _ _
  have hWnorm : residualSobolevSeminorm n s W ≤
      Cwave s*(residualSobolevSeminorm n s e + T^(s-s₀)*‖smoothResidualToL2 n e‖) := by
    rw [residualSobolevSeminorm_eq_periodicSobolevNorm, hW]
    exact hwave.2
  refine ⟨?_, fixedSourceLinear_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg weight base C hC A G hweight hraw e⟩
  have hsum : E e = Z+W := by dsimp only [W]; abel
  change residualSobolevSeminorm n s (E e) ≤ _
  rw [hsum]
  exact (((residualSobolevSeminorm n s).add_le' Z W).trans (add_le_add hZ hWnorm)).trans_eq (by ring)

end JanetCartan.PhysicalMean
