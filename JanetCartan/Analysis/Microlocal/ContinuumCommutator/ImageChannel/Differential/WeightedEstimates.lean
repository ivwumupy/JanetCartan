module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Estimates

/-!
# Weighted estimates for the literal finite image factors

For `app:ch_background:eq:bg-commutator`, every branch of the constructed
commutator differentiates a coefficient once. Interpolation from the fixed
first-jet baseline makes its j-th multiplier jet cost at most `(1+H)^(j/s)`.
The allocated Sobolev product estimate preserves this weight through every
actual factor and composition. Weighted datum interpolation then leaves just
one high budget times L². Constants precede the varying coefficients.

The consumer is the actual image-normal estimate, with both fixed masks and
both normal factors. No branch estimate is assumed by the primitive endpoints.
-/

@[expose] public noncomputable section

open scoped BigOperators
namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential
open PeriodicSobolevSpace ContinuumRow
namespace ImageFactorExpression

/-- Bounds the derivative words retained in the actual factor syntax
(`app:ch_background:eq:bg-commutator`). -/
def jetOrderLe {n : ℕ} {ι : Type*} (d : ℕ) : ImageFactorExpression n ι → Prop
  | .coefficient _ js => js.length ≤ d
  | .add e f | .comp e f => jetOrderLe d e ∧ jetOrderLe d f
  | .neg e => jetOrderLe d e
  | _ => True

variable {n : ℕ} {ι : Type*}

/-- Finite sums retain the primitive derivative order
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem jetOrderLe_finSum {m : ℕ} (d : ℕ)
    (f : Fin m → ImageFactorExpression n ι) :
    (finSum f).jetOrderLe d ↔ ∀ i, (f i).jetOrderLe d := by
  have h (l : List (ImageFactorExpression n ι)) :
      (l.foldr ImageFactorExpression.add ImageFactorExpression.zero).jetOrderLe d ↔
        ∀ e ∈ l, e.jetOrderLe d := by
    induction l with
    | nil => simp [jetOrderLe]
    | cons e l ih => simp [jetOrderLe, ih]
  simpa [finSum] using h (List.ofFn f)

private theorem inclusion_self (t : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) t) :
    inclusion (Nat.le_refl t) u = u := by
  apply toL2_injective t
  exact multiplier_toL2_inclusion _ _

private theorem power_product {s t j : ℕ} (hj : j ≤ t) {T : ℝ} (hT : 0 < T)
    (δ : ℝ) :
    T ^ ((j : ℝ) / s) * T ^ (((t - j : ℕ) : ℝ) / s + δ) =
      T ^ ((t : ℝ) / s + δ) := by
  rw [← Real.rpow_add hT, Nat.cast_sub hj]
  congr 1
  ring

/-- The finite factor action preserves a common weighted Sobolev budget
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_weighted_action_bound (e : ImageFactorExpression n ι)
    (he : e.jetOrderLe 1) (s : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))
      (T : ℝ), 1 ≤ T →
      (∀ a js, js.length ≤ 1 → ∀ j ≤ s,
        cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient (q a) (hq a) js)) ≤
          K * T ^ ((j : ℝ) / s)) →
      ∀ (t : ℕ), t ≤ s → ∀ (δ U : ℝ), 0 ≤ U →
      ∀ u : PeriodicSobolevSpace n (Euclidean n) t,
      (∀ r (hr : r ≤ t), ‖inclusion hr u‖ ≤ T ^ ((r : ℝ) / s + δ) * U) →
      ‖e.onSobolev q hq t u‖ ≤ C * (T ^ ((t : ℝ) / s + δ) * U) := by
  induction e with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intros
    simp [onSobolev]
  | coefficient a js =>
    let P := ∑ r ∈ Finset.range (s + 1), AuxiliaryRawBand.coefficientProductConstant n r
    have hP : 0 ≤ P := Finset.sum_nonneg fun r _ ↦ AuxiliaryRawBand.coefficientProductConstant_nonneg n r
    refine ⟨P * (s + 1) * K, by positivity, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    have hprod := norm_cutoffSobolev_le (orderedCoefficient (q a) (hq a) js)
      ((hq a).coordinateDerivList js) t u
    have hsum : (∑ j ∈ Finset.range (t + 1),
        cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient (q a) (hq a) js)) *
          ‖inclusion (Nat.sub_le t j) u‖) ≤
        (t + 1) * (K * (T ^ ((t : ℝ) / s + δ) * U)) := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (t + 1), K * (T ^ ((t : ℝ) / s + δ) * U) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjt : j ≤ t := by simpa using hj
          calc
            _ ≤ (K * T ^ ((j : ℝ) / s)) *
                (T ^ (((t-j : ℕ) : ℝ) / s + δ) * U) :=
              mul_le_mul (hcoeff a js he j (hjt.trans ht)) (hu _ (Nat.sub_le t j))
                (norm_nonneg _) (by positivity)
            _ = K * ((T ^ ((j : ℝ) / s) *
                T ^ (((t-j : ℕ) : ℝ) / s + δ)) * U) := by ring
            _ = _ := by rw [power_product hjt (by positivity)]
        _ = _ := by simp
    have hPt : AuxiliaryRawBand.coefficientProductConstant n t ≤ P :=
      Finset.single_le_sum (fun r _ ↦ AuxiliaryRawBand.coefficientProductConstant_nonneg n r)
        (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ _ := hprod
      _ ≤ AuxiliaryRawBand.coefficientProductConstant n t *
          ((t + 1) * (K * (T ^ ((t : ℝ) / s + δ) * U))) :=
        mul_le_mul_of_nonneg_left hsum (AuxiliaryRawBand.coefficientProductConstant_nonneg n t)
      _ ≤ P * ((s + 1) * (K * (T ^ ((t : ℝ) / s + δ) * U))) := by
        gcongr
      _ = _ := by ring
  | matrixUnit i k =>
    refine ⟨1, by norm_num, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    simpa only [onSobolev, one_mul] using
      (norm_matrixUnitSobolev_le t i k u).trans (by simpa only [inclusion_self] using hu t le_rfl)
  | bessel =>
    refine ⟨1, by norm_num, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    simpa only [onSobolev, one_mul] using
      (norm_besselSobolev_apply_le t u).trans (by simpa only [inclusion_self] using hu t le_rfl)
  | derivativeBessel i =>
    refine ⟨1, by norm_num, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    simpa only [onSobolev, one_mul] using
      (norm_derivativeBesselSobolev_apply_le t i u).trans (by simpa only [inclusion_self] using hu t le_rfl)
  | add e f ihe ihf =>
    obtain ⟨C, hC, hCe⟩ := ihe he.1
    obtain ⟨D, hD, hDf⟩ := ihf he.2
    refine ⟨C + D, by positivity, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    calc
      _ ≤ ‖e.onSobolev q hq t u‖ + ‖f.onSobolev q hq t u‖ := norm_add_le _ _
      _ ≤ C * _ + D * _ := add_le_add (hCe q hq T hT hcoeff t ht δ U hU u hu)
        (hDf q hq T hT hcoeff t ht δ U hU u hu)
      _ = _ := by ring
  | neg e ihe =>
    obtain ⟨C, hC, hCe⟩ := ihe he
    refine ⟨C, hC, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    simpa only [onSobolev, neg_apply, norm_neg] using
      hCe q hq T hT hcoeff t ht δ U hU u hu
  | comp e f ihe ihf =>
    obtain ⟨C, hC, hCe⟩ := ihe he.1
    obtain ⟨D, hD, hDf⟩ := ihf he.2
    refine ⟨C * D, by positivity, ?_⟩
    intro q hq T hT hcoeff t ht δ U hU u hu
    have hf : ∀ r (hr : r ≤ t), ‖inclusion hr (f.onSobolev q hq t u)‖ ≤
        T ^ ((r : ℝ) / s + δ) * (D * U) := by
      intro r hr
      rw [inclusion_onSobolev]
      have hu' : ∀ k (hk : k ≤ r), ‖inclusion hk (inclusion hr u)‖ ≤
          T ^ ((k : ℝ) / s + δ) * U := by
        intro k hk
        have hi : inclusion hk (inclusion hr u) = inclusion (hk.trans hr) u := by
          apply toL2_injective k
          simp only [multiplier_toL2_inclusion]
        rw [hi]
        exact hu _ _
      convert hDf q hq T hT hcoeff r (hr.trans ht) δ U hU (inclusion hr u) hu' using 1
      ring
    simpa only [onSobolev, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm D] using
      hCe q hq T hT hcoeff t ht δ (D * U) (mul_nonneg hD hU) (f.onSobolev q hq t u) hf

/-- One coefficient derivative increases the retained jet order by one
(`app:ch_background:eq:bg-commutator`). -/
theorem jetOrderLe_coefficientDerivative (e : ImageFactorExpression n ι)
    {d : ℕ} (he : e.jetOrderLe d) (i : Fin n) :
    (e.coefficientDerivative i).jetOrderLe (d + 1) := by
  induction e with
  | coefficient a js => exact Nat.succ_le_succ he
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩
  | neg e ihe => exact ihe he
  | comp e f ihe ihf =>
    have mono : ∀ e : ImageFactorExpression n ι, e.jetOrderLe d → e.jetOrderLe (d+1) := by
      intro e h
      induction e with
      | coefficient a js => exact h.trans (Nat.le_succ d)
      | add e f he hf | comp e f he hf => exact ⟨he h.1, hf h.2⟩
      | neg e he => exact he h
      | _ => trivial
    exact ⟨⟨ihe he.1, mono f he.2⟩, ⟨mono e he.1, ihf he.2⟩⟩
  | _ => trivial

private theorem ordered_profile {s : ℕ} {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H)
    (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (hp : ∀ p ≤ s + 1, cNorm (fundamentalCell n) p (periodicLift q) ≤
      K * (1 + H) ^ (((p-1 : ℕ) : ℝ) / s))
    (js : List (Fin n)) (hjs : js.length ≤ 1) (j : ℕ) (hj : j ≤ s) :
    cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient q hq js)) ≤
      ((s + 1) * K) * (1 + H) ^ ((j : ℝ) / s) := by
  calc
    _ ≤ (j+1) * cNorm (fundamentalCell n) (j+js.length) (periodicLift q) :=
      cNorm_periodicCoordinateDerivList_le q hq js j
    _ ≤ (s+1) * (K * (1 + H) ^ ((j : ℝ) / s)) := by
      apply mul_le_mul
      · exact_mod_cast Nat.add_le_add_right hj 1
      · apply (hp _ (by omega)).trans
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
        exact_mod_cast (show j + js.length - 1 ≤ j by omega)
      · exact cNorm_nonneg _ _ _
      · positivity
    _ = _ := by ring

private theorem norm_ordered_ofSmooth_le (t : ℕ) (js : List (Fin n))
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    ‖ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js)‖ ≤
      ‖ofSmooth (t + js.length) f hf‖ := by
  induction js generalizing t with
  | nil => simp [periodicCoordinateDerivList]
  | cons i js ih =>
    apply (norm_ofSmooth_coordinateDeriv_le t i _ (hf.coordinateDerivList js)).trans
    have hindex : t + (i :: js).length = (t+1) + js.length := by simp; omega
    rw [hindex]
    exact ih (t+1)

private theorem norm_ofSmooth_le_power {s r : ℕ} (hr : r ≤ s)
    {T : ℝ} (hT : 0 < T) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    ‖ofSmooth r f hf‖ ≤ T ^ ((r : ℝ) / s - 1) *
      (‖ofSmooth s f hf‖ + T * ‖toL2 s (ofSmooth s f hf)‖) := by
  have h := periodic_gradeNorm_weighted_interpolate hr hT.le (ofSmooth s f hf)
  rw [← multiplier_norm_inclusion_eq_gradeNorm hr, multiplier_inclusion_ofSmooth] at h
  have hp : T ^ ((r : ℝ) / s - 1) * T ^ (1 - (r : ℝ) / s) = 1 := by
    rw [← Real.rpow_add hT]
    simp
  calc
    _ = T ^ ((r : ℝ) / s - 1) * (T ^ (1 - (r : ℝ) / s) * ‖ofSmooth r f hf‖) := by
      rw [← mul_assoc, hp, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hT.le _)

/-- Primitive first and high jet budgets bound every actual commutator branch
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_primitive_branch_bound (e : ImageFactorExpression n ι)
    (he : e.jetOrderLe 0) (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))
      (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ M) →
      (∀ a j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ H) →
      ∀ (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f)
        (t : ℕ) (js : List (Fin n)), t + js.length ≤ s → ∀ i : Fin n,
      ‖(e.coefficientDerivative i).onSobolev q hq t
        (ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js))‖ ≤
          C * (‖ofSmooth s f hf‖ + (1 + H) * ‖toL2 s (ofSmooth s f hf)‖) := by
  obtain ⟨K, hK, hprofile⟩ := exists_coefficient_jet_profile n s hM
  have hb (i : Fin n) := (e.coefficientDerivative i).exists_weighted_action_bound
    (e.jetOrderLe_coefficientDerivative he i) s (show 0 ≤ (s+1) * K by positivity)
  choose C hC hbound using hb
  have hsumC : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ hC i
  refine ⟨1 + ∑ i, C i, by positivity, ?_⟩
  intro q hq H hH hlow hhigh f hf t js hcount i
  let R := ‖ofSmooth s f hf‖ + (1+H) * ‖toL2 s (ofSmooth s f hf)‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcoeff : ∀ a ks, ks.length ≤ 1 → ∀ j ≤ s,
      cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient (q a) (hq a) ks)) ≤
        ((s+1) * K) * (1+H) ^ ((j : ℝ) / s) := by
    intro a ks hks j hj
    exact ordered_profile hK.le hH (q a) (hq a)
      (hprofile (q a) (hq a) H hH (hlow a) (hhigh a)) ks hks j hj
  have hu : ∀ r (hr : r ≤ t),
      ‖inclusion hr (ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js))‖ ≤
        (1+H) ^ ((r : ℝ) / s + ((js.length : ℝ) / s - 1)) * R := by
    intro r hr
    rw [multiplier_inclusion_ofSmooth]
    apply (norm_ordered_ofSmooth_le r js f hf).trans
    convert norm_ofSmooth_le_power (show r + js.length ≤ s by omega)
      (show 0 < 1+H by positivity) f hf using 1
    congr 2
    push_cast
    ring
  have hout := hbound i q hq (1+H) (by linarith) hcoeff t (by omega)
    ((js.length : ℝ) / s - 1) R hR _ hu
  have hexp : (t : ℝ) / s + ((js.length : ℝ) / s - 1) ≤ 0 := by
    by_cases hs : s = 0
    · simp [hs]
    have hspos : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hc : (t : ℝ) + js.length ≤ s := by exact_mod_cast hcount
    have hd := (div_le_one hspos).mpr hc
    rw [add_div] at hd
    linarith
  have hp : (1+H) ^ ((t : ℝ) / s + ((js.length : ℝ) / s - 1)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1+H by linarith) hexp
  have hCi : C i ≤ 1 + ∑ j, C j :=
    (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i)).trans (by linarith)
  have hscale : (1+H) ^ ((t : ℝ) / s + ((js.length : ℝ) / s - 1)) * R ≤ R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hR
  exact hout.trans (mul_le_mul hCi hscale (by positivity) (by positivity))


/-- Primitive jet budgets imply the single-high estimate for the constructed
commutator (`app:ch_background:eq:bg-commutator`). -/
theorem exists_primitive_commutator_bound (e : ImageFactorExpression n ι)
    (he : e.jetOrderLe 0) (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))
      (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ M) →
      (∀ a j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ H) →
      ∀ (is : List (Fin n)) (hlen : is.length ≤ s+1)
        (u : PeriodicSobolevSpace n (Euclidean n) s),
      ‖e.commutator q hq s is hlen u‖ ≤ C * (‖u‖ + (1+H) * ‖toL2 s u‖) := by
  obtain ⟨C, hC, hbranch⟩ := e.exists_primitive_branch_bound he s hM
  refine ⟨(s+1)*C, by positivity, ?_⟩
  intro q hq H hH hlow hhigh is hlen u
  exact e.norm_commutator_le_of_smooth_branch_bound q hq s hC.le hH
    (hbranch q hq H hH hlow hhigh) is hlen u

end ImageFactorExpression
end JanetCartan.ContinuumCommutator.ImageChannel.Differential
