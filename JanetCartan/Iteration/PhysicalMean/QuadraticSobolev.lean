module

public import JanetCartan.Iteration.PhysicalMean.QuadraticProfiles
public import JanetCartan.Iteration.PhysicalMean.GroupedCross

/-!
# Same-order Sobolev profile of the actual full quadratic source

The exact balanced derivative assembly is summed with fixed derivative-only
constants, then transferred to the SAME centered periodization without any
embedding or derivative-order loss (`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal

namespace JanetCartan.PhysicalMean
open BallExtension PhysicalForwardMean RawPrimary.SliceBounds PhysicalSamplingShells RawInputRealization LocalSobolev

/-- A fixed derivative-order majorant for every full balanced word constant.
The finite sums depend only on orders, never on original label cardinalities. -/
def quadraticOrderProfileConstant (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (s+1), ∑ t ∈ Finset.range (s+1), ∑ r ∈ Finset.range (s+1),
    quadraticWordProfileConstant n N Rbox aC aG p MB MW c t r

/-- The fixed coordinate profile counts exactly the three-way Leibniz choices. -/
def quadraticCoordinateProfileConstant (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ) (s : ℕ) : ℝ :=
  3^s*quadraticOrderProfileConstant n N Rbox aC aG p MB MW s

/-- The SAME-order Sobolev profile adds only the fixed physical coordinate
norm-equivalence constant. All these constants are independent of the sample,
current, source, input measure, carrier ceiling and Picard iteration depth. -/
def quadraticSobolevProfileConstant (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ) (s : ℕ) : ℝ :=
  (Real.sqrt (s.factorial : ℝ)*((sobolevMultiindices n s).card : ℝ))*
    quadraticCoordinateProfileConstant n N Rbox aC aG p MB MW s

/-- Nonnegativity of the fixed order-only majorant. -/
theorem quadraticOrderProfileConstant_nonneg (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ)
    (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hMB : ∀ j, 0 ≤ MB j) (hMW : ∀ j, 0 ≤ MW j) (s : ℕ) :
    0 ≤ quadraticOrderProfileConstant n N Rbox aC aG p MB MW s := by
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro t _
  apply Finset.sum_nonneg
  intro r _
  exact quadraticWordProfileConstant_nonneg n N Rbox aC aG p MB MW haC haG hp hMB hMW c t r

/-- Every actual word constant is bounded by the prechosen order majorant. -/
theorem quadraticWordProfileConstant_le_order (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ)
    (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hMB : ∀ j, 0 ≤ MB j) (hMW : ∀ j, 0 ≤ MW j) {c t r s : ℕ}
    (hc : c ≤ s) (ht : t ≤ s) (hr : r ≤ s) :
    quadraticWordProfileConstant n N Rbox aC aG p MB MW c t r ≤
      quadraticOrderProfileConstant n N Rbox aC aG p MB MW s := by
  have hn := quadraticWordProfileConstant_nonneg n N Rbox aC aG p MB MW haC haG hp hMB hMW
  calc
    _ ≤ ∑ r' ∈ Finset.range (s+1), quadraticWordProfileConstant n N Rbox aC aG p MB MW c t r' :=
      Finset.single_le_sum (fun r' _ ↦ hn c t r') (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ t' ∈ Finset.range (s+1), ∑ r' ∈ Finset.range (s+1),
        quadraticWordProfileConstant n N Rbox aC aG p MB MW c t' r' :=
      Finset.single_le_sum (fun t' _ ↦ Finset.sum_nonneg (fun r' _ ↦ hn c t' r')) (Finset.mem_range.mpr (by omega))
    _ ≤ _ := Finset.single_le_sum
      (fun c' _ ↦ Finset.sum_nonneg (fun t' _ ↦ Finset.sum_nonneg (fun r' _ ↦ hn c' t' r')))
      (Finset.mem_range.mpr (by omega))

/-- Exact number of derivative choices, with NO original sample count. -/
theorem crossDerivativeBranches_length {n : ℕ} (ds : List (Fin n)) :
    (crossDerivativeBranches ds).length = 3^ds.length := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    simp [crossDerivativeBranches, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

private theorem memLp_list_sum_profile {n : ℕ} {κ : Type*} (l : List κ)
    (F : κ → Euclidean n → Euclidean n) {M : ℝ}
    (hF : ∀ q ∈ l, MemLp (F q) 2 volume ∧ lpNorm (F q) 2 volume ≤ M) :
    MemLp (fun x ↦ (l.map (fun q ↦ F q x)).sum) 2 volume ∧
      lpNorm (fun x ↦ (l.map (fun q ↦ F q x)).sum) 2 volume ≤ (l.length : ℝ)*M := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq := hF q (List.mem_cons_self)
    have hl := ih (fun p hp ↦ hF p (List.mem_cons_of_mem q hp))
    constructor
    · convert hq.1.add hl.1 using 1
      funext x
      simp only [List.map_cons, List.sum_cons]
      rfl
    · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact ((lpNorm_add_le hq.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hq.2 hl.2)).trans_eq (by ring)

/-- The actual full weighted quadratic source obeys the sharp same-order
Sobolev estimate. Smoothness/support and all derivative identities are proved
from the full primitive kernel. The ONLY quantitative source inputs are the
actual individual lower-field jets and aggregate adjoint moments produced by
IndividualSource/AggregateSource; no quadratic norm conclusion is assumed. -/
theorem groupedAnnularWeightedQuadratic_sobolev_profile {n N : ℕ} {ν β : Type*}
    [Fintype ν] [Fintype β]
    [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β]
    (radius : ν × β → ℝ) (weight : ν → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (φ θ : ((ν × β) × Euclidean (n-1)) → Euclidean n → ℝ) (m : ((ν × β) × Euclidean (n-1)) → ℝ)
    (A : Fin N → Fin n → ((ν × β) × Euclidean (n-1)) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hAc : ∀ a c, Continuous (fun z : ((ν × β) × Euclidean (n-1)) × Euclidean n ↦ A a c z.1 z.2))
    (hθ : ∀ z, ContDiff ℝ ∞ (θ z)) (hA : ∀ a c z, ContDiff ℝ ∞ (A a c z))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c z, tsupport (A a c z) ⊆ K)
    (hphase : ∀ z, m z ≠ 0 → ∀ x ∈ K, φ z x = ‖z.2‖*θ z x)
    (hjets : ∀ a c i j, Continuous (fun z : Euclidean n × Euclidean (n-1) ↦
      iteratedFDeriv ℝ j
        (fun y ↦ physicalForwardKernel (fun η ↦ φ (i,η)) (fun η ↦ m (i,η))
          (fun η y ↦ A a c (i,η) y) y z.2) z.1))
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : ContDiff ℝ ∞ C)
    (f g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (s m₀ : ℕ)
    (hbc : ∀ ds : List (Fin n), ∀ a c (b : SliceDerivativeBranch ds.length),
      Continuous (fun z : ((ν × β) × Euclidean (n-1)) × Euclidean n ↦
        sliceDerivativeAmplitude (θ z.1) (A a c z.1)
          (fun j ↦ EuclideanSpace.single (ds.get j) 1) b z.2))
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hRbox : Rbox < 1/2)
    (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (aC aG p MB MW : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j)
    (hp : ∀ j, 0 ≤ p j) (hMB : ∀ j, 0 ≤ MB j) (hMW : ∀ j, 0 ≤ MW j)
    {T R h : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hh : 0 ≤ h)
    (hCj : ∀ x ∈ K, ∀ j ≤ n/2+1+s,
      ‖iteratedFDeriv ℝ j C x‖ ≤ aC j*T^(j-(2*m₀+(n/2+1))))
    (hAj : ∀ a c z, m z ≠ 0 → ∀ x ∈ K, ∀ j ≤ s+(n/2+1),
      ‖iteratedFDeriv ℝ j (A a c z) x‖ ≤ aG j*T^(j-(2*m₀+(n/2+1))))
    (hθj : ∀ z, m z ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ s+(n/2+1) →
      ‖iteratedFDeriv ℝ j (θ z) x‖ ≤ p j*T^(j-1-(2*m₀+(n/2+1))))
    (hBf : ∀ t ≤ s, ∀ i, (∑ j ∈ Finset.range (n/2+1+t+1),
      lpNorm (iteratedFDeriv ℝ j (groupedAnnularForwardField radius φ m A f i)) 2 volume) ≤ MB t*h*R^(t-m₀))
    (hBg : ∀ t ≤ s, ∀ i, (∑ j ∈ Finset.range (n/2+1+t+1),
      lpNorm (iteratedFDeriv ℝ j (groupedAnnularForwardField radius φ m A g i)) 2 volume) ≤ MB t*h*R^(t-m₀))
    (hrawf : ∀ k ≤ s, lpNorm (fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius (fun i ↦ weight i.1) f z) 2
      (annularShellMeasure radius) ≤ MW k*h*R^(k-2*m₀))
    (hrawg : ∀ k ≤ s, lpNorm (fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius (fun i ↦ weight i.1) g z) 2
      (annularShellMeasure radius) ≤ MW k*h*R^(k-2*m₀))
    (Tfull : Lp ℂ 2 (annularShellMeasure radius) →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ w : Lp ℂ 2 (annularShellMeasure radius), Tfull w =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ (fun z ↦ Real.sqrt (weight z.1.1)*m z) (fun _ x ↦ (χ x : ℂ)) x z*w z
        ∂annularShellMeasure radius) :
    let Q := groupedAnnularWeightedQuadratic radius φ m A weight C f g
    IsSmoothPeriodic (UniformStep.Periodization.vectorPeriodization Q) ∧
      (∀ ds : List (Fin n), ds.length ≤ s → MemLp (cartesianCoordinateDerivList ds Q) 2 volume ∧
        lpNorm (cartesianCoordinateDerivList ds Q) 2 volume ≤
          quadraticCoordinateProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*R^(s-2*m₀)) ∧
      periodicSobolevNorm s (UniformStep.Periodization.vectorPeriodization Q) ≤
        quadraticSobolevProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*R^(s-2*m₀) := by
  intro Q
  have hins (i : ν × β) : Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ ((i,z.1),z.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  have hφi (i : ν × β) : Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ φ (i,z.1) z.2) :=
    hφ.comp (hins i)
  have hmi (i : ν × β) : Continuous (fun η ↦ m (i,η)) := hm.comp (continuous_const.prodMk continuous_id)
  have hmsi (i : ν × β) : HasCompactSupport (fun η ↦ m (i,η)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hms.image continuous_snd)
    intro η hη
    exact ⟨(i,η), subset_tsupport _ hη, rfl⟩
  have hAci (a : Fin N) (c : Fin n) (i : ν × β) :
      Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ A a c (i,z.1) z.2) := (hAc a c).comp (hins i)
  have hshellfields (v : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ν × β) :=
    annularForwardField_smooth_supported radius φ θ m A hφi hmi hmsi hAci hθ hA hK hAK hphase hjets v i
  have hfields (v : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ν) :=
    groupedAnnularForwardField_smooth_supported radius φ m A v hK.isClosed (hshellfields v) i
  have horder := quadraticOrderProfileConstant_nonneg n N Rbox aC aG p MB MW haC haG hp hMB hMW s
  have hR0 := zero_le_one.trans hR
  have hw (v w : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
      (hBv : ∀ t ≤ s, ∀ i, (∑ j ∈ Finset.range (n/2+1+t+1),
        lpNorm (iteratedFDeriv ℝ j (groupedAnnularForwardField radius φ m A v i)) 2 volume) ≤ MB t*h*R^(t-m₀))
      (hWw : ∀ k ≤ s, lpNorm (fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius (fun i ↦ weight i.1) w z) 2
        (annularShellMeasure radius) ≤ MW k*h*R^(k-2*m₀))
      (dc dt dr : List (Fin n)) (hc : dc.length ≤ s) (ht : dt.length ≤ s) (hr : dr.length ≤ s)
      (htr : dt.length ≤ dr.length) :
      MemLp (groupedAnnularCrossWordBranch radius φ θ m A weight C v w dc dt dr) 2 volume ∧
      lpNorm (groupedAnnularCrossWordBranch radius φ θ m A weight C v w dc dt dr) 2 volume ≤
        quadraticOrderProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*
          R^(dc.length+dr.length+dt.length-2*m₀) := by
    have hw0 := annularCrossWordBranch_L2_profile radius (fun i ↦ weight i.1) φ θ m A hφ hm hms hθ hA hK hAK C hC
      (fun i ↦ groupedAnnularForwardField radius φ m A v i.1) w
      (fun i ↦ hfields v i.1) dc dt dr htr (hbc dr) χ hχ hχs hχK Rbox hbox aC aG p MB MW haC haG hp hMB hMW
      hT hR hTR hh m₀ (fun x hx j hj ↦ hCj x hx j (by omega))
      (fun a c z hz x hx j hj ↦ hAj a c z hz x hx j (by omega))
      (fun z hz x hx j hj hj' ↦ hθj z hz x hx j hj (by omega))
      (fun i ↦ hBv dt.length ht i.1) (fun k hk ↦ hWw k (hk.trans hr)) Tfull hTfull
    refine ⟨hw0.1, hw0.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (quadraticWordProfileConstant_le_order n N Rbox aC aG p MB MW haC haG hp hMB hMW hc ht hr)
      (norm_nonneg Tfull)) (sq_nonneg h)) (pow_nonneg hR0 _)
  have hcoord (ds : List (Fin n)) (hds : ds.length ≤ s) :
      MemLp (cartesianCoordinateDerivList ds Q) 2 volume ∧
      lpNorm (cartesianCoordinateDerivList ds Q) 2 volume ≤
        quadraticCoordinateProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*R^(s-2*m₀) := by
    have hbranch (q : List (Fin n) × List (Fin n) × List (Fin n)) (hq : q ∈ crossDerivativeBranches ds) :
        MemLp (groupedAnnularBalancedBranch radius φ θ m A weight C f g q) 2 volume ∧
        lpNorm (groupedAnnularBalancedBranch radius φ θ m A weight C f g q) 2 volume ≤
          quadraticOrderProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*R^(ds.length-2*m₀) := by
      have hg := crossDerivativeBranches_grade ds q hq
      by_cases hrt : q.2.1.length ≤ q.2.2.length
      · have hwq := hw f g hBf hrawg q.1 q.2.1 q.2.2 (by omega) (by omega) (by omega) hrt
        have he : q.1.length+q.2.2.length+q.2.1.length = ds.length := by omega
        have heF : groupedAnnularBalancedBranch radius φ θ m A weight C f g q =
            groupedAnnularCrossWordBranch radius φ θ m A weight C f g q.1 q.2.1 q.2.2 := by
          funext x
          simp only [groupedAnnularBalancedBranch, hrt, ↓reduceIte]
        rw [heF]
        simpa only [he] using hwq
      · have hwq := hw g f hBg hrawf q.1 q.2.2 q.2.1 (by omega) (by omega) (by omega) (by omega)
        have heF : groupedAnnularBalancedBranch radius φ θ m A weight C f g q =
            groupedAnnularCrossWordBranch radius φ θ m A weight C g f q.1 q.2.2 q.2.1 := by
          funext x
          simp only [groupedAnnularBalancedBranch, hrt, ↓reduceIte]
        rw [heF]
        simpa only [hg] using hwq
    have he : cartesianCoordinateDerivList ds Q = fun x ↦
        ((crossDerivativeBranches ds).map (fun q ↦ groupedAnnularBalancedBranch radius φ θ m A weight C f g q x)).sum := by
      funext x
      exact groupedAnnularWeightedQuadratic_coordinate_eq_balancedBranches radius φ θ m A hφi hmi hmsi hAci hθ hA
        hK hAK hphase hjets weight hweight C hC f g
        (fun d a c i b ↦ (hbc d a c b).comp (hins i)) ds x
    rw [he]
    have hl := memLp_list_sum_profile (crossDerivativeBranches ds)
      (groupedAnnularBalancedBranch radius φ θ m A weight C f g) hbranch
    refine ⟨hl.1, hl.2.trans ?_⟩
    rw [crossDerivativeBranches_length, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (3 : ℝ)^s*(quadraticOrderProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*R^(s-2*m₀)) :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hds)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.sub_le_sub_right hds _)) (by positivity))
          (by positivity) (by positivity)
      _ = _ := by dsimp only [quadraticCoordinateProfileConstant]; ring
  have hQsm : ContDiff ℝ ∞ Q := by
    apply hC.clm_apply
    apply ContDiff.sum
    intro i _
    exact (((CurrentMean.hermitianContinuousBilinear (m := Fin N) (n := Fin n)).contDiff.comp
      (hfields f i).1).clm_apply (hfields g i).1).const_smul (weight i)
  have hQK : tsupport Q ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    have hz (i : ν) : groupedAnnularForwardField radius φ m A f i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht ↦ hxK ((hfields f i).2 ht))
    apply hx
    simp [Q, groupedAnnularWeightedQuadratic, hz]
  have hQbox : tsupport Q ⊆ {x | ∀ i, |x i| ≤ Rbox} := fun x hx ↦ hbox x (hQK hx)
  have hM : 0 ≤ quadraticCoordinateProfileConstant n N Rbox aC aG p MB MW s*‖Tfull‖*h^2*R^(s-2*m₀) := by
    dsimp only [quadraticCoordinateProfileConstant]
    positivity
  refine ⟨UniformStep.Periodization.isSmoothPeriodic_vectorPeriodization hRbox hQbox hQsm, hcoord, ?_⟩
  exact (periodicSobolevNorm_vectorPeriodization_le_coordinate_bound s hRbox hM Q hQsm hQbox hcoord).trans_eq
    (by dsimp only [quadraticSobolevProfileConstant]; ring)

end JanetCartan.PhysicalMean
