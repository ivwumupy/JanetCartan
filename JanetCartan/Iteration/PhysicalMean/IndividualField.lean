module

public import JanetCartan.Iteration.PhysicalForwardMean.VectorJets
public import JanetCartan.Iteration.PhysicalMean.ScalarInput
public import JanetCartan.Iteration.PhysicalMean.InverseMomentProfile

/-!
# The same individual full forward field on its actual real adjoint

The literal full matrix Bochner field is applied to the SAME original
scalar-input real adjoint. The bare tester is used twice, with the exact
half-moment matching `k + 1/2 = (k+1) - 1/2`. The resulting physical jet
budget has source order exactly `s+1`, with no Sobolev-embedding loss
(`app:ch_mean_pairs:eq:block-fields`, `app:ch_mean_pairs:eq:mean-quadratic-low`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean PeriodicLocalL2 Pseudodifferential AmplitudeBound.PaperEstimates
open PhysicalForwardMean PhysicalSamplingShells RawInputPartition

private theorem halfMoment_convolution_le
    {T : ℝ} (hT : 1 ≤ T) (s r₀ : ℕ) (M W : ℕ → ℝ)
    (hM : ∀ k, 0 ≤ M k) (hW : ∀ k, 0 ≤ W k) :
    (∑ k ∈ Finset.range (s+1), T^(s-k-r₀) *
      (M (k+1) * ∑ i ∈ Finset.range (k+1+1), T^(k+1-i-r₀) * W i)) ≤
    (∑ k ∈ Finset.range (s+1), M (k+1)) *
      ∑ i ∈ Finset.range (s+1+1), T^(s+1-i-r₀) * W i := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mul_left_comm, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hM (k+1))
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1+1), T^(s+1-i-r₀) * W i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k+1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : (s-k-r₀) + (k+1-i-r₀) ≤ s+1-i-r₀ := by omega
      calc
        _ = T^((s-k-r₀)+(k+1-i-r₀)) * W i := by rw [pow_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT he) (hW i)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (hW i))

/-- The literal full individual matrix field on the SAME original real
adjoint has an `H^s` physical jet budget at source order exactly `s+1`.
The fixed constant precedes the band count, history-dependent phase and
full amplitudes, original operator, tester and source. The native operator
is identified by its exact forward entry kernels, not by an operator-norm
premise. In the mean application the regular source is the SAME CURRENT
UNCUT inverse applied to the Picard datum; no inverse is reselected here. -/
theorem exists_individualNativeField_jet_constant
    (n N s : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ J : ℕ,
    let X := RefinedIndex J × Euclidean (n-1)
    let μ := annularShellMeasure (n := n) (refinedRadius (J := J))
    ∀ (φ : X → Euclidean n → ℝ)
      (Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ)
      (G : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
      (a : Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
      (L : RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
      (m : X → ℝ),
      Continuous (Function.uncurry φ) →
      (∀ u, ContDiff ℝ ∞ (φ u)) →
      (∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i))) →
      (∀ a b i, ContDiff ℝ ∞ (Function.uncurry (G a b i))) →
      (∀ i j, ContDiff ℝ ∞ (Function.uncurry (a i j))) →
      (∀ i h, ContDiff ℝ ∞ (fun q : Euclidean (n-1) × Euclidean n ↦ L i q.1 h q.2)) →
      Continuous m → HasCompactSupport m → (∀ u, ‖u.2‖ ≤ 1 → m u = 0) →
    ∀ {K : Set (Euclidean n)}, IsCompact K →
      (∀ a b i η, tsupport (G a b i η) ⊆ K) →
      (∀ i j η, tsupport (a i j η) ⊆ K) →
      (∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x) →
      (∀ u, m u ≠ 0 → ∀ h x, x ∈ K → inner ℝ h u.2 = fderiv ℝ (φ u) x (L u.1 u.2 h x)) →
      (∀ x ∈ K, χ x = 1) → (∀ x ∈ K, ∀ i, |x i| ≤ Rbox) →
    ∀ {s₀ : ℕ} {T : ℝ}, 1 ≤ T →
      (∀ a0 b0 i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
        ‖iteratedFDeriv ℝ j (G a0 b0 i η) x‖ ≤ aG j*T^(j-(s₀+(n/2+1)))) →
      (∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y/‖η‖) x‖ ≤ p j*T^(j-1-(s₀+(n/2+1)))) →
      (∀ i j η, m (j,η) ≠ 0 → ∀ x ∈ K, ∀ r,
        ‖iteratedFDeriv ℝ r (a i j η) x‖ ≤ Badj r*T^(r-(s₀+(n/2+1)))) →
      (∀ j η, m (j,η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ r,
        ‖iteratedFDeriv ℝ r (L j η h) x‖ ≤ Badj r*T^(r-(s₀+(n/2+1)))) →
    ∀ Tbare : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)),
      (∀ f : Lp ℂ 2 μ, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
        sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u*f u ∂μ) →
    ∀ A : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)),
      (∀ f i, finiteL2CoordinateIsometry volume (A f) i =ᵐ[volume] fun x ↦ ∫ u,
        sampledMomentKernel φ (halfWeightedMomentMask m) (fun u y ↦ a i u.1 u.2 y) x u*f u ∂μ) →
    ∀ w : ContinuumRow.OutputL2 n, (∀ j, w ∈ periodicSobolevLevel n (Euclidean n) j) →
    let v := (transferOutputOperator (realQuadratureChannel A)).adjoint w
    let B : Euclidean n → Matrix (Fin N) (Fin n) ℂ := fun x ↦ ∫ u,
      ((fun a0 b0 ↦ physicalForwardKernel φ (fun u ↦ m u*Real.sqrt ‖u.2‖)
        (fun u ↦ G a0 b0 u.1 u.2) x u*v u) : Matrix (Fin N) (Fin n) ℂ) ∂μ
    ContDiff ℝ ∞ B ∧ tsupport B ⊆ K ∧
      (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j B) 2 volume) ∧
      ∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j B) 2 volume ≤
        D * ‖Tbare‖^2 * ∑ i ∈ Finset.range (s+1+1), T^(s+1-i-s₀)*periodicSobolevNorm i w := by
  classical
  obtain ⟨Cf, hCf, hforward⟩ := exists_singleForward_matrix_halfMoment_constant n N s Rbox aG p haG hp
  let M := fun q ↦ nativeRealMomentConstant χ hχ hχs hχcell Rbox Badj q
  have hM (q : ℕ) : 0 ≤ M q := by
    exact mul_nonneg (mul_nonneg (by norm_num)
      (sampledRadialMomentConstant_nonneg n Rbox Badj hBadj q))
      (sourceMomentConstant_nonneg χ hχ hχs hχcell q)
  refine ⟨Cf * ∑ k ∈ Finset.range (s+1), M (k+1),
    mul_nonneg hCf (Finset.sum_nonneg fun k _ ↦ hM (k+1)), ?_⟩
  intro J X μ φ Φ G a L m hφ hφs hΦ hG ha hL hm hms hhigh K hK hGK haK hagree hphase hχK hbox
    s₀ T hT hGj hΦj haj hLj Tbare hTbare A hA w hw v B
  let t : TopologicalSpace (RefinedIndex J) := inferInstance
  let f : RefinedIndex J → ℝ := fun i ↦ ((Fintype.equivFin (RefinedIndex J) i).val : ℝ)
  have hf : Function.Injective f := by
    intro i j hij
    apply (Fintype.equivFin (RefinedIndex J)).injective
    apply Fin.ext
    change ((Fintype.equivFin (RefinedIndex J) i).val : ℝ) =
      ((Fintype.equivFin (RefinedIndex J) j).val : ℝ) at hij
    exact_mod_cast hij
  let mt : MetricSpace (RefinedIndex J) := MetricSpace.induced f hf inferInstance
  have hmt : t = mt.toUniformSpace.toTopologicalSpace := by
    have ht : t = ⊥ := DiscreteTopology.eq_bot
    have hm : mt.toUniformSpace.toTopologicalSpace = ⊥ := by
      let : MetricSpace (RefinedIndex J) := mt
      exact DiscreteTopology.eq_bot
    exact ht.trans hm.symm
  let : MetricSpace (RefinedIndex J) := mt.replaceTopology hmt
  let am : Fin n → Unit → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ := fun i _ ↦ a i
  let entries := sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) am hφ
    (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms)
    (fun i _ j ↦ ha i j) hK (fun i _ j η ↦ haK i j η)
  have hentries (f : Lp ℂ 2 μ) (i : Fin n) :
      finiteL2CoordinateIsometry volume (A f) i = entries i () f := by
    apply Lp.ext
    apply (hA f i).trans
    exact (sampledMomentOperator_ae_kernel μ φ (halfWeightedMomentMask m)
      (fun u ↦ a i u.1 u.2) hφ (continuous_halfWeightedMomentMask m hm)
      (continuous_originalSampledAmplitude (a i) (ha i))
      (hasCompactSupport_halfWeightedMomentMask m hms) hK (fun u ↦ haK i u.1 u.2) f).symm
  have he := nativeRealScalarRow_adjoint_eq_matrixCoordinate μ (fun i ↦ entries i ()) A hentries w
  have hmoment (k : ℕ) :
      (eLpNorm (fun u : X ↦ ((‖u.2‖^((k : ℝ)+1/2) : ℝ) : ℂ)*v u) 2 μ).toReal ≤
        M (k+1) * ‖Tbare‖ * ∑ i ∈ Finset.range (k+1+1), T^(k+1-i-s₀)*periodicSobolevNorm i w := by
    have hh := nativeRealIndividualAdjoint_moment_L2_bound μ φ m am L hφ hm hms hhigh
      (fun i _ j ↦ ha i j) hL hK (fun i _ j η ↦ haK i j η)
      χ hχ hχs hχcell hχK Rbox hbox Tbare hTbare hφs hphase Badj hBadj (k+1) s₀ hT
      (fun i _ j η ↦ haj i j η) hLj w hw ()
    have hk : ((k+1 : ℕ) : ℝ)-1/2 = (k : ℝ)+1/2 := by push_cast; ring
    dsimp only at hh
    rw [hk] at hh
    rw [show v = (transferOutputOperator (realQuadratureChannel A)).adjoint w from rfl, he]
    simpa only [entries, am, M, toReal_eLpNorm] using hh.2
  have hhigh' (u : X) (hu : m u ≠ 0) : 1 ≤ ‖u.2‖ := by
    by_contra hh
    exact hu (hhigh u (le_of_lt (lt_of_not_ge hh)))
  have hb := hforward J φ Φ G m hφ hΦ hG hm hms hhigh' hK hGK hagree
    χ hχ.continuous hχs hχK hbox hT hGj hΦj Tbare hTbare v
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.trans ?_⟩
  have hc := halfMoment_convolution_le hT s s₀ (fun q ↦ M q * ‖Tbare‖)
    (fun i ↦ periodicSobolevNorm i w) (fun q ↦ mul_nonneg (hM q) (norm_nonneg _))
    (fun _ ↦ Real.sqrt_nonneg _)
  have hsum : (∑ k ∈ Finset.range (s+1), T^(s-k-s₀) *
      (eLpNorm (fun u : X ↦ ((‖u.2‖^((k : ℝ)+1/2) : ℝ) : ℂ)*v u) 2 μ).toReal) ≤
      (∑ k ∈ Finset.range (s+1), M (k+1)*‖Tbare‖) *
        ∑ i ∈ Finset.range (s+1+1), T^(s+1-i-s₀)*periodicSobolevNorm i w := by
    apply le_trans _ hc
    exact Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hmoment k)
      (pow_nonneg (zero_le_one.trans hT) _)
  calc
    _ ≤ Cf*‖Tbare‖ * ((∑ k ∈ Finset.range (s+1), M (k+1)*‖Tbare‖) *
        ∑ i ∈ Finset.range (s+1+1), T^(s+1-i-s₀)*periodicSobolevNorm i w) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hCf (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end JanetCartan.PhysicalMean
