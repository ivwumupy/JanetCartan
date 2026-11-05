module

public import JanetCartan.Iteration.PhysicalMean.NativeSourceProfiles
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Pointwise
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Jets

/-!
# Physical high profiles of the complete original individual source field

Consumer: the full unmeasured Hermitian tensor profile in `main:prop:mean`.
Only this ROUGH physical high profile spends the fixed Sobolev loss `n+1`;
`2*m0` absorbs it. The sharp quadratic low estimate still uses H^ell, not
C^ell. Actual native source/adjoint estimates are applied, not assumed as field
profiles; all original shells remain inside the same complete individual field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open PhysicalForwardMean PhysicalSamplingShells RawInputPartition ContinuumRow PeriodicLocalL2 Pseudodifferential

private theorem matrixField_cNorm_le_L2Jets {n N : ℕ} (s : ℕ) (Kphys : Set (Euclidean n))
    (f : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (hf : ContDiff ℝ ∞ f)
    (hmem : ∀ j ≤ s+n+1, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    cNorm Kphys s f ≤ ((s+1 : ℝ)*(2 : ℝ)^n)*
      ∑ j ∈ Finset.range (s+n+1+1), lpNorm (iteratedFDeriv ℝ j f) 2 volume := by
  have hpoint (j : ℕ) (hj : j ≤ s) (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ (2 : ℝ)^n*
        ∑ k ∈ Finset.range (s+n+1+1), lpNorm (iteratedFDeriv ℝ k f) 2 volume := by
    have h := LocalSobolev.FiniteOrder.smooth_jet_estimate_of_scalar volume
      (r := n) (k := s+1) (C := (2 : ℝ)^n) (by positivity)
      (fun u hu hm x ↦ LocalSobolev.FiniteOrder.norm_le_sum_eLpNorm_iteratedFDeriv hu hm x)
      hf (fun k hk ↦ hmem k (by omega)) (j := j) (by omega) x
    simpa only [toReal_eLpNorm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hbound := cNorm_le_sum_of_bounds
    (fun j (_ : j ≤ s) ↦ mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
      (Finset.sum_nonneg fun _ _ ↦ lpNorm_nonneg))
    (fun j hj x (_ : x ∈ Kphys) ↦ hpoint j hj x)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc] using hbound

/-- The physical field constant is fixed before the original current, sample,
source and cutoff. Only dimension/order counts and the existing bare tester
squared enter it (`main:prop:mean`). -/
def nativeIndividualPhysicalProfileConstant (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (Cbare : ℝ) (s : ℕ) : ℝ :=
  ((s+1 : ℝ)*(2 : ℝ)^n)*nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell
    aG p Badj Cinv M haG hp hBadj Cbare (s+n+1-(n/2+1))

/-- The physical individual constant is nonnegative, before data choices. -/
theorem nativeIndividualPhysicalProfileConstant_nonneg (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (hM : ∀ j, 0 ≤ M j)
    (Cbare : ℝ) (s : ℕ) :
    0 ≤ nativeIndividualPhysicalProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare s :=
  mul_nonneg (by positivity)
    (nativeLowerSourceProfileConstant_nonneg n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj hCinv hM Cbare _)

/-- The ACTUAL full native individual field of the SAME measured adjoint and
current inverse has a physical `C_s*h*R^s` profile. Its complete bare-test source
bound is applied internally. The loss here is only a fixed high-profile loss;
it is never substituted into the sharp low quadratic argument. -/
theorem individualNativeInverseField_cNorm_source_profile
    (n N s : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (hM : ∀ j, 0 ≤ M j)
    (Cbare : ℝ) (J : ℕ)
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ)
    (G : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (a : Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (L : RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hφs : ∀ u, ContDiff ℝ ∞ (φ u))
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (hG : ∀ a b i, ContDiff ℝ ∞ (Function.uncurry (G a b i)))
    (ha : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (a i j)))
    (hL : ∀ i h, ContDiff ℝ ∞ (fun z : Euclidean (n-1) × Euclidean n ↦ L i z.1 h z.2))
    (hm : Continuous m) (hms : HasCompactSupport m) (hhigh : ∀ u, ‖u.2‖ ≤ 1 → m u = 0)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hGK : ∀ a b i η, tsupport (G a b i η) ⊆ K) (haK : ∀ i j η, tsupport (a i j η) ⊆ K)
    (hagree : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x)
    (hphase : ∀ u, m u ≠ 0 → ∀ h x, x ∈ K → inner ℝ h u.2 = fderiv ℝ (φ u) x (L u.1 u.2 h x))
    (hχK : ∀ x ∈ K, χ x = 1) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {T R h : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hh : 0 ≤ h)
    (hGj : ∀ a0 b0 i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (G a0 b0 i η) x‖ ≤ aG j*T^(j-(2*(n/2+2)+(n/2+1))))
    (hΦj : ∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y/‖η‖) x‖ ≤ p j*T^(j-1-(2*(n/2+2)+(n/2+1))))
    (haj : ∀ i j η, m (j,η) ≠ 0 → ∀ x ∈ K, ∀ r,
      ‖iteratedFDeriv ℝ r (a i j η) x‖ ≤ Badj r*T^(r-(2*(n/2+2)+(n/2+1))))
    (hLj : ∀ j η, m (j,η) ≠ 0 → ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ K, ∀ r,
      ‖iteratedFDeriv ℝ r (L j η v) x‖ ≤ Badj r*T^(r-(2*(n/2+2)+(n/2+1))))
    (Tbare : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTbare : ∀ f, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u*f u
        ∂(annularShellMeasure (n := n) (refinedRadius (J := J))))
    (hTbareBound : ‖Tbare‖ ≤ Cbare)
    (A : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hA : ∀ f i, finiteL2CoordinateIsometry volume (A f) i =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ (halfWeightedMomentMask m) (fun u y ↦ a i u.1 u.2 y) x u*f u
        ∂(annularShellMeasure (n := n) (refinedRadius (J := J))))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    (hreg : ∀ j, Q₀ e ∈ periodicSobolevLevel n (Euclidean n) j)
    (hinverse : ∀ j, j ≤ s+n+1+1 → periodicSobolevNorm j (Q₀ e) ≤
      Cinv j*(periodicSobolevNorm j e+T^(j-2*(n/2+2))*‖e‖))
    (hsource : ∀ j ≤ s+n+1+1, periodicSobolevNorm j e ≤ M j*h*R^(j-2*(n/2+2))) :
    let D := individualNativeInverseField φ m G A Q₀ e
    ContDiff ℝ ∞ D ∧ tsupport D ⊆ K ∧
      ∀ Kphys : Set (Euclidean n), cNorm Kphys s D ≤ nativeIndividualPhysicalProfileConstant n N Rbox χ hχ hχs hχcell
        aG p Badj Cinv M haG hp hBadj Cbare s*h*R^s := by
  intro D
  let t := s+n+1-(n/2+1)
  have ht : n/2+1+t = s+n+1 := by dsimp only [t]; omega
  have hb := individualNativeInverseField_source_profile n N t Rbox χ hχ hχs hχcell
    aG p Badj Cinv M haG hp hBadj hCinv hM Cbare J φ Φ G a L m hφ hφs hΦ hG ha hL hm hms hhigh
    hK hGK haK hagree hphase hχK hbox hT hR hTR hh hGj hΦj haj hLj Tbare hTbare hTbareBound A hA Q₀ e hreg
    (fun j hj ↦ hinverse j (by omega)) (fun j hj ↦ hsource j (by omega))
  rw [ht] at hb
  have hB := nativeLowerSourceProfileConstant_nonneg n N Rbox χ hχ hχs hχcell
    aG p Badj Cinv M haG hp hBadj hCinv hM Cbare t
  have hg : t-(n/2+2) ≤ s := by dsimp only [t]; omega
  refine ⟨hb.1, hb.2.1, fun Kphys ↦ ?_⟩
  apply (matrixField_cNorm_le_L2Jets s Kphys D hb.1 hb.2.2.1).trans
  calc
    _ ≤ ((s+1 : ℝ)*(2 : ℝ)^n)*
        (nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare t*h*R^(t-(n/2+2))) :=
      mul_le_mul_of_nonneg_left hb.2.2.2 (by positivity)
    _ ≤ ((s+1 : ℝ)*(2 : ℝ)^n)*
        (nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare t*h*R^s) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hg) (mul_nonneg hB hh)) (by positivity)
    _ = _ := by dsimp only [nativeIndividualPhysicalProfileConstant, t]; ring

end JanetCartan.PhysicalMean
