module

public import JanetCartan.Iteration.PhysicalMean.IndividualSource
public import JanetCartan.Iteration.PhysicalMean.AggregateSource

/-!
# Fixed source-profile budgets for the actual native current fields

These constants are chosen before every current, sample and source. They
consume the genuine source profile, then APPLY IndividualSource and
AggregateSource to the SAME inverse. The lower physical field spends exactly
`ell+t+1`, giving grade `(t-m0)+`; the higher input stays in its original
aggregate radial moment (`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open PhysicalForwardMean PhysicalSamplingShells RawInputPartition ContinuumRow PeriodicLocalL2 Pseudodifferential

/-- A finite order-only majorant of the source profile, never a sample sum. -/
def sourceProfilePrefix (M : ℕ → ℝ) (q : ℕ) : ℝ := ∑ i ∈ Finset.range (q+1), M i

/-- Nonnegativity of the fixed finite source-profile majorant. -/
theorem sourceProfilePrefix_nonneg (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i) (q : ℕ) :
    0 ≤ sourceProfilePrefix M q := Finset.sum_nonneg fun i _ ↦ hM i

/-- Each required source order is bounded by the same prechosen finite prefix. -/
theorem sourceProfile_le_prefix (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i) {i q : ℕ} (hi : i ≤ q) :
    M i ≤ sourceProfilePrefix M q :=
  Finset.single_le_sum (fun i _ ↦ hM i) (Finset.mem_range.mpr (by omega))

/-- The fixed full lower-field source constant at word order `t`. Its bare
tester factor is squared because the SAME raw forward and individual adjoint
are composed. No half-weighted aggregate tester is substituted here. -/
def nativeLowerSourceProfileConstant (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (Cbare : ℝ) (t : ℕ) : ℝ :=
  let s := n/2+1+t
  individualNativeFieldConstant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj*
    ((s : ℝ)+3)*(∑ i ∈ Finset.range (s+1+1), Cinv i)*((s : ℝ)+2)*Cbare^2*sourceProfilePrefix M (s+1)

/-- Positivity of the lower-field profile before any current/sample is chosen. -/
theorem nativeLowerSourceProfileConstant_nonneg (n N : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (hM : ∀ j, 0 ≤ M j)
    (Cbare : ℝ) (t : ℕ) :
    0 ≤ nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare t := by
  have hD := individualNativeFieldConstant_nonneg n N (n/2+1+t) Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
  have hI : 0 ≤ ∑ i ∈ Finset.range (n/2+1+t+1+1), Cinv i := Finset.sum_nonneg fun i _ ↦ hCinv i
  have hP := sourceProfilePrefix_nonneg M hM (n/2+1+t+1)
  dsimp only [nativeLowerSourceProfileConstant]
  positivity

/-- The full native individual source field has exactly the lower-factor
profile required by the balanced quadratic row. All original physical jets,
bare tester, measured adjoint and current inverse are used explicitly. -/
theorem individualNativeInverseField_source_profile
    (n N t : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj Cinv M : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) (hCinv : ∀ j, 0 ≤ Cinv j) (hM : ∀ j, 0 ≤ M j)
    (Cbare : ℝ)
    (J : ℕ)
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
    (hinverse : ∀ j, j ≤ n/2+1+t+1 → periodicSobolevNorm j (Q₀ e) ≤
      Cinv j*(periodicSobolevNorm j e+T^(j-2*(n/2+2))*‖e‖))
    (hsource : ∀ j ≤ n/2+1+t+1, periodicSobolevNorm j e ≤ M j*h*R^(j-2*(n/2+2))) :
    let B := individualNativeInverseField φ m G A Q₀ e
    ContDiff ℝ ∞ B ∧ tsupport B ⊆ K ∧
      (∀ j ≤ n/2+1+t, MemLp (iteratedFDeriv ℝ j B) 2 volume) ∧
      (∑ j ∈ Finset.range (n/2+1+t+1), lpNorm (iteratedFDeriv ℝ j B) 2 volume) ≤
        nativeLowerSourceProfileConstant n N Rbox χ hχ hχs hχcell aG p Badj Cinv M haG hp hBadj Cbare t*
          h*R^(t-(n/2+2)) := by
  intro B
  let s := n/2+1+t
  have hb := individualNativeInverseField_bounds n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
    Cinv hCinv J φ Φ G a L m hφ hφs hΦ hG ha hL hm hms hhigh hK hGK haK hagree hphase hχK hbox
    hT hGj hΦj haj hLj Tbare hTbare A hA Q₀ e hreg hinverse
  have hP := sourceProfilePrefix_nonneg M hM (s+1)
  have hs : ∀ j ≤ s+1, periodicSobolevNorm j e ≤ (sourceProfilePrefix M (s+1)*h)*R^(j-2*(n/2+2)) := by
    intro j hj
    exact (hsource j hj).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sourceProfile_le_prefix M hM hj) hh) (pow_nonneg (zero_le_one.trans hR) _))
  have hbound := hb.2.2.2.2 R hR hTR (sourceProfilePrefix M (s+1)*h) (mul_nonneg hP hh) hs
  have hgrade : s+1-2*(n/2+2) = t-(n/2+2) := by dsimp only [s]; omega
  rw [hgrade] at hbound
  let D := individualNativeFieldConstant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
  have hD := individualNativeFieldConstant_nonneg n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
  have hI : 0 ≤ ∑ i ∈ Finset.range (s+1+1), Cinv i := Finset.sum_nonneg fun i _ ↦ hCinv i
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hbound.trans ?_⟩
  dsimp only [nativeLowerSourceProfileConstant]
  have ht : ‖Tbare‖^2 ≤ Cbare^2 := pow_le_pow_left₀ (norm_nonneg _) hTbareBound 2
  calc
    _ ≤ D*((s : ℝ)+3)*(∑ i ∈ Finset.range (s+1+1), Cinv i)*((s : ℝ)+2)*Cbare^2*
        (sourceProfilePrefix M (s+1)*h)*R^(t-(n/2+2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (by positivity)) (mul_nonneg hP hh)) (pow_nonneg (zero_le_one.trans hR) _)
    _ = _ := by dsimp only [D, s]; ring

end JanetCartan.PhysicalMean
