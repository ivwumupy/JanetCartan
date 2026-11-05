module

public import JanetCartan.Iteration.PhysicalMean.IndividualField

/-!
# The actual individual field on the same current uncut inverse

This instantiates the original full matrix Bochner field with the original
real adjoint of the SAME current inverse datum. It closes the precise low
`H^m0` and balanced high source budgets needed by the full modified row.
The full corrected amplitudes and their exact forward kernel identities
remain the parent original-data producer's obligation; they are never
replaced by a principal term or the zero-source background.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean PeriodicLocalL2 Pseudodifferential AmplitudeBound.PaperEstimates
open PhysicalForwardMean PhysicalSamplingShells RawInputPartition

/-- Choose the full individual-field constant before its band count, current
phase, amplitudes, tester, current inverse and source. -/
def individualNativeFieldConstant (n N s : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) : ℝ :=
  (exists_individualNativeField_jet_constant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj).choose

/-- Nonnegativity of the fixed original individual-field constant. -/
theorem individualNativeFieldConstant_nonneg (n N s : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j) :
    0 ≤ individualNativeFieldConstant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj :=
  (exists_individualNativeField_jet_constant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj).choose_spec.1

/-- The literal full matrix Bochner field, fed by the actual original real
adjoint of THIS supplied current uncut inverse. The whole original disjoint
shell measure remains one integral; no bandwise norm is summed. -/
def individualNativeInverseField {n N J : ℕ}
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ)
    (G : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (A : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n) : Euclidean n → Matrix (Fin N) (Fin n) ℂ :=
  fun x ↦ ∫ u,
    ((fun a b ↦ physicalForwardKernel φ (fun u ↦ m u*Real.sqrt ‖u.2‖)
      (fun u ↦ G a b u.1 u.2) x u *
        ((transferOutputOperator (realQuadratureChannel A)).adjoint (Q₀ e)) u) :
          Matrix (Fin N) (Fin n) ℂ)
    ∂(annularShellMeasure (n := n) (refinedRadius (J := J)))

/-- Actual low and high physical source-jet budgets for the SAME individual
field `Grawν (Aν* (Q₀ e))`. At `s=ell`, the low clause is EXACTLY `H^m0(e)`.
At `s=ell+t`, the high clause gives the lower-factor grade `t-m0` when
`s₀=2*m0`; this factor, not the higher differentiated factor, is used outside
the aggregate row (`app:ch_mean_pairs:eq:block-bilinear`).

The only analytic inverse premise is the original uncut-current estimate
`bg-r-inverse`; the original current inverse producer supplies it and the
all-order membership. Neither a desired field norm nor a successful mean
source is an input. -/
theorem individualNativeInverseField_bounds
    (n N s : ℕ) (Rbox : ℝ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχcell : tsupport χ ⊆ halfOpenCell n)
    (aG p Badj : ℕ → ℝ) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hBadj : ∀ j, 0 ≤ Badj j)
    (Cinv : ℕ → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
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
    (hL : ∀ i h, ContDiff ℝ ∞ (fun q : Euclidean (n-1) × Euclidean n ↦ L i q.1 h q.2))
    (hm : Continuous m) (hms : HasCompactSupport m) (hhigh : ∀ u, ‖u.2‖ ≤ 1 → m u = 0)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hGK : ∀ a b i η, tsupport (G a b i η) ⊆ K)
    (haK : ∀ i j η, tsupport (a i j η) ⊆ K)
    (hagree : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x)
    (hphase : ∀ u, m u ≠ 0 → ∀ h x, x ∈ K → inner ℝ h u.2 = fderiv ℝ (φ u) x (L u.1 u.2 h x))
    (hχK : ∀ x ∈ K, χ x = 1) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s₀ : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hGj : ∀ a0 b0 i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (G a0 b0 i η) x‖ ≤ aG j*T^(j-(s₀+(n/2+1))))
    (hΦj : ∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y/‖η‖) x‖ ≤ p j*T^(j-1-(s₀+(n/2+1))))
    (haj : ∀ i j η, m (j,η) ≠ 0 → ∀ x ∈ K, ∀ r,
      ‖iteratedFDeriv ℝ r (a i j η) x‖ ≤ Badj r*T^(r-(s₀+(n/2+1))))
    (hLj : ∀ j η, m (j,η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ r,
      ‖iteratedFDeriv ℝ r (L j η h) x‖ ≤ Badj r*T^(r-(s₀+(n/2+1))))
    (Tbare : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTbare : ∀ f, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u*f u
      ∂(annularShellMeasure (n := n) (refinedRadius (J := J))))
    (A : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hA : ∀ f i, finiteL2CoordinateIsometry volume (A f) i =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ (halfWeightedMomentMask m) (fun u y ↦ a i u.1 u.2 y) x u*f u
      ∂(annularShellMeasure (n := n) (refinedRadius (J := J))))
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n)
    (hreg : ∀ j, Q₀ e ∈ periodicSobolevLevel n (Euclidean n) j)
    (hinverse : ∀ j, j ≤ s+1 → periodicSobolevNorm j (Q₀ e) ≤
      Cinv j * (periodicSobolevNorm j e + T^(j-s₀)*‖e‖)) :
    let D := individualNativeFieldConstant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
    let CI := ∑ i ∈ Finset.range (s+1+1), Cinv i
    let B := individualNativeInverseField φ m G A Q₀ e
    ContDiff ℝ ∞ B ∧ tsupport B ⊆ K ∧
      (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j B) 2 volume) ∧
      ((s+1 ≤ s₀) → e ∈ periodicSobolevLevel n (Euclidean n) (s+1) →
        ∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j B) 2 volume ≤
          2*D*CI*‖Tbare‖^2*periodicSobolevNorm (s+1) e) ∧
      (∀ R : ℝ, 1 ≤ R → T ≤ R → ∀ M : ℝ, 0 ≤ M →
        (∀ i, i ≤ s+1 → periodicSobolevNorm i e ≤ M*R^(i-s₀)) →
        ∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j B) 2 volume ≤
          D*((s : ℝ)+3)*CI*((s : ℝ)+2)*‖Tbare‖^2*M*R^(s+1-s₀)) := by
  dsimp only
  let D := individualNativeFieldConstant n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
  have hD := individualNativeFieldConstant_nonneg n N s Rbox χ hχ hχs hχcell aG p Badj haG hp hBadj
  have hf := (exists_individualNativeField_jet_constant n N s Rbox χ hχ hχs hχcell
    aG p Badj haG hp hBadj).choose_spec.2
      J φ Φ G a L m hφ hφs hΦ hG ha hL hm hms hhigh hK hGK haK hagree hphase hχK hbox
      hT hGj hΦj haj hLj Tbare hTbare A hA (Q₀ e) hreg
  change ContDiff ℝ ∞ (individualNativeInverseField φ m G A Q₀ e) ∧
      tsupport (individualNativeInverseField φ m G A Q₀ e) ⊆ K ∧
      (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j (individualNativeInverseField φ m G A Q₀ e)) 2 volume) ∧
      (∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j (individualNativeInverseField φ m G A Q₀ e)) 2 volume) ≤
        D*‖Tbare‖^2*∑ i ∈ Finset.range (s+1+1), T^(s+1-i-s₀)*periodicSobolevNorm i (Q₀ e) at hf
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
  · intro hs he
    have hi := inverseSource_low_moment_sum_le Q₀ e Cinv hCinv (s+1) s₀ hs T he hinverse
    exact (hf.2.2.2.trans (mul_le_mul_of_nonneg_left hi
      (mul_nonneg hD (sq_nonneg _)))).trans_eq (by dsimp only [D]; push_cast; ring)
  · intro R hR hTR M hM hsource
    have hi := inverseSource_profile_moment_sum_le Q₀ e Cinv hCinv (s+1) s₀ hT hR hTR M hM hinverse hsource
    exact (hf.2.2.2.trans (mul_le_mul_of_nonneg_left hi
      (mul_nonneg hD (sq_nonneg _)))).trans_eq (by dsimp only [D]; push_cast; ring)

end JanetCartan.PhysicalMean
