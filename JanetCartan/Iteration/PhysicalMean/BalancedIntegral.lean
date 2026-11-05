module

public import JanetCartan.Iteration.PhysicalMean.BalancedRow
public import JanetCartan.Iteration.PhysicalMean.CrossIntegral

/-!
# Actual physical L² bounds for the balanced full quadratic branches

Apply the proven sharp native row bound to the literal measured Hermitian
integral on the original disjoint annuli. Lower-field continuity is derived
from its smooth physical fields and the retained discrete labels; it is not
postulated. The frequency-weighted higher input remains INSIDE the same
aggregate native row (`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open BallExtension PhysicalForwardMean RawPrimary.SliceBounds PhysicalSamplingShells RawInputRealization

/-- One actual balanced differentiated quadratic branch has genuine physical
L² membership and the sharp native aggregate bound. The primitive factors
are the exact FULL matrix branch, coefficient jets and lower individual-field
jets. No successful row norm, integral realization, or derivative estimate
for the quadratic tensor is a premise. -/
theorem annularMeasuredCross_balanced_L2_bound {n N : ℕ} {ι : Type*}
    [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    (radius : ι → ℝ)
    (φ θ : (ι × Euclidean (n-1)) → Euclidean n → ℝ) (m : (ι × Euclidean (n-1)) → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (A : Fin N → Fin n → (ι × Euclidean (n-1)) → Euclidean n → ℂ)
    (hC : ContDiff ℝ ∞ C) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ a c u, ContDiff ℝ ∞ (A a c u))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    (dc dt dr : List (Fin n)) (b : SliceDerivativeBranch dr.length)
    (hbc : ∀ a c, Continuous (fun q : (ι × Euclidean (n-1)) × Euclidean n ↦
      sliceDerivativeAmplitude (θ q.1) (A a c q.1)
        (fun i ↦ EuclideanSpace.single (dr.get i) 1) b q.2))
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (aC aG p : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    {T : ℝ} (hT : 1 ≤ T) (s₀ : ℕ)
    (hCj : ∀ x ∈ K, ∀ j ≤ n/2+1+dc.length,
      ‖iteratedFDeriv ℝ j C x‖ ≤ aC j*T^(j-(s₀+(n/2+1))))
    (hAj : ∀ a c u, m u ≠ 0 → ∀ x ∈ K, ∀ j ≤ dr.length+(n/2+1),
      ‖iteratedFDeriv ℝ j (A a c u) x‖ ≤ aG j*T^(j-(s₀+(n/2+1))))
    (hθj : ∀ u, m u ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ dr.length+(n/2+1) →
      ‖iteratedFDeriv ℝ j (θ u) x‖ ≤ p j*T^(j-1-(s₀+(n/2+1))))
    {Z : ℝ} (hZ : 0 ≤ Z)
    (hBmem : ∀ i, ∀ j ≤ n/2+1+dt.length, MemLp (iteratedFDeriv ℝ j (B i)) 2 volume)
    (hBb : ∀ i, (∑ j ∈ Finset.range (n/2+1+dt.length+1), lpNorm (iteratedFDeriv ℝ j (B i)) 2 volume) ≤ Z)
    (Tfull : Lp ℂ 2 (annularShellMeasure radius) →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ f : Lp ℂ 2 (annularShellMeasure radius), Tfull f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u*f u ∂annularShellMeasure radius)
    (w : Lp ℂ 2 (annularShellMeasure radius)) :
    let Cc := cartesianCoordinateDerivList dc C
    let Bt := fun i ↦ cartesianCoordinateDerivList dt (B i)
    let Gb := matrixForwardBranchAmplitude θ A (fun i ↦ EuclideanSpace.single (dr.get i) 1) b
    let Cbranch := Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*
      (∑ j ∈ Finset.range (n/2+1+1), aC (j+dc.length))*
      matrixForwardBranchConstant n N (n/2+1) aG p b*((n/2+1 : ℕ)+1)
    MemLp (annularMeasuredCross radius φ m Cc Bt Gb w) 2 volume ∧
      lpNorm (annularMeasuredCross radius φ m Cc Bt Gb w) 2 volume ≤
        Cbranch*‖Tfull‖*T^(dc.length+dr.length-b.phaseCount-s₀)*Z*‖w‖ ∧
      ∀ m₀ : ℕ, s₀ = 2*m₀ → dt.length ≤ dr.length →
      ∀ R h CB CW : ℝ, 1 ≤ R → T ≤ R → 0 ≤ h → 0 ≤ CB → 0 ≤ CW →
        Z ≤ CB*h*R^(dt.length-m₀) → ‖w‖ ≤ CW*h*R^(b.phaseCount-s₀) →
        lpNorm (annularMeasuredCross radius φ m Cc Bt Gb w) 2 volume ≤
          Cbranch*‖Tfull‖*CB*CW*h^2*R^(dc.length+dr.length+dt.length-s₀) := by
  intro Cc Bt Gb Cbranch
  have hCc : ContDiff ℝ ∞ Cc := contDiffOn_univ.mp
    (contDiffOn_cartesianCoordinateDerivList isOpen_univ hC.contDiffOn dc)
  have hBt (i : ι) : ContDiff ℝ ∞ (Bt i) := contDiffOn_univ.mp
    (contDiffOn_cartesianCoordinateDerivList isOpen_univ (hB i).contDiffOn dt)
  have hBct : Continuous (fun p : ι × Euclidean n ↦ Bt p.1 p.2) :=
    continuous_prod_of_discrete_left.mpr (fun i ↦ (hBt i).continuous)
  have hBc : Continuous (fun p : (ι × Euclidean (n-1)) × Euclidean n ↦ Bt p.1.1 p.2) :=
    hBct.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hGb : Continuous (Function.uncurry Gb) := continuous_matrixForwardBranchAmplitude θ A _ b hbc
  have hGs (u : ι × Euclidean (n-1)) : tsupport (Gb u) ⊆ K :=
    (matrixForwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK _ b u).2
  have hi := annularMeasuredCross_memLp_norm radius φ m hφ hm hms Cc Bt Gb hCc hBc hGb hK hGs w
  have hr := norm_balancedNativeCrossRow_le (annularShellMeasure radius) φ θ m hφ hm hms
    C (fun u ↦ B u.1) A hC (fun u ↦ hB u.1) hθ hA hK hAK dc dt dr b hBc hbc
    χ hχ hχs hχK Rbox hbox aC aG p haC haG hp hT s₀ hCj hAj hθj hZ
    (fun u _ ↦ hBmem u.1) (fun u _ ↦ hBb u.1) Tfull hTfull
  have hb := hi.2.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg w))
  refine ⟨hi.1, hb, ?_⟩
  intro m₀ hs₀ htr R h CB CW hR hTR hh hCB hCW hZp hwp
  have hT0 := zero_le_one.trans hT
  have hCbranch : 0 ≤ Cbranch := by
    have hrow := modifiedCrossRowConstant_nonneg n N Rbox
    have hsum : 0 ≤ ∑ j ∈ Finset.range (n/2+1+1), aC (j+dc.length) :=
      Finset.sum_nonneg fun j _ ↦ haC _
    have hmatrix := matrixForwardBranchConstant_nonneg n N (n/2+1) b haG hp
    dsimp only [Cbranch]
    positivity
  have hgrade : T^(dc.length+dr.length-b.phaseCount-s₀)*R^(b.phaseCount-s₀)*R^(dt.length-m₀) ≤
      R^(dc.length+dr.length+dt.length-s₀) := by
    rw [hs₀]
    simpa only [Nat.sub_self, Nat.zero_sub, pow_zero, mul_one] using
      (quadratic_source_scale_product_le hR hT0 hTR (i := b.phaseCount) (k := b.phaseCount)
        (c := dc.length) (r := dr.length) (t := dt.length) (m₀ := m₀) le_rfl b.phaseCount_le htr)
  have hbudget : T^(dc.length+dr.length-b.phaseCount-s₀)*Z*‖w‖ ≤
      CB*CW*h^2*R^(dc.length+dr.length+dt.length-s₀) := by
    calc
      _ = T^(dc.length+dr.length-b.phaseCount-s₀)*(Z*‖w‖) := by ring
      _ ≤ T^(dc.length+dr.length-b.phaseCount-s₀)*((CB*h*R^(dt.length-m₀))*(CW*h*R^(b.phaseCount-s₀))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hZp hwp (norm_nonneg w) (by positivity)) (pow_nonneg hT0 _)
      _ = CB*CW*h^2*(T^(dc.length+dr.length-b.phaseCount-s₀)*R^(b.phaseCount-s₀)*R^(dt.length-m₀)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrade (by positivity)
  calc
    _ ≤ (Cbranch*‖Tfull‖)*(T^(dc.length+dr.length-b.phaseCount-s₀)*Z*‖w‖) := hb.trans_eq (by ring)
    _ ≤ (Cbranch*‖Tfull‖)*(CB*CW*h^2*R^(dc.length+dr.length+dt.length-s₀)) :=
      mul_le_mul_of_nonneg_left hbudget (mul_nonneg hCbranch (norm_nonneg Tfull))
    _ = _ := by ring

end JanetCartan.PhysicalMean
