module

public import JanetCartan.Iteration.PhysicalMean.NativeCross
public import JanetCartan.Iteration.PhysicalMean.DerivativeJets
public import JanetCartan.Iteration.PhysicalMean.Grades
public import JanetCartan.Iteration.PhysicalForwardMean.MatrixBranches

/-!
# The sharp actual balanced differentiated native row

The coefficient derivative, FULL high matrix branch, and lower field derivative
are combined in the literal original modified row. Its bound is proved by the
actual scalar theorem, the exact matrix branch profile and lossless lower-field
jets. The higher derivative stays INSIDE the aggregate input operator
(`app:ch_mean_pairs:eq:block-bilinear`, `new:eq:Q-derivative-term`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open BallExtension PhysicalForwardMean RawPrimary.SliceBounds
open Pseudodifferential PeriodicLocalL2 AmplitudeBound.PaperEstimates

/-- Actual sharp bound for one balanced high quadratic branch. All
amplitude bounds are primitive FULL-amplitude and phase jets, genuine
coefficient jets, and the already-produced lower individual field jets.
There is no successful modified-row estimate or vector realization premise.
The predata factors count only fixed derivative/matrix coordinates. -/
theorem norm_balancedNativeCrossRow_le {n N : ℕ} {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ θ : X → Euclidean n → ℝ) (m : X → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (A : Fin N → Fin n → X → Euclidean n → ℂ)
    (hC : ContDiff ℝ ∞ C) (hB : ∀ u, ContDiff ℝ ∞ (B u))
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ a c u, ContDiff ℝ ∞ (A a c u))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    (dc dt dr : List (Fin n)) (b : SliceDerivativeBranch dr.length)
    (hBc : Continuous (fun q : X × Euclidean n ↦ cartesianCoordinateDerivList dt (B q.1) q.2))
    (hbc : ∀ a c, Continuous (fun q : X × Euclidean n ↦
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
    (hBmem : ∀ u, m u ≠ 0 → ∀ j ≤ n/2+1+dt.length, MemLp (iteratedFDeriv ℝ j (B u)) 2 volume)
    (hBb : ∀ u, m u ≠ 0 →
      (∑ j ∈ Finset.range (n/2+1+dt.length+1), lpNorm (iteratedFDeriv ℝ j (B u)) 2 volume) ≤ Z)
    (Tfull : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ f : Lp ℂ 2 μ, Tfull f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u*f u ∂μ) :
    let Cc := cartesianCoordinateDerivList dc C
    let Bt := fun u ↦ cartesianCoordinateDerivList dt (B u)
    let Gb := matrixForwardBranchAmplitude θ A (fun i ↦ EuclideanSpace.single (dr.get i) 1) b
    let hCc : ContDiff ℝ ∞ Cc := contDiffOn_univ.mp
      (contDiffOn_cartesianCoordinateDerivList isOpen_univ hC.contDiffOn dc)
    let hGb := continuous_matrixForwardBranchAmplitude θ A _ b hbc
    let hGs := fun u ↦ (matrixForwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK _ b u).2
    ‖nativeCrossRow μ φ m hφ hm hms Cc Bt Gb hCc hBc hGb hK hGs‖ ≤
      (Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*
        (∑ j ∈ Finset.range (n/2+1+1), aC (j+dc.length))*
        matrixForwardBranchConstant n N (n/2+1) aG p b*((n/2+1 : ℕ)+1)) *
        ‖Tfull‖*T^(dc.length+dr.length-b.phaseCount-s₀)*Z := by
  intro Cc Bt Gb hCc hGb hGs
  let ell := n/2+1
  let AC := ∑ j ∈ Finset.range (ell+1), aC (j+dc.length)
  let AG := matrixForwardBranchConstant n N ell aG p b
  have hAC : 0 ≤ AC := Finset.sum_nonneg fun j _ ↦ haC _
  have hAG : 0 ≤ AG := matrixForwardBranchConstant_nonneg n N ell b haG hp
  have hT0 := zero_le_one.trans hT
  have hCB : cNorm K ell Cc ≤ AC*T^(dc.length-s₀) :=
    cNorm_cartesianWord_le_reserve hC K dc ell s₀ hT aC haC hCj
  have hGB (u : X) (hu : m u ≠ 0) : cNorm K ell (Gb u) ≤ AG*T^(dr.length-b.phaseCount-s₀) :=
    cNorm_matrixForwardBranch_le_of_localPrimitiveJets θ A m hθ hA hK hAK hT aG p haG hp hAj hθj
      (fun i ↦ EuclideanSpace.single (dr.get i) 1) (fun i ↦ by simp [EuclideanSpace.single]) b u hu
  have hBt (u : X) : ContDiff ℝ ∞ (Bt u) := contDiffOn_univ.mp
    (contDiffOn_cartesianCoordinateDerivList isOpen_univ (hB u).contDiffOn dt)
  have hBjet (u : X) (hu : m u ≠ 0) := cartesianWord_jet_L2_bound (hB u) dt ell (hBmem u hu)
  have hBbound (u : X) (hu : m u ≠ 0) :
      (∑ j ∈ Finset.range (ell+1), lpNorm (iteratedFDeriv ℝ j (Bt u)) 2 volume) ≤ ((ell : ℝ)+1)*Z :=
    (hBjet u hu).2.trans (mul_le_mul_of_nonneg_left (hBb u hu) (by positivity))
  have hn := norm_nativeCrossRow_le μ φ m hφ hm hms Cc Bt Gb hCc hBc hGb hK hGs hBt
    (fun u ↦ (matrixForwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK _ b u).1)
    χ hχ hχs hχK Rbox hbox (AC*T^(dc.length-s₀)) (AG*T^(dr.length-b.phaseCount-s₀))
    (((ell : ℝ)+1)*Z) (by positivity) (by positivity) (by positivity)
    hCB hGB (fun u hu ↦ (hBjet u hu).1) hBbound Tfull hTfull
  have hprod := coefficient_branch_scale_product_le hT (c := dc.length) (r := dr.length)
    (s₀ := s₀) b.phaseCount_le
  let Krow := Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*AC*AG*((ell : ℝ)+1)*‖Tfull‖*Z
  have hKn : 0 ≤ Krow := by
    have := modifiedCrossRowConstant_nonneg n N Rbox
    dsimp only [Krow]
    positivity
  calc
    _ ≤ Krow*(T^(dc.length-s₀)*T^(dr.length-b.phaseCount-s₀)) := hn.trans_eq (by dsimp only [Krow]; ring)
    _ ≤ Krow*T^(dc.length+dr.length-b.phaseCount-s₀) := mul_le_mul_of_nonneg_left hprod hKn
    _ = _ := by dsimp only [Krow, AC, AG, ell]; push_cast; ring

end JanetCartan.PhysicalMean
