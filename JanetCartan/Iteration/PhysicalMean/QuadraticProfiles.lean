module

public import JanetCartan.Iteration.PhysicalMean.CrossBranches
public import JanetCartan.Iteration.PhysicalMean.BalancedIntegral
public import JanetCartan.Iteration.PhysicalMean.LinearProfiles

/-!
# Actual full weighted quadratic source profiles

Sum only the fixed derivative branches after applying the sharp modified row
to every actual full annular term. The lower individual-field and aggregate
input profiles are supplied by IndividualSource and AggregateSource for the
SAME current inverse. Neither a quadratic source estimate nor a successful
quadratic derivative identity is a premise
(`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal

namespace JanetCartan.PhysicalMean
open BallExtension PhysicalForwardMean RawPrimary.SliceBounds PhysicalSamplingShells RawInputRealization LocalSobolev

/-- The fixed word-profile constant sums only binary physical derivative
branches, never sample or shell labels. It is chosen before every source,
current map, inverse, sample, native measure, or carrier scale. -/
def quadraticWordProfileConstant (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ)
    (c t r : ℕ) : ℝ :=
  ∑ b : SliceDerivativeBranch r,
    (Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*
      (∑ j ∈ Finset.range (n/2+1+1), aC (j+c))*
      matrixForwardBranchConstant n N (n/2+1) aG p b*((n/2+1 : ℕ)+1))*MB t*MW b.phaseCount

/-- Nonnegativity of the predata full quadratic word constant. -/
theorem quadraticWordProfileConstant_nonneg (n N : ℕ) (Rbox : ℝ) (aC aG p MB MW : ℕ → ℝ)
    (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j) (hp : ∀ j, 0 ≤ p j)
    (hMB : ∀ j, 0 ≤ MB j) (hMW : ∀ j, 0 ≤ MW j) (c t r : ℕ) :
    0 ≤ quadraticWordProfileConstant n N Rbox aC aG p MB MW c t r := by
  apply Finset.sum_nonneg
  intro b _
  have hrow := modifiedCrossRowConstant_nonneg n N Rbox
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n/2+1+1), aC (j+c) := Finset.sum_nonneg fun j _ ↦ haC _
  have hbranch := matrixForwardBranchConstant_nonneg n N (n/2+1) b haG hp
  have hMBt := hMB t
  have hMWb := hMW b.phaseCount
  positivity

variable {n N : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
    [MeasurableSpace ι] [BorelSpace ι]
    (radius : ι → ℝ) (weight : ι → ℝ)
    (φ θ : (ι × Euclidean (n-1)) → Euclidean n → ℝ) (m : (ι × Euclidean (n-1)) → ℝ)
    (A : Fin N → Fin n → (ι × Euclidean (n-1)) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hθ : ∀ z, ContDiff ℝ ∞ (θ z)) (hA : ∀ a c z, ContDiff ℝ ∞ (A a c z))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c z, tsupport (A a c z) ⊆ K)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : ContDiff ℝ ∞ C)
    (B : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (hfields : ∀ i, ContDiff ℝ ∞ (B i) ∧
      tsupport (B i) ⊆ K)
    (dc dt dr : List (Fin n)) (htr : dt.length ≤ dr.length)
    (hbc : ∀ a c (b : SliceDerivativeBranch dr.length),
      Continuous (fun z : (ι × Euclidean (n-1)) × Euclidean n ↦
        sliceDerivativeAmplitude (θ z.1) (A a c z.1)
          (fun j ↦ EuclideanSpace.single (dr.get j) 1) b z.2))
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (aC aG p MB MW : ℕ → ℝ) (haC : ∀ j, 0 ≤ aC j) (haG : ∀ j, 0 ≤ aG j)
    (hp : ∀ j, 0 ≤ p j) (hMB : ∀ j, 0 ≤ MB j) (hMW : ∀ j, 0 ≤ MW j)
    {T R h : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R) (hh : 0 ≤ h) (m₀ : ℕ)
    (hCj : ∀ x ∈ K, ∀ j ≤ n/2+1+dc.length,
      ‖iteratedFDeriv ℝ j C x‖ ≤ aC j*T^(j-(2*m₀+(n/2+1))))
    (hAj : ∀ a c z, m z ≠ 0 → ∀ x ∈ K, ∀ j ≤ dr.length+(n/2+1),
      ‖iteratedFDeriv ℝ j (A a c z) x‖ ≤ aG j*T^(j-(2*m₀+(n/2+1))))
    (hθj : ∀ z, m z ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ dr.length+(n/2+1) →
      ‖iteratedFDeriv ℝ j (θ z) x‖ ≤ p j*T^(j-1-(2*m₀+(n/2+1))))
    (hBjets : ∀ i, (∑ j ∈ Finset.range (n/2+1+dt.length+1),
      lpNorm (iteratedFDeriv ℝ j (B i)) 2 volume) ≤
        MB dt.length*h*R^(dt.length-m₀))
    (hraw : ∀ k ≤ dr.length,
      lpNorm (fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius weight g z) 2 (annularShellMeasure radius) ≤
        MW k*h*R^(k-2*m₀))
    (Tfull : Lp ℂ 2 (annularShellMeasure radius) →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTfull : ∀ w : Lp ℂ 2 (annularShellMeasure radius), Tfull w =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ (fun z ↦ Real.sqrt (weight z.1)*m z) (fun _ x ↦ (χ x : ℂ)) x z*w z
        ∂annularShellMeasure radius)

include hφ hm hms hθ hA hK hAK hC hfields htr hbc hχ hχs hχK hbox haC haG hp hMB hMW
  hT hR hTR hh hCj hAj hθj hBjets hraw hTfull

/-- The actual finite high-factor branch sum has genuine physical L²
membership and the sharp final `h² R^(c+r+t-s0)` profile. This theorem applies
the full branch row theorem and exact weighted input moment identity before
summing; no samplewise high-field norm occurs. -/
theorem annularCrossWordBranch_L2_profile :
    MemLp (annularCrossWordBranch radius φ θ m A weight C B g dc dt dr) 2 volume ∧
      lpNorm (annularCrossWordBranch radius φ θ m A weight C B g dc dt dr) 2 volume ≤
        quadraticWordProfileConstant n N Rbox aC aG p MB MW dc.length dt.length dr.length*
          ‖Tfull‖*h^2*R^(dc.length+dr.length+dt.length-2*m₀) := by
  let mw := fun z : ι × Euclidean (n-1) ↦ Real.sqrt (weight z.1)*m z
  have hmw : Continuous mw :=
    (((continuous_of_discreteTopology : Continuous weight).comp continuous_fst).sqrt).mul hm
  have hmws : HasCompactSupport mw := hms.mul_left
  let dirs := fun j : Fin dr.length ↦ EuclideanSpace.single (dr.get j) (1 : ℝ)
  let w := fun b : SliceDerivativeBranch dr.length ↦ weightedAnnularInput radius weight
    (annularRadialInput radius g b.phaseCount (fun i ↦ annular_radial_memLp (radius i) (g i) b.phaseCount))
  let F := fun b : SliceDerivativeBranch dr.length ↦ annularMeasuredCross radius φ mw
    (cartesianCoordinateDerivList dc C) (fun i ↦ cartesianCoordinateDerivList dt (B i))
    (matrixForwardBranchAmplitude θ A dirs b) (w b)
  let cb := fun b : SliceDerivativeBranch dr.length ↦
    (Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*
      (∑ j ∈ Finset.range (n/2+1+1), aC (j+dc.length))*
      matrixForwardBranchConstant n N (n/2+1) aG p b*((n/2+1 : ℕ)+1))*MB dt.length*MW b.phaseCount
  have hBmem (i : ι) (j : ℕ) : MemLp (iteratedFDeriv ℝ j (B i)) 2 volume :=
    memLp_iteratedFDeriv_of_contDiff_hasCompactSupport (hfields i).1
      (hK.of_isClosed_subset (isClosed_tsupport _) (hfields i).2) j
  have hb (b : SliceDerivativeBranch dr.length) : MemLp (F b) 2 volume ∧
      lpNorm (F b) 2 volume ≤ cb b*‖Tfull‖*h^2*R^(dc.length+dr.length+dt.length-2*m₀) := by
    have hZ : 0 ≤ MB dt.length*h*R^(dt.length-m₀) :=
      mul_nonneg (mul_nonneg (hMB _) hh) (pow_nonneg (zero_le_one.trans hR) _)
    have hin := annularMeasuredCross_balanced_L2_bound radius φ θ mw hφ hmw hmws C B A hC
      (fun i ↦ (hfields i).1) hθ hA hK hAK dc dt dr b (fun a c ↦ hbc a c b)
      χ hχ hχs hχK Rbox hbox aC aG p haC haG hp hT (2*m₀) hCj
      (fun a c z hz ↦ hAj a c z (mul_ne_zero_iff.mp hz).2)
      (fun z hz ↦ hθj z (mul_ne_zero_iff.mp hz).2)
      hZ (fun i j _ ↦ hBmem i j) hBjets Tfull hTfull (w b)
    have hw : ‖w b‖ ≤ MW b.phaseCount*h*R^(b.phaseCount-2*m₀) := by
      rw [(weightedAnnularInput_radial_memLp_norm radius weight g b.phaseCount
        (fun i ↦ annular_radial_memLp (radius i) (g i) b.phaseCount)).2]
      exact hraw b.phaseCount b.phaseCount_le
    refine ⟨hin.1, ?_⟩
    exact (hin.2.2 m₀ rfl htr R h (MB dt.length) (MW b.phaseCount) hR hTR hh (hMB _) (hMW _)
      le_rfl hw).trans_eq (by dsimp only [cb]; ring)
  have hmem := memLp_finsetSum Finset.univ (fun b _ ↦ (hb b).1)
  refine ⟨hmem, ?_⟩
  have hn := lpNorm_sum_le (s := Finset.univ) (fun b _ ↦ (hb b).1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  change lpNorm (fun x ↦ ∑ b, F b x) 2 volume ≤ _
  calc
    _ = lpNorm (∑ b, F b) 2 volume := by congr 1; funext x; simp
    _ ≤ ∑ b, lpNorm (F b) 2 volume := hn
    _ ≤ ∑ b, cb b*‖Tfull‖*h^2*R^(dc.length+dr.length+dt.length-2*m₀) :=
      Finset.sum_le_sum (fun b _ ↦ (hb b).2)
    _ = _ := by simp only [← Finset.sum_mul]; rfl

end JanetCartan.PhysicalMean
