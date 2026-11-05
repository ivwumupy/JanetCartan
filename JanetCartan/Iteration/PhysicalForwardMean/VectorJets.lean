module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import JanetCartan.Iteration.PhysicalForwardMean.SingleCurrent
public import JanetCartan.Analysis.Sobolev.Local.Cutoff.Product
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.NormComparison
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.Integrability
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Frobenius
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.MatrixIntegrals

/-!
# Lossless physical matrix jets of the same individual forward field

The lower factor in `app:ch_mean_pairs:eq:block-fields` and the literal modified
cross amplitude in `main:prop:mean` needs physical H^ell, not C^ell. Finite matrix
coordinate assembly and the existing Cartesian/Fréchet comparison preserve the
EXACT derivative order and physical Lebesgue measure. No Sobolev embedding,
periodic replacement, support-volume factor or input-frequency power is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open LocalSobolev Pseudodifferential AmplitudeBound
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin N) (Fin n) ℂ

private theorem norm_matrix_le_entry_sum (A : Mat) :
    ‖A‖ ≤ ∑ a, ∑ b, ‖A a b‖ := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  exact (Finset.sum_le_sum fun a _ ↦
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)).trans
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ by positivity))

/-- Finite coordinate assembly in the actual Frobenius norm and physical L².
Only the fixed output dimensions are summed, never the samples or bands
(`app:ch_mean_pairs:eq:block-fields`). -/
theorem lpNorm_matrix_le_sum_entries {B : E → Mat} (hB : MemLp B 2 volume) :
    lpNorm B 2 volume ≤ ∑ a, ∑ b, lpNorm (fun x ↦ B x a b) 2 volume := by
  classical
  let f : (Fin N × Fin n) → E → ℝ := fun ab x ↦ ‖B x ab.1 ab.2‖
  have hf (ab : Fin N × Fin n) : MemLp (f ab) 2 volume :=
    ((matrixEntryEvaluation ab.1 ab.2).comp_memLp' hB).norm
  let F : E → ℝ := ∑ ab, f ab
  have hF : MemLp F 2 volume := memLp_finsetSum' _ (fun ab _ ↦ hf ab)
  have hFn (x : E) : 0 ≤ F x := by
    simp only [F, Finset.sum_apply, f]
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpoint (x : E) : ‖B x‖ ≤ 1 * ‖F x‖ := by
    rw [one_mul, Real.norm_of_nonneg (hFn x)]
    simpa only [F, Finset.sum_apply, f, Fintype.sum_prod_type] using norm_matrix_le_entry_sum (B x)
  have hb := eLpNorm_toReal_le_mul_of_bound hB.aestronglyMeasurable hF (by norm_num) hpoint
  simp only [toReal_eLpNorm, one_mul] at hb
  calc
    _ ≤ lpNorm F 2 volume := hb
    _ ≤ ∑ ab, lpNorm (f ab) 2 volume := lpNorm_sum_le (fun ab _ ↦ hf ab) (by norm_num)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact lpNorm_norm ((matrixEntryEvaluation a b).comp_memLp' hB).aestronglyMeasurable 2

/-- The SAME matrix Cartesian jet has exactly the original scalar coordinate
word in every entry. This is an identity, not a norm change or another field
(`app:not:fourier`; `app:ch_mean_pairs:eq:block-fields`). -/
theorem matrix_cartesianJetDerivative_apply
    {B : E → Mat} (hB : ContDiff ℝ ∞ B) (α : Fin n → ℕ)
    (a : Fin N) (b : Fin n) (x : E) :
    (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j B) α x) a b =
      euclideanCoordinateDerivList (sobolevDerivativeList α) (fun y ↦ B y a b) x := by
  let ds := sobolevDerivativeList α
  have he := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv
    ((matrixEntryEvaluation a b).contDiff.comp hB) ds.get x
  rw [List.ofFn_get] at he
  change _ = euclideanCoordinateDerivList ds ((matrixEntryEvaluation a b) ∘ B) x
  rw [he, (matrixEntryEvaluation a b).iteratedFDeriv_comp_left hB.contDiffAt (by simp)]
  simp only [cartesianJetDerivative, EuclideanSpace.basisFun_apply]
  rfl

/-- Fixed dimension/order constants transfer the actual scalar entrywise
Cartesian L² estimates to the SAME matrix Fréchet L² jets at exactly order `s`.
This is the lower-factor input of `PhysicalMean.crossAmplitude_jet_L2_bound`,
not a C^s bound. The result includes zero row/column dimensions and requires no
sign assumption on the supplied upper bound (`main:prop:mean`). -/
theorem exists_matrix_jetL2_le_coordinate_bound (n N s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : Euclidean n → Matrix (Fin N) (Fin n) ℂ,
      ContDiff ℝ ∞ B → HasCompactSupport B → ∀ M : ℝ,
      (∀ ds : List (Fin n), ds.length ≤ s → ∀ a b,
        MemLp (euclideanCoordinateDerivList ds (fun x ↦ B x a b)) 2 volume ∧
        lpNorm (euclideanCoordinateDerivList ds (fun x ↦ B x a b)) 2 volume ≤ M) →
      (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j B) 2 volume) ∧
      ∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j B) 2 volume ≤ C*M := by
  classical
  let A : ℝ := Real.sqrt (((s : ℝ)+1)*BallExtension.frechetEnergyComparisonConstant n s)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨A*((sobolevMultiindices n s).card : ℝ)*N*n, by positivity, ?_⟩
  intro B hB hBc M hcoord
  have hJ (j : ℕ) := memLp_iteratedFDeriv_of_contDiff_hasCompactSupport hB hBc j
  refine ⟨fun j _ ↦ hJ j,?_⟩
  let J := fun j ↦ iteratedFDeriv ℝ j B
  have hcart (α : Fin n → ℕ) : MemLp (cartesianJetDerivative J α) 2 volume := by
    simpa only [Measure.restrict_univ] using
      (memLp_cartesianJetDerivative (U := univ) α (by simpa only [Measure.restrict_univ] using hJ (∑ i,α i)))
  have hnorm : cartesianJetNorm univ s J ≤
      ∑ α ∈ sobolevMultiindices n s, lpNorm (cartesianJetDerivative J (fun i ↦ α (some i))) 2 volume := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨Finset.sum_nonneg (fun _ _ ↦ by rw [← toReal_eLpNorm]; exact ENNReal.toReal_nonneg),?_⟩
    calc
      cartesianJetEnergy univ s J = ∑ α ∈ sobolevMultiindices n s,
          (lpNorm (cartesianJetDerivative J (fun i ↦ α (some i))) 2 volume)^2 := by
        unfold cartesianJetEnergy
        apply Finset.sum_congr rfl
        intro α _
        simp only [Measure.restrict_univ]
        symm
        simpa only [toReal_eLpNorm] using
          eLpNorm_toReal_sq_eq_integral_norm_sq (hcart (fun i ↦ α (some i)))
      _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ by rw [← toReal_eLpNorm]; exact ENNReal.toReal_nonneg)
  have hcartbound : cartesianJetNorm univ s J ≤ ((sobolevMultiindices n s).card : ℝ)*N*n*M := by
    calc
      _ ≤ ∑ α ∈ sobolevMultiindices n s,
          lpNorm (cartesianJetDerivative J (fun i ↦ α (some i))) 2 volume := hnorm
      _ ≤ ∑ α ∈ sobolevMultiindices n s, ∑ a : Fin N, ∑ b : Fin n, M := by
        apply Finset.sum_le_sum
        intro α hα
        apply (lpNorm_matrix_le_sum_entries (hcart (fun i ↦ α (some i)))).trans
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        have ho : (sobolevDerivativeList (fun i ↦ α (some i))).length ≤ s := by
          rw [sobolevDerivativeList_length]
          have hh := mem_sobolevMultiindices.mp hα
          omega
        have he : (fun x ↦ cartesianJetDerivative J (fun i ↦ α (some i)) x a b) =
            euclideanCoordinateDerivList (sobolevDerivativeList (fun i ↦ α (some i))) (fun x ↦ B x a b) :=
          funext (matrix_cartesianJetDerivative_apply hB _ a b)
        rw [he]
        exact (hcoord _ ho a b).2
      _ = _ := by simp; ring
  let : InnerProductSpace ℝ (Matrix (Fin N) (Fin n) ℂ) :=
    CurrentMean.matrixFrobeniusInnerProductSpace
  have hcompare := jetL2Norm_iteratedFDerivWithin_le_mul_cartesianJetNorm
    isOpen_univ s hB.contDiffOn (fun j _ ↦ by
      simpa only [iteratedFDerivWithin_univ, Measure.restrict_univ] using hJ j)
  simp only [iteratedFDerivWithin_univ, jetL2Norm, Measure.restrict_univ, toReal_eLpNorm] at hcompare
  exact (hcompare.trans (mul_le_mul_of_nonneg_left hcartbound hA)).trans_eq (by ring)

open PhysicalMean PhysicalSamplingShells RawInputPartition
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

/-- Apply the original scalar half-moment producer to the LITERAL full matrix
Bochner integral of the SAME individual field `Dν v`. Kernel integrability,
entry identities, smoothness and the original support are derived here, not
supplied as output estimates. The fixed constant precedes samples, scale,
current phase/amplitude, tester and input. The exact order `s` and moments
`k+1/2`, `k ≤ s`, are preserved. Consumer: the `H^ell(Dν v)` lower factor in
`PhysicalMean.crossAmplitude_jet_L2_bound`, `app:ch_mean_pairs:eq:block-fields`
and `app:ch_mean_pairs:eq:mean-quadratic-low`. -/
theorem exists_singleForward_matrix_halfMoment_constant
    (n N s : ℕ) (Rbox : ℝ) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ,
    let X := RefinedIndex J × Euclidean (n-1)
    let μ := annularShellMeasure (n := n) (refinedRadius (J := J))
    ∀ (φ : X → Euclidean n → ℝ)
      (Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ)
      (A : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
      (mBare : X → ℝ),
      Continuous (Function.uncurry φ) →
      (∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i))) →
      (∀ a b i, ContDiff ℝ ∞ (Function.uncurry (A a b i))) →
      Continuous mBare → HasCompactSupport mBare →
      (∀ u, mBare u ≠ 0 → 1 ≤ ‖u.2‖) →
    ∀ {K : Set (Euclidean n)}, IsCompact K →
      (∀ a b i η, tsupport (A a b i η) ⊆ K) →
      (∀ u, mBare u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x) →
    ∀ χ : Euclidean n → ℝ, Continuous χ → HasCompactSupport χ →
      (∀ x ∈ K, χ x = 1) → (∀ x ∈ K, ∀ i, |x i| ≤ Rbox) →
    ∀ {s0 : ℕ} {T : ℝ}, 1 ≤ T →
      (∀ a0 b0 i η, mBare (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
        ‖iteratedFDeriv ℝ j (A a0 b0 i η) x‖ ≤ a j*T^(j-(s0+(n/2+1)))) →
      (∀ i η, mBare (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
        ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y/‖η‖) x‖ ≤ p j*T^(j-1-(s0+(n/2+1)))) →
    ∀ Tbare : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)),
      (∀ f : Lp ℂ 2 μ, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
        sampledMomentKernel φ mBare (fun _ y ↦ (χ y : ℂ)) x u*f u ∂μ) →
    ∀ v : Lp ℂ 2 μ,
    let B : Euclidean n → Matrix (Fin N) (Fin n) ℂ := fun x ↦ ∫ u,
      ((fun a0 b0 ↦ physicalForwardKernel φ (fun u ↦ mBare u*Real.sqrt ‖u.2‖)
        (fun u ↦ A a0 b0 u.1 u.2) x u*v u) : Matrix (Fin N) (Fin n) ℂ) ∂μ
    ContDiff ℝ ∞ B ∧ tsupport B ⊆ K ∧
      (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j B) 2 volume) ∧
      ∑ j ∈ Finset.range (s+1), lpNorm (iteratedFDeriv ℝ j B) 2 volume ≤
        C*‖Tbare‖*∑ k ∈ Finset.range (s+1), T^(s-k-s0)*
          (eLpNorm (fun u : X ↦ ((‖u.2‖^((k : ℝ)+1/2) : ℝ) : ℂ)*v u) 2 μ).toReal := by
  classical
  obtain ⟨C0,hC0,htransfer⟩ := exists_matrix_jetL2_le_coordinate_bound n N s
  let D := ∑ j ∈ Finset.range (s+1), forwardDerivativeConstant n Rbox a p j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ forwardDerivativeConstant_nonneg n Rbox a p j ha hp
  refine ⟨C0*D,mul_nonneg hC0 hD,?_⟩
  intro J X μ φ Φ A mBare hφ hΦ hA hm hms hhigh K hK hAK hagree χ hχ hχs hχK hbox s0 T hT hAj hΦj Tbare hTbare v B
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
  let mHalf : X → ℝ := fun u ↦ mBare u*Real.sqrt ‖u.2‖
  have hmHalf : Continuous mHalf := hm.mul (Real.continuous_sqrt.comp continuous_snd.norm)
  have hmHalfS : HasCompactSupport mHalf := hms.mul_right
  have hAc (a0 : Fin N) (b0 : Fin n) :
      Continuous (Function.uncurry (fun u : X ↦ A a0 b0 u.1 u.2)) := by
    have hc : Continuous (fun q : RefinedIndex J × (Euclidean (n-1) × Euclidean n) ↦
        A a0 b0 q.1 q.2.1 q.2.2) :=
      continuous_prod_of_discrete_left.mpr (fun i ↦ (hA a0 b0 i).continuous)
    exact hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hInt (a0 : Fin N) (b0 : Fin n) (x : Euclidean n) :
      Integrable (fun u : X ↦ physicalForwardKernel φ mHalf (fun u ↦ A a0 b0 u.1 u.2) x u*v u) μ := by
    apply ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel.integrable_compactKernel_mul_L2
    · exact continuous_sampledMomentKernel φ mHalf (fun u y ↦ star (A a0 b0 u.1 u.2 y)) hφ hmHalf (hAc a0 b0).star
    · apply hasCompactSupport_sampledMomentKernel φ mHalf (fun u y ↦ star (A a0 b0 u.1 u.2 y)) hmHalfS hK
      intro u
      apply closure_minimal _ hK.isClosed
      intro x hx
      exact hAK a0 b0 u.1 u.2 (subset_tsupport _ (fun hz ↦ hx (by simp only [hz,star_zero])))
  have hBe (a0 : Fin N) (b0 : Fin n) : (fun x ↦ B x a0 b0) =
      fun x ↦ ∫ u, physicalForwardKernel φ mHalf (fun u ↦ A a0 b0 u.1 u.2) x u*v u ∂μ := by
    funext x
    exact matrix_integral_apply _ (fun a0 b0 ↦ hInt a0 b0 x) a0 b0
  have hscalar (a0 : Fin N) (b0 : Fin n) := singleForward_physical_halfMoment_bounds
    φ Φ (A a0 b0) mBare hφ hΦ (hA a0 b0) hm hms hhigh
    hK (hAK a0 b0) hagree χ hχ hχs hχK Rbox hbox hT a p ha hp
    (hAj a0 b0) hΦj Tbare hTbare v
  have hBsmooth : ContDiff ℝ ∞ B := by
    let e : Matrix (Fin N) (Fin n) ℂ ≃L[ℂ] (Fin N × Fin n → ℂ) := matrixEntryEquiv
    have hc : ContDiff ℝ ∞ (fun (x : Euclidean n) (ab : Fin N × Fin n) ↦ B x ab.1 ab.2) :=
      contDiff_pi.mpr (fun ab ↦ by rw [hBe ab.1 ab.2]; exact (hscalar ab.1 ab.2).1)
    exact (e.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hc
  have hBK : tsupport B ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    apply hx
    ext a0 b0
    change (fun y ↦ B y a0 b0) x = 0
    rw [hBe a0 b0]
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ ∫ u, physicalForwardKernel φ mHalf (fun u ↦ A a0 b0 u.1 u.2) y u*v u ∂μ)
      (fun hh ↦ hxK ((hscalar a0 b0).2.1 hh))
  let W := ∑ k ∈ Finset.range (s+1), T^(s-k-s0)*
    (eLpNorm (fun u : X ↦ ((‖u.2‖^((k : ℝ)+1/2) : ℝ) : ℂ)*v u) 2 μ).toReal
  let M := D*‖Tbare‖*W
  have hcoords : ∀ ds : List (Fin n), ds.length ≤ s → ∀ a0 b0,
      MemLp (euclideanCoordinateDerivList ds (fun x ↦ B x a0 b0)) 2 volume ∧
      lpNorm (euclideanCoordinateDerivList ds (fun x ↦ B x a0 b0)) 2 volume ≤ M := by
    intro ds hds a0 b0
    rw [hBe a0 b0]
    refine ⟨(hscalar a0 b0).2.2.1 ds,?_⟩
    have hb := (hscalar a0 b0).2.2.2 ds
    simp only [toReal_eLpNorm] at hb
    apply hb.trans
    have hDj : forwardDerivativeConstant n Rbox a p ds.length ≤ D :=
      Finset.single_le_sum (fun j _ ↦ forwardDerivativeConstant_nonneg n Rbox a p j ha hp)
        (Finset.mem_range.mpr (by omega))
    have hWeights : (∑ k ∈ Finset.range (ds.length+1), T^(ds.length-k-s0)*
        (eLpNorm (fun u : X ↦ ((‖u.2‖^((k : ℝ)+1/2) : ℝ) : ℂ)*v u) 2 μ).toReal) ≤ W := by
      apply (Finset.sum_le_sum (fun k _ ↦ mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT (show ds.length-k-s0 ≤ s-k-s0 by omega)) ENNReal.toReal_nonneg)).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) ENNReal.toReal_nonneg)
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hDj (norm_nonneg _)) hWeights
      (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) ENNReal.toReal_nonneg)
      (mul_nonneg hD (norm_nonneg _))
  obtain ⟨hmem,hbound⟩ := htransfer B hBsmooth
    (hK.of_isClosed_subset (isClosed_tsupport B) hBK) M hcoords
  refine ⟨hBsmooth,hBK,hmem,?_⟩
  exact hbound.trans_eq (by dsimp [M,W]; ring)

end JanetCartan.PhysicalForwardMean
