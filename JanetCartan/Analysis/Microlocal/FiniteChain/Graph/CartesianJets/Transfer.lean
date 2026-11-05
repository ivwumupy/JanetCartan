module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Leakage.CartesianBounds.Cutoff
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CompactKernels

/-!
# Physical derivatives and the actual Cartesian graph jets

The consumer is `KernelLimits.exists_jointKernel_physical_extension`, specifically
its `hb` hypothesis, for `app:ch_regular:eq:chain-tail`. The physical derivative
bounds are supplied by `jc-graph-factor-physical-shell-bridge`. This module proves
the coordinate, matrix-entry and fixed-cutoff implications independently of that
producer. It uses the existing Cartesian jets and the Frobenius matrix norm.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
open Set
namespace JanetCartan.FiniteChain.Graph.CartesianJets
open JanetCartan.RetardedSobolev JanetCartan.RetardedSobolev.Spaces
open Retarded.Leakage Retarded.KernelDecay AmplitudeBound FourierIntegral
variable {n r d m : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Transverse words are evaluated full differentials in pure transverse
vectors, with the order unchanged (`app:ch_regular:eq:chain-tail`). -/
theorem transverseJet_eq_evaluated_iteratedFDeriv {k : ℕ}
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (vs : Fin k → (Fin d → ℝ)) :
    transverseJet (List.ofFn vs) f =
      fun x => iteratedFDeriv ℝ k f x (fun a => (0, vs a)) := by
  induction k with
  | zero => simp [transverseJet]
  | succ k ih =>
    rw [List.ofFn_succ, transverseJet,
      transverseDeriv_eq_fderiv _ ((contDiff_transverseJet hf _).differentiable (by simp)), ih]
    funext x
    rw [((hf.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).differentiable
      (by simp) x).iteratedFDeriv_succ_apply_left']
    rfl

/-- Identification of the existing mixed time/transverse jet with evaluated
Fréchet derivatives. The input swap and both orders are literal, as required by
`KernelLimits.exists_jointKernel_physical_extension`
(`app:ch_regular:eq:chain-tail`). -/
theorem jet_eq_mixed_evaluated_iteratedFDeriv
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (i : JetIndex d m) (p : (Fin d → ℝ) × ℝ) :
    jet i f p = iteratedFDeriv ℝ i.2.2.val
      (fun x => iteratedFDeriv ℝ i.1.val f x
        (fun a => (0, Pi.single (i.2.1 a) 1))) (p.2, p.1) (fun _ => (1, 0)) := by
  rw [jet, timeJet, iteratedDeriv_eq_iteratedFDeriv,
    outputJet_apply_eq_jointJet (contDiff_transverseJet hf _),
    transverseJet_eq_evaluated_iteratedFDeriv hf]

/-- A fixed physical coordinate map inserts exactly one factor per derivative
vector (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_coordinates_apply
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {f : Euclidean n → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    (x : ℝ × (Fin d → ℝ)) (v : Fin k → ℝ × (Fin d → ℝ)) :
    iteratedFDeriv ℝ k (fun z => f (J z)) x v =
      iteratedFDeriv ℝ k f (J x) (fun a => J (v a)) := by
  change iteratedFDeriv ℝ k (f ∘ J.toContinuousLinearMap) x v = _
  rw [J.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by simp)]
  rfl

/-- The mixed jet in physical coordinates inserts `J (1,0)` for every time
slot and `J (0,e_a)` for every transverse slot. This identifies the literal
jet used by the graph extension (`app:ch_regular:eq:chain-tail`). -/
theorem jet_coordinates_eq_mixed_iteratedFDeriv
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {f : Euclidean n → ℂ} (hf : ContDiff ℝ ∞ f)
    (i : JetIndex d m) (p : (Fin d → ℝ) × ℝ) :
    jet i (fun x => f (J x)) p = iteratedFDeriv ℝ i.2.2.val
      (fun z => iteratedFDeriv ℝ i.1.val f z
        (fun a => J (0, Pi.single (i.2.1 a) 1)))
      (J (p.2, p.1)) (fun _ => J (1, 0)) := by
  rw [jet_eq_mixed_evaluated_iteratedFDeriv
    (f := fun x => f (J x)) (hf.comp J.contDiff) i p]
  simp_rw [iteratedFDeriv_coordinates_apply J hf]
  refine iteratedFDeriv_coordinates_apply J
    (f := fun z => iteratedFDeriv ℝ i.1.val f z
      (fun a => J (0, Pi.single (i.2.1 a) 1))) ?_ i.2.2.val (p.2, p.1) (fun _ => (1, 0))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i.1.val => Euclidean n) ℂ
    (fun a => J (0, Pi.single (i.2.1 a) 1))).contDiff.comp
      (hf.iteratedFDeriv_right (m := ∞) (by simp))

/-- Entry evaluation commutes with every physical output differential, for
the Frobenius matrix kernels of `app:ch_regular:eq:chain-tail`. -/
theorem iteratedFDeriv_matrixEntry_apply
    {K : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (hK : ContDiff ℝ ∞ K)
    (k : ℕ) (x : Euclidean n) (v : Fin k → Euclidean n) (a b : Fin r) :
    iteratedFDeriv ℝ k (fun z => K z a b) x v =
      (iteratedFDeriv ℝ k K x v) a b := by
  change iteratedFDeriv ℝ k (matrixEntryEvaluation a b ∘ K) x v = _
  rw [(matrixEntryEvaluation a b).iteratedFDeriv_comp_left hK.contDiffAt (by simp)]
  rfl

/-- Unit-direction estimates of a physical matrix kernel bound the full
scalar-entry differential with no matrix-size loss
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_matrixEntry_le
    {K : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (hK : ContDiff ℝ ∞ K)
    (k : ℕ) (x : Euclidean n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ v : Fin k → Euclidean n, (∀ j, ‖v j‖ ≤ 1) →
      ‖iteratedFDeriv ℝ k K x v‖ ≤ B) (a b : Fin r) :
    ‖iteratedFDeriv ℝ k (fun z => K z a b) x‖ ≤ B := by
  apply norm_multilinear_le_of_unit_directions _ hB
  intro v hv
  rw [iteratedFDeriv_matrixEntry_apply hK]
  exact (norm_matrixEntry_le_frobenius _ a b).trans (hb v hv)

/-- A smooth compact physical cutoff supplies its own fixed derivative
profile; no cutoff estimate is an analytic premise
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_cutoff_derivative_profile {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ) :
    ∃ H : ℕ → ℝ, (∀ j, 0 ≤ H j) ∧
      ∀ j x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ H j := by
  have hb j := (hsψ.iteratedFDeriv (𝕜 := ℝ) j).exists_bound_of_continuous
    ((hψ.iteratedFDeriv_right (m := ∞) (i := j) (by simp)).continuous)
  choose H hH using hb
  exact ⟨fun j => max 0 (H j), fun j => le_max_left _ _,
    fun j x => (hH j x).trans (le_max_right _ _)⟩

/-- Explicit finite cutoff and coordinate combination of the physical bounds.
It is independent of the matrix channel and the Cartesian jet index. Its
coefficients depend only on the fixed coordinates, cutoff and Sobolev order
(`app:ch_regular:eq:chain-tail`). -/
def jetMajorant (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (H B : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), derivativeConvolution H B k *
    (max 1 ‖J.toContinuousLinearMap‖) ^ k

/-- Positivity needs physical bounds only through the requested Sobolev order
(`app:ch_regular:eq:chain-tail`). -/
theorem jetMajorant_nonneg
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {H B : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hB : ∀ j ≤ m, 0 ≤ B j) :
    0 ≤ jetMajorant J H B m := by
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH j))
    (hB _ ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))

/-- Pointwise Leibniz estimate using only the physical derivatives through
order `k`. This is the fixed-cutoff step of `app:ch_regular:eq:chain-tail`. -/
theorem norm_cutoff_matrixEntry_iteratedFDeriv_le
    {ψ : Euclidean n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {K : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (hK : ContDiff ℝ ∞ K)
    {H B : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (k : ℕ) (x : Euclidean n)
    (hB : ∀ j ≤ k, 0 ≤ B j)
    (hc : ∀ j ≤ k, ‖iteratedFDeriv ℝ j ψ x‖ ≤ H j)
    (hb : ∀ j ≤ k, ∀ v : Fin j → Euclidean n, (∀ l, ‖v l‖ ≤ 1) →
      ‖iteratedFDeriv ℝ j K x v‖ ≤ B j) (a b : Fin r) :
    ‖iteratedFDeriv ℝ k (fun z => (ψ z : ℂ) * K z a b) x‖ ≤
      derivativeConvolution H B k := by
  apply (norm_iteratedFDeriv_mul_le (Complex.ofRealCLM.contDiff.comp hψ)
    ((matrixEntryEvaluation a b).contDiff.comp hK) x (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc' : ‖iteratedFDeriv ℝ j (fun z => (ψ z : ℂ)) x‖ ≤ H j := by
    change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ ψ) x‖ ≤ _
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hψ.contDiffAt (by simp)]
    exact hc j hjk
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg _))
    (norm_iteratedFDeriv_matrixEntry_le hK _ x (hB _ (Nat.sub_le _ _))
      (hb _ (Nat.sub_le _ _)) a b) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (hH j))

/-- Coordinate factors convert the actual mixed Cartesian jet to the physical
full derivative at exactly its total order (`app:ch_regular:eq:chain-tail`). -/
theorem norm_jet_coordinates_le
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {f : Euclidean n → ℂ} (hf : ContDiff ℝ ∞ f)
    (i : JetIndex d m) (p : (Fin d → ℝ) × ℝ) :
    ‖jet i (fun x => f (J x)) p‖ ≤
      ‖iteratedFDeriv ℝ (i.1.val + i.2.2.val) f (J (p.2, p.1))‖ *
        ‖J.toContinuousLinearMap‖ ^ (i.1.val + i.2.2.val) := by
  apply (norm_cartesianJet_le_iteratedFDeriv (hf.comp J.contDiff) i p).trans
  change ‖iteratedFDeriv ℝ (i.1.val + i.2.2.val) (f ∘ J.toContinuousLinearMap)
    (p.2, p.1)‖ ≤ _
  rw [J.toContinuousLinearMap.iteratedFDeriv_comp_right hf _ (by simp)]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ContinuousLinearEquiv.coe_coe] using
    (iteratedFDeriv ℝ (i.1.val + i.2.2.val) f _).norm_compContinuousLinearMap_le
      (fun _ => J.toContinuousLinearMap)

/-- Physical unit-direction bounds on the cutoff support imply every actual
Cartesian output jet, uniformly in the matrix channels and input base. Outside
the support the jet vanishes. This supplies `hb` in
`KernelLimits.exists_jointKernel_physical_extension`
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_cutMatrixEntry_jet_le
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {ψ : Euclidean n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {K : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hK : ContDiff ℝ ∞ (Function.uncurry K))
    {H B : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hB : ∀ j ≤ m, 0 ≤ B j)
    (hc : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ H j)
    (hb : ∀ x ∈ tsupport ψ, ∀ y, ∀ j ≤ m, ∀ v : Fin j → Euclidean n,
      (∀ l, ‖v l‖ ≤ 1) → ‖iteratedFDeriv ℝ j (fun z => K z y) x v‖ ≤ B j)
    (a b : Fin r) (i : JetIndex d m) (p y : (Fin d → ℝ) × ℝ) :
    ‖jet i (fun x => (ψ (J x) : ℂ) * K (J x) (J (y.2, y.1)) a b) p‖ ≤
      jetMajorant J H B m := by
  let f : Euclidean n → ℂ := fun z => (ψ z : ℂ) * K z (J (y.2, y.1)) a b
  have hcol : ContDiff ℝ ∞ (fun z => K z (J (y.2, y.1))) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  have hf : ContDiff ℝ ∞ f := (Complex.ofRealCLM.contDiff.comp hψ).mul
    ((matrixEntryEvaluation a b).contDiff.comp hcol)
  have hnon := jetMajorant_nonneg J hH hB
  change ‖jet i (f ∘ J) p‖ ≤ jetMajorant J H B m
  by_cases hx : J (p.2, p.1) ∈ tsupport ψ
  swap
  · rw [jet_eq_zero_off_tsupport i (hf.comp J.contDiff) p, norm_zero]
    · exact hnon
    · intro hp
      apply hx
      have hs : tsupport (fun x => f (J x)) ⊆ J ⁻¹' tsupport ψ := by
        apply closure_minimal _ ((isClosed_tsupport ψ).preimage J.continuous)
        intro x hx'
        by_contra hh
        exact hx' (by simp [f, image_eq_zero_of_notMem_tsupport hh])
      exact hs hp
  let k := i.1.val + i.2.2.val
  have hkm : k ≤ m := by dsimp [k]; have := i.1.isLt; have := i.2.2.isLt; omega
  have hcut : ‖iteratedFDeriv ℝ k f (J (p.2, p.1))‖ ≤ derivativeConvolution H B k :=
    norm_cutoff_matrixEntry_iteratedFDeriv_le hψ hcol hH k _
      (fun j hj => hB j (hj.trans hkm)) (fun j hj => hc j (hj.trans hkm) _)
      (fun j hj => hb _ hx _ j (hj.trans hkm)) a b
  have hconv : 0 ≤ derivativeConvolution H B k := (norm_nonneg _).trans hcut
  apply (norm_jet_coordinates_le J hf i p).trans
  calc
    _ ≤ derivativeConvolution H B k * (max 1 ‖J.toContinuousLinearMap‖) ^ k :=
      mul_le_mul hcut (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k)
        (pow_nonneg (norm_nonneg _) k) hconv
    _ ≤ jetMajorant J H B m := by
      unfold jetMajorant
      apply Finset.single_le_sum
        (f := fun l : ℕ => derivativeConvolution H B l * (max 1 ‖J.toContinuousLinearMap‖) ^ l)
        (s := Finset.range (m + 1)) (a := k)
      · intro l hl
        apply mul_nonneg _ (by positivity)
        apply Finset.sum_nonneg
        intro j _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH j))
          (hB _ ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hl))))
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hkm)

end JanetCartan.FiniteChain.Graph.CartesianJets
