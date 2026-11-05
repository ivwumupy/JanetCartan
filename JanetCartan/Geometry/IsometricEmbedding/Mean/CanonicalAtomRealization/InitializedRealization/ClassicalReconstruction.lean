module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.Expansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.CoefficientProducts
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Joint classical bounds for the literal ambient reconstruction

The reduced solver and complete strain envelopes are inserted in the actual
coordinate formula of `app:ch_response:eq:response-reconstruction-grading`.
Leibniz convolutions retain the sum of derivative orders. One carrier factor
is used for displacement and two for the physical derivative, giving the
quadratic and linear smallness in `app:ch_response:cor:current-atoms` from
the same cubic reduced envelopes.

The producer of the primitive coefficient profiles is `HistoryCoefficients`;
the source profile is retained by `CorrectedAtoms.InitializedTerminalSolver`.
The actual normalized inverse supplies the reduced solution profile. These
are profiles of those fields, without an independent ambient response.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CanonicalAtomRealization

open ResponseTransfer IsometricEmbedding.Reconstruction

private theorem localJet_product_le
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f g : D → ℂ} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f y * g y) x‖ ≤
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (m-j) g x‖ := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn' (m := (m : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨V, hV, hxV, hgV⟩ := hg.contDiffOn' (m := (m : ℕ∞ω)) (by simp) (by simp)
  simp only [insert_eq_of_mem (mem_univ x), univ_inter] at hfU hgV
  have h := norm_iteratedFDerivWithin_mul_le
    (hfU.mono (inter_subset_left (t := V))) (hgV.mono (inter_subset_right (s := U)))
    (hU.inter hV).uniqueDiffOn ⟨hxU, hxV⟩ (n := m) le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ (hU.inter hV) ⟨hxU,hxV⟩] using h

private theorem localJet_product_profile
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f g : D → ℂ} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (C B : ℕ → ℝ)
    (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K) (reserve m : ℕ)
    (hfB : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ C j * K^(j-reserve))
    (hgB : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ B j * A * K^(j-reserve)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f y * g y) x‖ ≤
      reconstructionProductBudget C B m * A * K^(m-reserve) := by
  apply (localJet_product_le hf hg m).trans
  simp only [reconstructionProductBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (m.choose j : ℝ) * (C j * K^(j-reserve)) *
        (B (m-j) * A * K^(m-j-reserve)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfB j hjm) (by positivity))
        (hgB (m-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (hC j)
          (pow_nonneg (zero_le_one.trans hK) _)))
    _ = ((m.choose j : ℝ) * C j * B (m-j)) * A *
        K^((j-reserve)+(m-j-reserve)) := by rw [pow_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hK (show (j-reserve)+(m-j-reserve) ≤ m-reserve by omega))
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hC j)) (hB _)) hA

private theorem localJet_sum_le
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] {f : ι → D → F} {x : D}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ ∑ i, f i y) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ m (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ (hf i).of_le (by simp))]
  exact norm_sum_le _ _

private theorem localJet_add_le
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : D → F} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by simp)) (hg.of_le (by simp))]
  exact norm_add_le _ _

/-- A physical derivative is the derivative of the same joint family in a
physical direction. This keeps the phase and reduced solution parameters fixed
in `app:ch_response:eq:response-reconstruction-grading`. -/
theorem physical_fderiv_eq_joint_fderiv
    {n : ℕ} {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n × Z → F} {p : Euclidean n × Z}
    (hf : DifferentiableAt ℝ f p) (v : Euclidean n) :
    fderiv ℝ (fun x ↦ f (x,p.2)) p.1 v = fderiv ℝ f p (v,0) := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have h := (hf.hasFDerivAt.comp p.1 hi).fderiv
  exact congrArg (fun T ↦ T v) h

/-- Joint smoothness supplies the physical derivative used by the actual
phase and response reconstruction (`app:ch_response:eq:response-reconstruction-grading`). -/
theorem contDiffOn_physical_fderiv_of_joint
    {n : ℕ} {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {f : Euclidean n × Z → F} (hf : ContDiffOn ℝ ∞ f Ω) (v : Euclidean n) :
    ContDiffOn ℝ ∞ (fun p ↦ fderiv ℝ (fun x ↦ f (x,p.2)) p.1 v) Ω := by
  apply ((hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const).congr
  intro p hp
  exact physical_fderiv_eq_joint_fderiv ((hf.contDiffAt (hΩ.mem_nhds hp)).differentiableAt
    (by simp)) v

/-- Differentiation in a unit physical direction costs one joint derivative
and no multiplicative loss. Applied to the same phase and reduced solution in
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem norm_iteratedFDeriv_physical_fderiv_le_joint
    {n : ℕ} {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {f : Euclidean n × Z → F} (hf : ContDiffOn ℝ ∞ f Ω)
    (v : Euclidean n) (hv : ‖v‖ ≤ 1) (m : ℕ)
    {p : Euclidean n × Z} (hp : p ∈ Ω) :
    ‖iteratedFDeriv ℝ m (fun q ↦ fderiv ℝ (fun x ↦ f (x,q.2)) q.1 v) p‖ ≤
      ‖iteratedFDeriv ℝ (m+1) f p‖ := by
  have he : (fun q ↦ fderiv ℝ (fun x ↦ f (x,q.2)) q.1 v) =ᶠ[𝓝 p]
      (fun q ↦ fderiv ℝ f q (v,0)) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact physical_fderiv_eq_joint_fderiv ((hf.contDiffAt (hΩ.mem_nhds hq)).differentiableAt
      (by simp)) v
  rw [(he.iteratedFDeriv ℝ m).eq_of_nhds]
  have hd := (hf.contDiffAt (hΩ.mem_nhds hp)).fderiv_right (m := ∞) (by simp)
  calc
    _ ≤ ‖(v,(0 : Z))‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ f) p‖ :=
      norm_iteratedFDeriv_clm_apply_const hd (by simp)
    _ ≤ ‖iteratedFDeriv ℝ m (fderiv ℝ f) p‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (by simpa using hv)
    _ = _ := norm_iteratedFDeriv_fderiv

private theorem localJet_const_mul
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : D → ℂ} {x : D} (hf : ContDiffAt ℝ ∞ f x) (m : ℕ) (c : ℂ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ c * f y) x‖ =
      ‖c‖ * ‖iteratedFDeriv ℝ m f x‖ := by
  change ‖iteratedFDeriv ℝ m (c • f) x‖ = _
  rw [iteratedFDeriv_const_smul_apply (hf.of_le (by simp)), norm_smul]

private theorem reconstruction_slow_derivative_le {A K ρ B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 1 ≤ K) (hKρ : K ≤ ρ)
    (reserve m : ℕ) :
    B * A * K^(m+1-reserve) ≤ B * (A*ρ) * K^(m-reserve) := by
  calc
    _ ≤ B * A * K^((m-reserve)+1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hK (show m+1-reserve ≤ (m-reserve)+1 by omega))
        (mul_nonneg hB hA)
    _ = B * A * K * K^(m-reserve) := by rw [pow_succ]; ring
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hKρ (mul_nonneg hB hA)
      exact (mul_le_mul_of_nonneg_right this
        (pow_nonneg (zero_le_one.trans hK) _)).trans_eq (by ring)

/-- The literal displacement sum has this finite Leibniz budget. The source
and carrier products have two primitive coefficients; the derivative of the
reduced solution costs one order (`app:ch_response:eq:response-graded-displacement`). -/
def jointReconstructionDisplacementBudget (n : ℕ) (C B : ℕ → ℝ) (r : ℕ) : ℝ :=
  (n : ℝ) * reconstructionProductBudget C B r +
    (n*n : ℕ) * (reconstructionProductBudget C (fun j ↦ B (j+1)) r +
      2 * reconstructionProductBudget (reconstructionProductBudget C C) B r)

/-- The displacement budget is nonnegative for the actual nonnegative
primitive profiles (`app:ch_response:eq:response-graded-displacement`). -/
theorem jointReconstructionDisplacementBudget_nonneg {C B : ℕ → ℝ}
    (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r) (n r : ℕ) :
    0 ≤ jointReconstructionDisplacementBudget n C B r := by
  unfold jointReconstructionDisplacementBudget
  exact add_nonneg
    (mul_nonneg (by positivity) (reconstructionProductBudget_nonneg hC hB r))
    (mul_nonneg (by positivity) (add_nonneg
      (reconstructionProductBudget_nonneg hC (fun j ↦ hB (j+1)) r)
      (mul_nonneg (by norm_num) (reconstructionProductBudget_nonneg
        (reconstructionProductBudget_nonneg hC hC) hB r))))

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Insert the actual full reduced source and solution in the coordinate
formula. The common derivative reserve is retained through every product,
and exactly one carrier factor is spent. The same coefficients are supplied
by `exists_admissible_history_reconstruction_entry_profiles`; the source and
solution profiles remain their respective producer applications
(`app:ch_response:eq:response-reconstruction-grading`). -/
theorem reconstructionAmplitude_joint_coordinate_graded
    (F : Euclidean n → Euclidean N)
    (φ : Euclidean n × Z → ℝ) (χ : Euclidean n → ℝ)
    (g : Euclidean n × Z → EuclideanSpace ℂ (Fin n))
    (a : Euclidean n × Z → Matrix (Fin n) (Fin n) ℂ)
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ ∞ g Ω)
    (ha : ∀ ij : Fin n × Fin n, ContDiffOn ℝ ∞ (fun q ↦ a q ij.1 ij.2) Ω)
    (hχ : ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦ (χ q.1 : ℂ)) Ω)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (fun q ↦
      ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)) Ω)
    (hV : ∀ l j, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionValueEntry F l j q.1) Ω)
    (hD : ∀ l ij, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionDerivativeEntry F l ij q.1) Ω)
    (hS : ∀ l ij, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionSourceEntry F l ij q.1) Ω)
    (C B : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {A K ρ : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K) (hKρ : K ≤ ρ)
    (reserve m : ℕ)
    (hχB : ∀ r ≤ m, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦ (χ p.1 : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hφB : ∀ i r, r ≤ m → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        ((partialDeriv (fun x ↦ φ (x,p.2)) p.1 i : ℝ) : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hVB : ∀ l j r, r ≤ m → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionValueEntry F l j p.1) q‖ ≤ C r * K^(r-reserve))
    (hDB : ∀ l ij r, r ≤ m → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionDerivativeEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hSB : ∀ l ij r, r ≤ m → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionSourceEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hgB : ∀ j r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ g p j) q‖ ≤ B r * A * K^(r-reserve))
    (haB : ∀ ij : Fin n × Fin n, ∀ r ≤ m, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ a p ij.1 ij.2) q‖ ≤ B r * A * K^(r-reserve)) :
    let R := fun (q : Euclidean n × Z) ↦ reconstructionAmplitude F ρ (fun x ↦ φ (x,q.2)) χ
      (fun x ↦ g (x,q.2)) (fun x ↦ a (x,q.2)) q.1
    ContDiffOn ℝ ∞ R Ω ∧
      ∀ l r, r ≤ m → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦ R p l) q‖ ≤
          jointReconstructionDisplacementBudget n C B r * (A*ρ) * K^(r-reserve) := by
  classical
  dsimp only
  let ξ := fun (i : Fin n) (q : Euclidean n × Z) ↦
    ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)
  let dg := fun (ij : Fin n × Fin n) (q : Euclidean n × Z) ↦
    partialDeriv (fun x ↦ g (x,q.2) ij.2) q.1 ij.1
  let tV := fun l (j : Fin n) (q : Euclidean n × Z) ↦
    reconstructionValueEntry F l j q.1 * g q j
  let tD := fun l (ij : Fin n × Fin n) (q : Euclidean n × Z) ↦
    reconstructionDerivativeEntry F l ij q.1 * dg ij q
  let tP := fun l (ij : Fin n × Fin n) (q : Euclidean n × Z) ↦
    (reconstructionDerivativeEntry F l ij q.1 * ξ ij.1 q) * g q ij.2
  let tS := fun l (ij : Fin n × Fin n) (q : Euclidean n × Z) ↦
    ((χ q.1 : ℂ) * reconstructionSourceEntry F l ij q.1) * a q ij.1 ij.2
  let Rl := fun l (q : Euclidean n × Z) ↦
    (∑ j, tV l j q) + (∑ ij, tD l ij q) +
      (Complex.I * (ρ : ℂ)) * (∑ ij, tP l ij q) + ∑ ij, tS l ij q
  have hg' (j : Fin n) : ContDiffOn ℝ ∞ (fun q ↦ g q j) Ω :=
    (contDiffOn_piLp 2).mp hg j
  have hdg (ij : Fin n × Fin n) : ContDiffOn ℝ ∞ (dg ij) Ω :=
    contDiffOn_physical_fderiv_of_joint hΩ (hg' ij.2) (EuclideanSpace.single ij.1 1)
  have htV l j : ContDiffOn ℝ ∞ (tV l j) Ω := (hV l j).mul (hg' j)
  have htD l ij : ContDiffOn ℝ ∞ (tD l ij) Ω := (hD l ij).mul (hdg ij)
  have htP l ij : ContDiffOn ℝ ∞ (tP l ij) Ω := ((hD l ij).mul (hφ ij.1)).mul (hg' ij.2)
  have htS l ij : ContDiffOn ℝ ∞ (tS l ij) Ω := (hχ.mul (hS l ij)).mul (ha ij)
  have hRl l : ContDiffOn ℝ ∞ (Rl l) Ω :=
    (((ContDiffOn.sum (fun j _ ↦ htV l j)).add (ContDiffOn.sum (fun ij _ ↦ htD l ij))).add
      (contDiffOn_const.mul (ContDiffOn.sum (fun ij _ ↦ htP l ij)))).add
      (ContDiffOn.sum (fun ij _ ↦ htS l ij))
  have he (l : Fin N) :
      (fun q ↦ reconstructionAmplitude F ρ (fun x ↦ φ (x,q.2)) χ
        (fun x ↦ g (x,q.2)) (fun x ↦ a (x,q.2)) q.1 l) = Rl l := by
    funext q
    rcases q with ⟨x,c⟩
    rw [reconstructionAmplitude_coordinate]
    simp only [Rl, tV, tD, tP, tS, dg, ξ, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    simp only [mul_assoc, mul_left_comm, mul_comm]
    abel
  refine ⟨(contDiffOn_piLp 2).mpr (fun l ↦ by rw [he]; exact hRl l), ?_⟩
  intro l r hr q hq
  have hρ : 1 ≤ ρ := hK.trans hKρ
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hqΩ := hΩ.mem_nhds hq
  have hCC := reconstructionProductBudget_nonneg hC hC
  have htVB (j : Fin n) : ‖iteratedFDeriv ℝ r (tV l j) q‖ ≤
      reconstructionProductBudget C B r * (A*ρ) * K^(r-reserve) := by
    have h := localJet_product_profile ((hV l j).contDiffAt hqΩ) ((hg' j).contDiffAt hqΩ)
      C B hC hB hA hK reserve r
      (fun i hi ↦ hVB l j i (hi.trans hr) q hq)
      (fun i hi ↦ hgB j i (by omega) q hq)
    apply h.trans
    have hz := mul_nonneg (reconstructionProductBudget_nonneg hC hB r) hA
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hz hρ)
      (pow_nonneg hK0 _)).trans_eq (by ring)
  have hdgB (ij : Fin n × Fin n) (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i (dg ij) q‖ ≤ B (i+1) * (A*ρ) * K^(i-reserve) := by
    have h := norm_iteratedFDeriv_physical_fderiv_le_joint hΩ (hg' ij.2)
      (EuclideanSpace.single ij.1 1) (by simp) i hq
    exact h.trans ((hgB ij.2 (i+1) (by omega) q hq).trans
      (reconstruction_slow_derivative_le hA (hB _) hK hKρ reserve i))
  have htDB (ij : Fin n × Fin n) : ‖iteratedFDeriv ℝ r (tD l ij) q‖ ≤
      reconstructionProductBudget C (fun i ↦ B (i+1)) r * (A*ρ) * K^(r-reserve) :=
    localJet_product_profile ((hD l ij).contDiffAt hqΩ) ((hdg ij).contDiffAt hqΩ)
      C (fun i ↦ B (i+1)) hC (fun i ↦ hB (i+1)) (mul_nonneg hA hρ0) hK reserve r
      (fun i hi ↦ hDB l ij i (hi.trans hr) q hq) (hdgB ij)
  have hDP (ij : Fin n × Fin n) (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i (fun p : Euclidean n × Z ↦
        reconstructionDerivativeEntry F l ij p.1 * ξ ij.1 p) q‖ ≤
        reconstructionProductBudget C C i * K^(i-reserve) := by
    simpa only [mul_one] using localJet_product_profile ((hD l ij).contDiffAt hqΩ)
      ((hφ ij.1).contDiffAt hqΩ) C C hC hC zero_le_one hK reserve i
      (fun k hk ↦ hDB l ij k (by omega) q hq)
      (fun k hk ↦ by simpa only [mul_one] using hφB ij.1 k (by omega) q hq)
  have htPB (ij : Fin n × Fin n) : ‖iteratedFDeriv ℝ r (tP l ij) q‖ ≤
      reconstructionProductBudget (reconstructionProductBudget C C) B r * A * K^(r-reserve) :=
    localJet_product_profile (((hD l ij).mul (hφ ij.1)).contDiffAt hqΩ)
      ((hg' ij.2).contDiffAt hqΩ) (reconstructionProductBudget C C) B hCC hB hA hK
      reserve r (hDP ij) (fun i hi ↦ hgB ij.2 i (by omega) q hq)
  have hCS (ij : Fin n × Fin n) (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i (fun p : Euclidean n × Z ↦
        (χ p.1 : ℂ) * reconstructionSourceEntry F l ij p.1) q‖ ≤
        reconstructionProductBudget C C i * K^(i-reserve) := by
    simpa only [mul_one] using localJet_product_profile (hχ.contDiffAt hqΩ)
      ((hS l ij).contDiffAt hqΩ) C C hC hC zero_le_one hK reserve i
      (fun k hk ↦ hχB k (by omega) q hq)
      (fun k hk ↦ by simpa only [mul_one] using hSB l ij k (by omega) q hq)
  have htSB (ij : Fin n × Fin n) : ‖iteratedFDeriv ℝ r (tS l ij) q‖ ≤
      reconstructionProductBudget (reconstructionProductBudget C C) B r * (A*ρ) *
        K^(r-reserve) := by
    have h := localJet_product_profile ((hχ.mul (hS l ij)).contDiffAt hqΩ)
      ((ha ij).contDiffAt hqΩ) (reconstructionProductBudget C C) B hCC hB hA hK
      reserve r (hCS ij) (fun i hi ↦ haB ij i (hi.trans hr) q hq)
    apply h.trans
    have hz := mul_nonneg (reconstructionProductBudget_nonneg hCC hB r) hA
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hz hρ)
      (pow_nonneg hK0 _)).trans_eq (by ring)
  have hsumV : ‖iteratedFDeriv ℝ r (fun p ↦ ∑ j, tV l j p) q‖ ≤
      (n : ℝ) * (reconstructionProductBudget C B r * (A*ρ) * K^(r-reserve)) := by
    exact (localJet_sum_le (fun j ↦ (htV l j).contDiffAt hqΩ) r).trans
      (by simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ htVB j))
  have hsumD : ‖iteratedFDeriv ℝ r (fun p ↦ ∑ ij, tD l ij p) q‖ ≤
      (n*n : ℕ) * (reconstructionProductBudget C (fun i ↦ B (i+1)) r *
        (A*ρ) * K^(r-reserve)) := by
    exact (localJet_sum_le (fun ij ↦ (htD l ij).contDiffAt hqΩ) r).trans
      (by simpa [Fintype.card_prod] using
        (Finset.sum_le_sum (fun ij (_ : ij ∈ Finset.univ) ↦ htDB ij)))
  have hsumP : ‖iteratedFDeriv ℝ r
      (fun p ↦ (Complex.I * (ρ : ℂ)) * (∑ ij, tP l ij p)) q‖ ≤
      (n*n : ℕ) * (reconstructionProductBudget (reconstructionProductBudget C C) B r *
        (A*ρ) * K^(r-reserve)) := by
    rw [localJet_const_mul ((ContDiffOn.sum (fun ij _ ↦ htP l ij)).contDiffAt hqΩ),
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0]
    have hb := (localJet_sum_le (fun ij ↦ (htP l ij).contDiffAt hqΩ) r).trans
      (Finset.sum_le_sum (fun ij (_ : ij ∈ Finset.univ) ↦ htPB ij))
    have hb' := mul_le_mul_of_nonneg_left hb hρ0
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul] at hb'
    exact hb'.trans_eq (by ring)
  have hsumS : ‖iteratedFDeriv ℝ r (fun p ↦ ∑ ij, tS l ij p) q‖ ≤
      (n*n : ℕ) * (reconstructionProductBudget (reconstructionProductBudget C C) B r *
        (A*ρ) * K^(r-reserve)) := by
    exact (localJet_sum_le (fun ij ↦ (htS l ij).contDiffAt hqΩ) r).trans
      (by simpa [Fintype.card_prod] using
        (Finset.sum_le_sum (fun ij (_ : ij ∈ Finset.univ) ↦ htSB ij)))
  have hsV : ContDiffAt ℝ ∞ (fun p ↦ ∑ j, tV l j p) q :=
    (ContDiffOn.sum (fun j _ ↦ htV l j)).contDiffAt hqΩ
  have hsD : ContDiffAt ℝ ∞ (fun p ↦ ∑ ij, tD l ij p) q :=
    (ContDiffOn.sum (fun ij _ ↦ htD l ij)).contDiffAt hqΩ
  have hsP : ContDiffAt ℝ ∞ (fun p ↦ (Complex.I * (ρ : ℂ)) * ∑ ij, tP l ij p) q :=
    ((contDiffOn_const (c := Complex.I * (ρ : ℂ))).mul
    (ContDiffOn.sum (fun ij _ ↦ htP l ij))).contDiffAt hqΩ
  have hsS : ContDiffAt ℝ ∞ (fun p ↦ ∑ ij, tS l ij p) q :=
    (ContDiffOn.sum (fun ij _ ↦ htS l ij)).contDiffAt hqΩ
  rw [he]
  change ‖iteratedFDeriv ℝ r (fun p ↦
    ((∑ j, tV l j p) + (∑ ij, tD l ij p) +
      (Complex.I * (ρ : ℂ)) * (∑ ij, tP l ij p)) + ∑ ij, tS l ij p) q‖ ≤ _
  apply (localJet_add_le ((hsV.add hsD).add hsP) hsS r).trans
  apply (add_le_add ((localJet_add_le (hsV.add hsD) hsP r).trans
    (add_le_add (localJet_add_le hsV hsD r) le_rfl)) le_rfl).trans
  apply (add_le_add (add_le_add (add_le_add hsumV hsumD) hsumP) hsumS).trans_eq
  unfold jointReconstructionDisplacementBudget
  ring

/-- The physical derivative has the phase-times-displacement product and one
ordinary envelope derivative. This is the exact second carrier factor in
`app:ch_response:eq:response-graded-derivative`. -/
def jointReconstructionPhysicalBudget (n : ℕ) (C B : ℕ → ℝ) (r : ℕ) : ℝ :=
  reconstructionProductBudget C (jointReconstructionDisplacementBudget n C B) r +
    jointReconstructionDisplacementBudget n C B (r+1)

/-- Nonnegativity of the physical derivative budget in
`app:ch_response:eq:response-graded-derivative`. -/
theorem jointReconstructionPhysicalBudget_nonneg {C B : ℕ → ℝ}
    (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r) (n r : ℕ) :
    0 ≤ jointReconstructionPhysicalBudget n C B r :=
  add_nonneg (reconstructionProductBudget_nonneg hC
    (jointReconstructionDisplacementBudget_nonneg hC hB n) r)
    (jointReconstructionDisplacementBudget_nonneg hC hB n (r+1))

private theorem reconstruction_physical_coordinate_of_displacement
    (F : Euclidean n → Euclidean N)
    (φ : Euclidean n × Z → ℝ) (χ : Euclidean n → ℝ)
    (g : Euclidean n × Z → EuclideanSpace ℂ (Fin n))
    (a : Euclidean n × Z → Matrix (Fin n) (Fin n) ℂ)
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    (hφsp : ∀ q ∈ Ω, Differentiable ℝ (fun x ↦ φ (x,q.2)))
    (hgsp : ∀ q ∈ Ω, Differentiable ℝ (fun x ↦ g (x,q.2)))
    (hφ : ∀ i, ContDiffOn ℝ ∞ (fun q ↦
      ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)) Ω)
    (C D : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hD : ∀ r, 0 ≤ D r)
    {A K ρ : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K) (hKρ : K ≤ ρ)
    (reserve m : ℕ)
    (hφB : ∀ i r, r ≤ m → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        ((partialDeriv (fun x ↦ φ (x,p.2)) p.1 i : ℝ) : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hR : ContDiffOn ℝ ∞ (fun q ↦ reconstructionAmplitude F ρ (fun x ↦ φ (x,q.2)) χ
      (fun x ↦ g (x,q.2)) (fun x ↦ a (x,q.2)) q.1) Ω)
    (hRB : ∀ l r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        reconstructionAmplitude F ρ (fun x ↦ φ (x,p.2)) χ
          (fun x ↦ g (x,p.2)) (fun x ↦ a (x,p.2)) p.1 l) q‖ ≤
        D r * (A*ρ) * K^(r-reserve)) :
    let V := fun (q : Euclidean n × Z) ↦ completedVariationComplex F
      (modulatedWave ρ (fun x ↦ φ (x,q.2)) (fun x ↦ g (x,q.2)))
      (fun x ↦ waveCarrier ρ (fun y ↦ φ (y,q.2)) x • ((χ x : ℂ) • a (x,q.2))) q.1
    let H := fun (l : Fin N) (i : Fin n) (q : Euclidean n × Z) ↦ (waveCarrier (-ρ) (fun x ↦ φ (x,q.2)) q.1 •
      fderiv ℝ (fun x ↦ V (x,q.2)) q.1 (EuclideanSpace.single i 1)) l
    (∀ l i, ContDiffOn ℝ ∞ (H l i) Ω) ∧
      ∀ l i r, r ≤ m → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (H l i) q‖ ≤
          (reconstructionProductBudget C D r + D (r+1)) * (A*ρ^2) * K^(r-reserve) := by
  classical
  dsimp only
  let R := fun (q : Euclidean n × Z) ↦ reconstructionAmplitude F ρ (fun x ↦ φ (x,q.2)) χ
    (fun x ↦ g (x,q.2)) (fun x ↦ a (x,q.2)) q.1
  let ξ := fun i (q : Euclidean n × Z) ↦
    ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)
  let dR := fun l i (q : Euclidean n × Z) ↦
    partialDeriv (fun x ↦ R (x,q.2) l) q.1 i
  let H := fun l i (q : Euclidean n × Z) ↦
    (Complex.I * (ρ : ℂ)) * (ξ i q * R q l) + dR l i q
  have hRc l : ContDiffOn ℝ ∞ (fun q ↦ R q l) Ω := (contDiffOn_piLp 2).mp hR l
  have hdR l i : ContDiffOn ℝ ∞ (dR l i) Ω :=
    contDiffOn_physical_fderiv_of_joint hΩ (hRc l) (EuclideanSpace.single i 1)
  have hH l i : ContDiffOn ℝ ∞ (H l i) Ω :=
    (contDiffOn_const.mul ((hφ i).mul (hRc l))).add (hdR l i)
  have he l i (q : Euclidean n × Z) (hq : q ∈ Ω) :
      (waveCarrier (-ρ) (fun x ↦ φ (x,q.2)) q.1 •
        fderiv ℝ (completedVariationComplex F
          (modulatedWave ρ (fun x ↦ φ (x,q.2)) (fun x ↦ g (x,q.2)))
          (fun x ↦ waveCarrier ρ (fun y ↦ φ (y,q.2)) x • ((χ x : ℂ) • a (x,q.2))))
          q.1 (EuclideanSpace.single i 1)) l = H l i q := by
    have hRat : DifferentiableAt ℝ R q :=
      (hR.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)
    have hinc : DifferentiableAt ℝ (fun x : Euclidean n ↦ (x,q.2)) q.1 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have hRsp : DifferentiableAt ℝ (fun x ↦ R (x,q.2)) q.1 :=
      DifferentiableAt.comp (f := fun x : Euclidean n ↦ (x,q.2)) (g := R) q.1 hRat hinc
    have hproj : (fderiv ℝ (fun x ↦ R (x,q.2)) q.1 (EuclideanSpace.single i 1)) l =
        partialDeriv (fun x ↦ R (x,q.2) l) q.1 i := by
      exact (congrArg (fun T ↦ T (EuclideanSpace.single i 1))
        (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (R q) l).comp q.1 hRsp.hasFDerivAt).fderiv)).symm
    have h := congrArg (fun z : EuclideanSpace ℂ (Fin N) ↦ z l)
      (demodulated_physicalDerivative_completedVariationComplex F χ (fun _ ↦ 1)
        (fun x ↦ a (x,q.2)) (hφsp q hq) (hgsp q hq) q.1
        (EuclideanSpace.single i 1) hRsp)
    simp only [Complex.ofReal_one, one_smul, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul] at h
    change _ = (Complex.I * (ρ : ℂ) * ξ i q) * R q l +
      (fderiv ℝ (fun x ↦ R (x,q.2)) q.1 (EuclideanSpace.single i 1)) l at h
    rw [hproj] at h
    simpa only [H, dR, mul_assoc, PiLp.smul_apply, smul_eq_mul] using h
  refine ⟨fun l i ↦ (hH l i).congr (fun q hq ↦ he l i q hq), ?_⟩
  intro l i r hr q hq
  have hρ0 : 0 ≤ ρ := zero_le_one.trans (hK.trans hKρ)
  have hAρ : 0 ≤ A*ρ := mul_nonneg hA hρ0
  have hqΩ := hΩ.mem_nhds hq
  have heq : (fun p : Euclidean n × Z ↦
      (waveCarrier (-ρ) (fun x ↦ φ (x,p.2)) p.1 •
        fderiv ℝ (completedVariationComplex F
          (modulatedWave ρ (fun x ↦ φ (x,p.2)) (fun x ↦ g (x,p.2)))
          (fun x ↦ waveCarrier ρ (fun y ↦ φ (y,p.2)) x • ((χ x : ℂ) • a (x,p.2))))
          p.1 (EuclideanSpace.single i 1)) l) =ᶠ[𝓝 q] H l i :=
    Filter.eventually_of_mem hqΩ (fun p hp ↦ he l i p hp)
  rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
  have hp := localJet_product_profile ((hφ i).contDiffAt hqΩ) ((hRc l).contDiffAt hqΩ)
    C D hC hD hAρ hK reserve r
    (fun j hj ↦ hφB i j (hj.trans hr) q hq)
    (fun j hj ↦ hRB l j (by omega) q hq)
  have hpc : ‖iteratedFDeriv ℝ r
      (fun p ↦ (Complex.I * (ρ : ℂ)) * (ξ i p * R p l)) q‖ ≤
      reconstructionProductBudget C D r * (A*ρ^2) * K^(r-reserve) := by
    rw [localJet_const_mul (((hφ i).mul (hRc l)).contDiffAt hqΩ),
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0]
    exact (mul_le_mul_of_nonneg_left hp hρ0).trans_eq (by ring)
  have hd : ‖iteratedFDeriv ℝ r (dR l i) q‖ ≤ D (r+1) * (A*ρ^2) * K^(r-reserve) := by
    apply (norm_iteratedFDeriv_physical_fderiv_le_joint hΩ (hRc l)
      (EuclideanSpace.single i 1) (by simp) r hq).trans
    apply (hRB l (r+1) (by omega) q hq).trans
    exact (reconstruction_slow_derivative_le hAρ (hD _) hK hKρ reserve r).trans_eq
      (by ring)
  apply (localJet_add_le
    ((contDiffAt_const (c := Complex.I * (ρ : ℂ))).mul
      (((hφ i).mul (hRc l)).contDiffAt hqΩ)) ((hdR l i).contDiffAt hqΩ) r).trans
  exact (add_le_add hpc hd).trans_eq (by ring)

/-- The SAME literal completed variation has both joint response profiles.
The displacement and physical derivative use one and two carrier factors,
respectively. All constants are explicit functions of primitive profiles,
with a common arbitrary derivative reserve. Together with the ordered-parameter
Fourier conversion, the reduced solution needs only total order `m+n+3`.
This supplies the reconstruction part of
`app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`; the normalized inverse must
still supply its own reduced envelope. -/
theorem completedVariationComplex_joint_response_graded
    (F : Euclidean n → Euclidean N)
    (φ : Euclidean n × Z → ℝ) (χ : Euclidean n → ℝ)
    (g : Euclidean n × Z → EuclideanSpace ℂ (Fin n))
    (a : Euclidean n × Z → Matrix (Fin n) (Fin n) ℂ)
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    (hφjoint : ContDiffOn ℝ ∞ φ Ω)
    (hφsp : ∀ q ∈ Ω, Differentiable ℝ (fun x ↦ φ (x,q.2)))
    (hgsp : ∀ q ∈ Ω, Differentiable ℝ (fun x ↦ g (x,q.2)))
    (hg : ContDiffOn ℝ ∞ g Ω)
    (ha : ∀ ij : Fin n × Fin n, ContDiffOn ℝ ∞ (fun q ↦ a q ij.1 ij.2) Ω)
    (hχ : ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦ (χ q.1 : ℂ)) Ω)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (fun q ↦
      ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)) Ω)
    (hV : ∀ l j, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionValueEntry F l j q.1) Ω)
    (hD : ∀ l ij, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionDerivativeEntry F l ij q.1) Ω)
    (hS : ∀ l ij, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionSourceEntry F l ij q.1) Ω)
    (C B : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {A K ρ : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K) (hKρ : K ≤ ρ)
    (reserve m : ℕ)
    (hχB : ∀ r ≤ m+1, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦ (χ p.1 : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hφB : ∀ i r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        ((partialDeriv (fun x ↦ φ (x,p.2)) p.1 i : ℝ) : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hVB : ∀ l j r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionValueEntry F l j p.1) q‖ ≤ C r * K^(r-reserve))
    (hDB : ∀ l ij r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionDerivativeEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hSB : ∀ l ij r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionSourceEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hgB : ∀ j r, r ≤ m+2 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ g p j) q‖ ≤ B r * A * K^(r-reserve))
    (haB : ∀ ij : Fin n × Fin n, ∀ r ≤ m+1, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ a p ij.1 ij.2) q‖ ≤ B r * A * K^(r-reserve)) :
    let R := fun (q : Euclidean n × Z) ↦ reconstructionAmplitude F ρ (fun x ↦ φ (x,q.2)) χ
      (fun x ↦ g (x,q.2)) (fun x ↦ a (x,q.2)) q.1
    let V := fun (q : Euclidean n × Z) ↦ completedVariationComplex F
      (modulatedWave ρ (fun x ↦ φ (x,q.2)) (fun x ↦ g (x,q.2)))
      (fun x ↦ waveCarrier ρ (fun y ↦ φ (y,q.2)) x • ((χ x : ℂ) • a (x,q.2))) q.1
    let H := fun (l : Fin N) (i : Fin n) (q : Euclidean n × Z) ↦ (waveCarrier (-ρ) (fun x ↦ φ (x,q.2)) q.1 •
      fderiv ℝ (fun x ↦ V (x,q.2)) q.1 (EuclideanSpace.single i 1)) l
    ContDiffOn ℝ ∞ V Ω ∧ ContDiffOn ℝ ∞ R Ω ∧
      (∀ l r, r ≤ m+1 → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦ R p l) q‖ ≤
          jointReconstructionDisplacementBudget n C B r * (A*ρ) * K^(r-reserve)) ∧
      (∀ l i, ContDiffOn ℝ ∞ (H l i) Ω) ∧
      (∀ l i r, r ≤ m → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (H l i) q‖ ≤
          jointReconstructionPhysicalBudget n C B r * (A*ρ^2) * K^(r-reserve)) := by
  obtain ⟨hR,hRB⟩ := reconstructionAmplitude_joint_coordinate_graded F φ χ g a hΩ
    hg ha hχ hφ hV hD hS C B hC hB hA hK hKρ reserve (m+1)
    hχB hφB hVB hDB hSB (by simpa [Nat.add_assoc] using hgB) haB
  obtain ⟨hH,hHB⟩ := reconstruction_physical_coordinate_of_displacement F φ χ g a hΩ
    hφsp hgsp hφ C (jointReconstructionDisplacementBudget n C B) hC
    (jointReconstructionDisplacementBudget_nonneg hC hB n) hA hK hKρ reserve m
    (fun i r hr ↦ hφB i r (by omega)) hR hRB
  refine ⟨?_, hR, hRB, hH, hHB⟩
  have hc : ContDiffOn ℝ ∞ (fun q ↦ waveCarrier ρ (fun x ↦ φ (x,q.2)) q.1) Ω := by
    exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφjoint)).cexp
  apply (hc.smul hR).congr
  intro q hq
  exact completedVariationComplex_modulated F χ (fun x ↦ a (x,q.2))
    (hφsp q hq q.1) (hgsp q hq q.1)

end JanetCartan.CanonicalAtomRealization
