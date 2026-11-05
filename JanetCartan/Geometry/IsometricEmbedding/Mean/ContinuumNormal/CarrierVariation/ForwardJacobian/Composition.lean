module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Fixed smooth operations on compact differential ranges

The finite-order Lipschitz estimate used for the absolute determinant and its
reciprocal in `app:ch_background:eq:bg-jacobian`, and in Step 4' of
`app:ch_osc:prop:osc-normal`. Compactness does not require a convex determinant
gap set. The constant uses fixed reference higher norms only.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation.ForwardJacobian
open HamiltonPhase.CompositionContinuity

/-- A fixed smooth operation is locally Lipschitz in finite mixed jets on a
fixed compact range. Consumer: the absolute transport determinant and its
reciprocal (`bg-jacobian`, `osc-normal`, Step 4'). -/
theorem exists_compact_comp_sub_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {S : Set F} (hK : IsCompact K) (hS : IsCompact S)
    {f : F → G} (hf : ∀ y ∈ S, ContDiffAt ℝ ∞ f y)
    {g₀ : E → F} (m : ℕ) (hg₀ : ∀ x ∈ K, ContDiffAt ℝ m g₀ x)
    (hrange₀ : MapsTo g₀ K S) :
    ∃ C > (0 : ℝ), ∀ g : E → F,
      (∀ x ∈ K, ContDiffAt ℝ m g x) → MapsTo g K S →
      cNorm K m (g - g₀) ≤ 1 →
      cNorm K m (f ∘ g - f ∘ g₀) ≤ C * cNorm K m (g - g₀) := by
  let J : F → (i : Fin (m + 1)) → F [×i.val]→L[ℝ] G :=
    fun y i ↦ iteratedFDeriv ℝ i.val f y
  have hJ : LocallyLipschitzOn S J := by
    intro y hy
    have hj : ContDiffAt ℝ 1 J y := contDiffAt_pi.mpr
      (fun i ↦ (hf y hy).iteratedFDeriv_right (by simp))
    obtain ⟨D, U, hU, hb⟩ := hj.exists_lipschitzOnWith
    exact ⟨D, U, mem_nhdsWithin_of_mem_nhds hU, hb⟩
  obtain ⟨D, hD⟩ := hJ.exists_lipschitzOnWith_of_compact hS
  let A := cNorm S m f
  let B := 1 + cNorm K m g₀
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  have hB : 0 ≤ B := by dsimp [B]; linarith [cNorm_nonneg K m g₀]
  let C := jetDifferenceConstant m A B
  have hC : 0 ≤ C := jetDifferenceConstant_nonneg m hA hB
  refine ⟨1 + C * (1 + D), by positivity, ?_⟩
  intro g hg hrange hsmall
  let ε := cNorm K m (g - g₀)
  have hε : 0 ≤ ε := cNorm_nonneg _ _ _
  have hdiff := fun i hi x hx ↦
    norm_iteratedFDeriv_sub_le_cNorm hK hg hg₀ (i := i) hi (x := x) hx
  have hbase := fun i hi x hx ↦
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg₀ (j := i) (x := x) hx hi
  have hval (x) (hx : x ∈ K) : ‖g₀ x - g x‖ ≤ ε := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun x hx ↦ (hg x hx).sub (hg₀ x hx)) hx (Nat.zero_le m)
    simpa only [ε, norm_iteratedFDeriv_zero, Pi.sub_def, norm_sub_rev] using hh
  have hb : cNorm K m (f ∘ g - f ∘ g₀) ≤ C * ((1 + D) * ε) := by
    apply cNorm_comp_sub_le_of_jet_bounds
      (fun x hx ↦ (hf _ (hrange hx)).of_le (by simp))
      (fun x hx ↦ (hf _ (hrange₀ hx)).of_le (by simp)) hg hg₀ hA hB (by positivity)
    · intro i hi x hx
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
        (fun y hy ↦ (hf y hy).of_le (by simp)) (hrange₀ hx) hi
    · intro i hi x hx
      refine ⟨(hbase i hi x hx).trans (by dsimp [B]; linarith), ?_⟩
      have ht := norm_le_norm_sub_add (iteratedFDeriv ℝ i g x) (iteratedFDeriv ℝ i g₀ x)
      have hd := hdiff i hi x hx
      have h₀ := hbase i hi x hx
      dsimp [B]
      linarith
    · intro i hi x hx
      have hh := (dist_le_pi_dist (J (g₀ x)) (J (g x)) ⟨i, Nat.lt_succ_of_le hi⟩).trans
        (hD.dist_le_mul (g₀ x) (hrange₀ hx) (g x) (hrange hx))
      simp only [J, dist_eq_norm] at hh
      exact hh.trans ((mul_le_mul_of_nonneg_left (hval x hx) D.coe_nonneg).trans
        (by nlinarith))
    · intro i hi x hx
      rw [norm_sub_rev]
      exact (hdiff i hi x hx).trans (by dsimp [ε]; nlinarith [D.coe_nonneg])
  exact hb.trans (by dsimp [ε] at *; nlinarith)

end JanetCartan.ContinuumNormal.CarrierVariation.ForwardJacobian
