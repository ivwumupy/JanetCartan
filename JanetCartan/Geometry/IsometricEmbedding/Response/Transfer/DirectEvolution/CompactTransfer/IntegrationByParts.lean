module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.SupportedCalculus

/-!
# Joint integration by parts for the actual transfer field

The compact-frequency identity `paper-v2.tex`, `new:eq:carrier-ibp`, with the
integration direction obtained from `DirectEvolution.transferCoefficient`.
The coefficients have no frequency factor. The consumer is the ordered
amplitude transfer for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

variable {n : ℕ} {E F ι : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [Fintype ι]

/-- Divergence of the full coefficient-amplitude product, differentiating
every mask and coefficient in `new:eq:carrier-ibp`. An orthonormal basis is
explicit so that the eventual source/covector splitting retains its directions. -/
def weightedDivergence (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (A : CarrierVariables n → CarrierVariables n) (g : CarrierVariables n → F)
    (w : CarrierVariables n) : F :=
  ∑ i, fderiv ℝ (fun z ↦ inner ℝ (b i) (A z) • g z) w (b i)

omit [CompleteSpace F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- Divergence retains the original compact support, including at every mask
boundary (`new:eq:carrier-ibp`). -/
theorem support_weightedDivergence_subset
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (A : CarrierVariables n → CarrierVariables n)
    {K : Set (CarrierVariables n)} (hK : IsClosed K)
    {g : CarrierVariables n → F} (hs : Function.support g ⊆ K) :
    Function.support (weightedDivergence b A g) ⊆ K := by
  intro w hw
  by_contra hn
  apply hw
  apply Finset.sum_eq_zero
  intro i _
  have hs' : tsupport (fun z ↦ inner ℝ (b i) (A z) • g z) ⊆ K :=
    closure_minimal ((Function.support_smul_subset_right _ _).trans hs) hK
  have ht := (tsupport_fderiv_apply_subset ℝ (b i)).trans hs'
  exact Function.notMem_support.mp (fun h ↦ hn (ht (subset_tsupport _ h)))

omit [CompleteSpace F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- The full divergence amplitude is smooth on the same domain. No enlargement
of the supported geometry is required in `new:eq:carrier-ibp`. -/
theorem contDiffOn_weightedDivergence
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {D : Set (CarrierVariables n)} (hD : IsOpen D)
    {A : CarrierVariables n → CarrierVariables n} {g : CarrierVariables n → F}
    (hA : ContDiffOn ℝ ∞ A D) (hg : ContDiffOn ℝ ∞ g D) :
    ContDiffOn ℝ ∞ (weightedDivergence b A g) D := by
  apply ContDiffOn.sum
  intro i _
  exact (((contDiffOn_const.inner ℝ hA).smul hg).fderiv_of_isOpen hD
    (by simp)).clm_apply contDiffOn_const

omit [CompleteSpace F] in
/-- The compact supported vector-field integration-by-parts identity. All
integrability comes from the same box, and the direction field is differentiated
inside the divergence. This is the integration step of `new:eq:carrier-ibp`. -/
theorem integral_fderiv_vectorField_smul
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {D K : Set (CarrierVariables n)} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) {Ω : CarrierVariables n → ℂ} {g : CarrierVariables n → F}
    {A : CarrierVariables n → CarrierVariables n}
    (hΩ : ContDiffOn ℝ ∞ Ω D) (hg : ContDiffOn ℝ ∞ g D)
    (hA : ContDiffOn ℝ ∞ A D) (hs : Function.support g ⊆ K) :
    (∫ w, fderiv ℝ Ω w (A w) • g w) =
      -(∫ w, Ω w • weightedDivergence b A g w) := by
  let G : ι → CarrierVariables n → F := fun i w ↦ inner ℝ (b i) (A w) • g w
  have hG (i) : ContDiffOn ℝ ∞ (G i) D := (contDiffOn_const.inner ℝ hA).smul hg
  have hsG (i) : Function.support (G i) ⊆ K :=
    (Function.support_smul_subset_right _ _).trans hs
  have hG' (i) := contDiff_of_support_subset hD hK.isClosed hKD (hG i) (hsG i)
  have hsDG (i) : Function.support (fun w ↦ fderiv ℝ (G i) w (b i)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (b i)).trans
      (closure_minimal (hsG i) hK.isClosed))
  have hi₁ (i) : Integrable (fun w ↦ fderiv ℝ Ω w (b i) • G i w) :=
    integrable_of_support_subset hD hK hKD
      (((hΩ.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const).smul (hG i))
      ((Function.support_smul_subset_right _ _).trans (hsG i))
  have hi₂ (i) : Integrable (fun w ↦ Ω w • fderiv ℝ (G i) w (b i)) :=
    integrable_of_support_subset hD hK hKD
      (hΩ.smul (((hG' i).fderiv_right (by simp)).clm_apply contDiff_const).contDiffOn)
      ((Function.support_smul_subset_right _ _).trans (hsDG i))
  calc
    _ = ∫ w, ∑ i, fderiv ℝ Ω w (b i) • G i w := by
      apply integral_congr_ae
      filter_upwards [] with w
      nth_rw 1 [← b.sum_repr' (A w)]
      simp only [map_sum, map_smul, Finset.sum_smul, G]
      apply Finset.sum_congr rfl
      intro i _
      exact smul_assoc _ _ _ |>.trans (smul_comm _ _ _)
    _ = ∑ i, ∫ w, fderiv ℝ Ω w (b i) • G i w :=
      integral_finsetSum _ (fun i _ ↦ hi₁ i)
    _ = ∑ i, -(∫ w, Ω w • fderiv ℝ (G i) w (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_fderiv_smul_eq_neg hD hK hKD hΩ (hG i) (hsG i) (b i)
    _ = -(∫ w, Ω w • weightedDivergence b A g w) := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hi₂ i)]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [weightedDivergence, Finset.smul_sum, G]

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
