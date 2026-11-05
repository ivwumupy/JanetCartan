module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AdjointAmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedAnnularGeometry

/-!
# Retained physical amplitude profiles on the larger source space

The normalized physical amplitudes of both orientations are independent of
the entire external parameter. The projection here applies only to those
amplitudes. It lets the retained annular jet and support producers act on the
same physical matrices and the same integration carrier. Neither the source
phase nor the datum is pulled back by this projection.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open DirectEvolution AnnularSobolev RetainedFactors Pseudodifferential
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CW" => CarrierVariables (d+1)
local notation "Par" => Euclidean 3 × Euclidean d

/-- Either literal normalized annular amplitude of
`app:ch_response:eq:direct-envelope-profile`, with its given parameter type. -/
abbrev orientedAnnularAmplitude (P : Type) (adj : Bool) (W : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (t lam : ℝ) (order : ℤ) :=
  if adj then normalizedAdjointAnnularElapsedAmplitude (P := P) W χout χsource β π t lam order
  else normalizedAnnularElapsedAmplitude (P := P) W χout χsource β π t lam order

/-- Smoothness used on both sides of the full-source substitution in
`app:ch_response:eq:fixed-factor-transfer`. The reverse matrix is the literal
conjugate transpose at the two exchanged physical positions. -/
theorem contDiff_orientedAnnularAmplitude (p : ℕ) (adj : Bool) (W : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hπ : ContDiff ℝ ∞ π) (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (o : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (orientedAnnularAmplitude (Euclidean p) adj W
      χout χsource β π t lam (-(o : ℤ)))) := by
  have hf := contDiff_normalizedAnnularElapsedAmplitude (p := p) W χout χsource β π
    hW ho hs hβ hπ t hlam o
  cases adj
  · exact hf
  · let J : Matrix (Fin r) (Fin r) ℂ ≃ₗᵢ[ℝ] Matrix (Fin r) (Fin r) ℂ := {
      Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ with
      norm_map' := Matrix.frobenius_norm_conjTranspose }
    convert J.contDiff.comp (hf.comp annularCarrierSwap.contDiff) using 1
    funext v
    change _ = ((lam ^ (-(o : ℤ)))⁻¹ • annularElapsedAmplitude W χout χsource β π t lam
      v.2.fst v.1.1 (lam • v.2.snd)).conjTranspose
    simp only [Function.uncurry, orientedAnnularAmplitude, ↓reduceIte,
      normalizedAdjointAnnularElapsedAmplitude, Matrix.conjTranspose_smul, star_trivial]

/-- Forgetting the inactive covector in the PHYSICAL amplitude is a contraction
and an open projection. Consequently the original annular jet bounds (from
`exists_admissible_history_retained_annular_jets` and its adjoint swap) and
the closed support from `exists_capped_annular_integration_carrier` transfer
with their original constants and the very same `Kcrit`, in both orientations
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSource_annularAmplitude_jets_support (adj : Bool) (W : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hπ : ContDiff ℝ ∞ π) (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (o : ℕ) :
    let α := fun P ↦ orientedAnnularAmplitude P adj W χout χsource β π t lam (-(o : ℤ))
    let proj := fun v : (E × Par) × CW ↦ ((v.1.1,v.1.2.1),v.2)
    (∀ j v, ‖iteratedFDeriv ℝ j (Function.uncurry (α Par)) v‖ ≤
      ‖iteratedFDeriv ℝ j (Function.uncurry (α (Euclidean 3))) (proj v)‖) ∧
    tsupport (Function.uncurry (α Par)) = proj ⁻¹' tsupport (Function.uncurry (α (Euclidean 3))) ∧
    ∀ q : E × Par, Function.support (α Par q) = Function.support (α (Euclidean 3) (q.1,q.2.1)) := by
  intro α proj
  let Pj := ((ContinuousLinearMap.id ℝ E).prodMap
    (ContinuousLinearMap.fst ℝ (Euclidean 3) (Euclidean d))).prodMap (ContinuousLinearMap.id ℝ CW)
  have hPj : ‖Pj‖ ≤ 1 := Pj.opNorm_le_bound zero_le_one (fun q ↦ by
    rw [one_mul]
    exact max_le_max (max_le_max le_rfl (norm_fst_le q.1.2)) le_rfl)
  have he : Function.uncurry (α Par) = Function.uncurry (α (Euclidean 3)) ∘ Pj := by
    cases adj <;> rfl
  have hopen : IsOpenMap proj := (IsOpenMap.id.prodMap isOpenMap_fst).prodMap IsOpenMap.id
  refine ⟨?_, ?_, ?_⟩
  · intro j v
    rw [he]
    apply (norm_iteratedFDeriv_comp_linear_le Pj _ (contDiff_orientedAnnularAmplitude 3 adj W
      χout χsource β π hW ho hs hβ hπ t hlam o) j v).trans
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hPj)
  · rw [he]
    exact (hopen.preimage_closure_eq_closure_preimage Pj.continuous (Function.support (Function.uncurry (α (Euclidean 3))))).symm
  · cases adj <;> intro q <;> rfl

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
