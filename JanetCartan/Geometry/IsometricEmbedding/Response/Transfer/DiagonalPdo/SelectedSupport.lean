module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.EllipticJointProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.Selector

/-!
# The actual selected elliptic support in the diagonal source box

Both physical masks and both shoulders of the original annular selector
give the compact integration support used by the forward and literal-adjoint
elliptic envelopes. The same compact works before coefficients, frequencies,
histories and the inverse/residual branch are chosen.

Sources: `app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open FourierIntegral NearCarrierFullLow
open DirectEvolution DirectEvolution.BranchAmplitudes DirectEvolution.AnnularComplement
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open ArbitraryAccuracy.ResidualLocalization
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d+1)
local notation "Joint" => (E × Par) × W
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The actual closed normalized support keeps the two physical masks in
their literal orientation and the entire original annular selector. This
supplies the support inputs of both diagonal Sobolev consumers without any
assumption on the selected symbol (`app:ch_response:eq:direct-envelope-profile`). -/
theorem tsupport_selected_diagonalAmplitude_subset
    (χout χsource : E → ℂ) (π : E → ℝ) (symbol : E → E → Mat)
    {lam : ℝ} (hlam : lam ≠ 0) (order : ℤ) (backward : Bool) :
    let A : FullAmplitude (d+1) r := fun x z ξ ↦
      (χout x * χsource z) • (π (lam⁻¹ • ξ) • symbol x ξ)
    let α := fun (q : E × Par) (w : W) ↦ (lam ^ order)⁻¹ •
      normalizedFullAmplitude (if backward then exchangedAdjointAmplitude A else A)
        lam (q.1,w.fst,w.snd)
    tsupport (Function.uncurry α) ⊆ {v : Joint |
      (if backward then v.2.fst else v.1.1) ∈ tsupport χout ∧
      (if backward then v.1.1 else v.2.fst) ∈ tsupport χsource ∧
      v.2.snd ∈ tsupport π} := by
  intro A α
  apply closure_minimal
  · intro v hv
    change α v.1 v.2 ≠ 0 at hv
    cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    all_goals
      refine ⟨subset_tsupport χout ?_, subset_tsupport χsource ?_, subset_tsupport π ?_⟩ <;>
        intro hz <;> exact hv (by simp [α, A, normalizedFullAmplitude,
          exchangedAdjointAmplitude, inv_smul_smul₀ hlam, hz])
  · cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ((isClosed_tsupport χout).preimage continuous_fst.fst).inter
        (((isClosed_tsupport χsource).preimage
          ((WithLp.continuous_fst 2 E E).comp continuous_snd)).inter
          ((isClosed_tsupport π).preimage
            ((WithLp.continuous_snd 2 E E).comp continuous_snd)))
    · exact ((isClosed_tsupport χout).preimage
        ((WithLp.continuous_fst 2 E E).comp continuous_snd)).inter
        (((isClosed_tsupport χsource).preimage continuous_fst.fst).inter
          ((isClosed_tsupport π).preimage
            ((WithLp.continuous_snd 2 E E).comp continuous_snd)))

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The SAME original selected physical masks and annular selector fit one
compact integration carrier inside the actual diagonal source box. The
forward and exchanged adjoint supports are both constructed, including every
normalized slice. The original upper selector shoulder is `2*b`; no new
mask or field is selected (`app:ch_response:eq:direct-envelope-profile`). -/
theorem selected_diagonalAmplitude_source_box_support
    (fam : ActualMaskFamily Ω x RQ A₀ K M)
    (χout : E → ℂ) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*fam.physicalRadius))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (Bsource : ℝ) :
    let χsource := fun z ↦ (fam.inputMask z : ℂ)
    let π := annularSelector (n := d+1) a b ha hb
    let X := tsupport χout ∪ tsupport χsource
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    let Kcrit := e ⁻¹' (X ×ˢ tsupport π)
    let D := e ⁻¹' (ball x (3*fam.physicalRadius) ×ˢ
      ball (0 : E) (1 + max Bsource (2*b)))
    IsCompact X ∧ X ⊆ ball x (3*fam.physicalRadius) ∧
      IsCompact Kcrit ∧ Kcrit ⊆ D ∧
      ∀ (symbol : E → E → Mat) (lam : ℝ), lam ≠ 0 →
      ∀ (order : ℤ) (backward : Bool),
      let A : FullAmplitude (d+1) r := fun y z ξ ↦
        (χout y * χsource z) • (π (lam⁻¹ • ξ) • symbol y ξ)
      let α := fun (q : E × Par) (w : W) ↦ (lam ^ order)⁻¹ •
        normalizedFullAmplitude (if backward then exchangedAdjointAmplitude A else A)
          lam (q.1,w.fst,w.snd)
      (∀ q, Function.support (α q) ⊆ Kcrit) ∧
      (∀ v ∈ tsupport (Function.uncurry α), v.1.1 ∈ X ∧ v.2 ∈ Kcrit) ∧
      ∀ (Cpar : Set Par) (c : Par), c ∈ Cpar → ∀ q,
        normalizedSlice c q ∈ tsupport (Function.uncurry α) →
        normalizedSlice c q ∈ (ball x (3*fam.physicalRadius) ×ˢ Cpar) ×ˢ D ∧
        ‖q.2‖ ≤ 2*b ∧ q.1.1 ∈ X ∧ q.1.2 ∈ X ∧
        lam⁻¹ • (lam • q.2) ∈ tsupport π := by
  intro χsource π X e Kcrit D
  have hX : IsCompact X := hoc.union (fam.inputMask_compact.comp_left Complex.ofReal_zero)
  have hXball : X ⊆ ball x (3*fam.physicalRadius) := by
    intro y hy
    rcases hy with hy | hy
    · exact (closedBall_subset_ball (by linarith [fam.physicalRadius_pos])) (hos hy)
    · exact fam.inputMask_support (tsupport_comp_subset Complex.ofReal_zero fam.inputMask hy)
  have hπ : IsCompact (tsupport π) := hasCompactSupport_annularSelector a b ha hb
  have hKD : Kcrit ⊆ D := by
    intro w hw
    refine ⟨hXball hw.1, ?_⟩
    rw [mem_ball_zero_iff]
    have hh := (tsupport_annularSelector_subset a b ha hb hw.2).2
    linarith [le_max_right Bsource (2*b)]
  refine ⟨hX,hXball,e.toHomeomorph.isCompact_preimage.mpr (hX.prod hπ),hKD,?_⟩
  intro symbol lam hlam order backward A α
  have hs := tsupport_selected_diagonalAmplitude_subset χout χsource π symbol hlam order backward
  have hs' (v : Joint) (hv : v ∈ tsupport (Function.uncurry α)) :
      v.1.1 ∈ X ∧ v.2 ∈ Kcrit := by
    have hh := hs hv
    cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte] at hh
    · exact ⟨Or.inl hh.1, Or.inr hh.2.1, hh.2.2⟩
    · exact ⟨Or.inr hh.2.1, Or.inl hh.1, hh.2.2⟩
  refine ⟨fun q w hw ↦ (hs' (q,w) (subset_tsupport _ hw)).2,hs',?_⟩
  intro Cpar c hc q hq
  have hh := hs' _ hq
  refine ⟨⟨⟨hXball hh.1,hc⟩,hKD hh.2⟩,?_,hh.1,hh.2.1,?_⟩
  · exact (tsupport_annularSelector_subset a b ha hb hh.2.2).2
  · rw [inv_smul_smul₀ hlam]
    exact hh.2.2

end JanetCartan.ResponseTransfer.DiagonalPdo
