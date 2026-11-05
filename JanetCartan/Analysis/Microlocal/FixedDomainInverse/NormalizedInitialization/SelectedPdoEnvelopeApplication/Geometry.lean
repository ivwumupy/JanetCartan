module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.SelectedSupport
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates

/-!
# Original physical source boxes for the selected PDO letters

The same two physical masks and annular selector provide the compact support
required by both primitive diagonal PDO estimates. This specializes their
support construction to the chart-coordinate endpoint and algebraic letters
of `app:ch_response:eq:fixed-factor-transfer`; no comparable-shell carrier is
imposed on the source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open FourierIntegral ResponseTransfer ResponseTransfer.NearCarrierFullLow
open ResponseTransfer.DirectEvolution ResponseTransfer.DirectEvolution.BranchAmplitudes
open ResponseTransfer.DirectEvolution.AnnularComplement ResponseTransfer.DiagonalPdo
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d+1)
local notation "Joint" => (E × Par) × W
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The original compact masks and complete annular support fit one fixed
source box in both literal orientations. Only the masks' actual compact
support enters this geometric step (`app:ch_response:eq:direct-envelope-profile`). -/
theorem selected_pdo_source_box_support
    (x : E) (radius : ℝ) (χout χsource : E → ℂ)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ ball x radius)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (Bsource : ℝ) :
    let π := annularSelector (n := d+1) a b ha hb
    let X := tsupport χout ∪ tsupport χsource
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    let Kcrit := e ⁻¹' (X ×ˢ tsupport π)
    let D := e ⁻¹' (ball x (radius) ×ˢ
      ball (0 : E) (1 + max Bsource (2*b)))
    IsCompact X ∧ X ⊆ ball x (radius) ∧
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
        normalizedSlice c q ∈ (ball x (radius) ×ˢ Cpar) ×ˢ D ∧
        ‖q.2‖ ≤ 2*b ∧ q.1.1 ∈ X ∧ q.1.2 ∈ X ∧
        lam⁻¹ • (lam • q.2) ∈ tsupport π := by
  intro π X e Kcrit D
  have hX : IsCompact X := hoc.union hsc
  have hXball : X ⊆ ball x radius := hmask
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

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
