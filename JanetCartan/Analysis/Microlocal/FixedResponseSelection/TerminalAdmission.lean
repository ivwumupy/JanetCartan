module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.SectorIncidenceSelection
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryAdmission
public import Mathlib.Algebra.Order.Field.Pi

/-!
# Finite retained-family margins before common reference selection

Take the minimum of the actual finite primary-phase margins, then apply the
existing history-admission producer at the SAME family's coefficient radius.
The returned reference tolerance also respects the independent no-return
margin. It precedes the reference, initial frequency and every finite history.
This lemma does not move a previously reference-dependent family before that
reference; that quantifier-order obligation remains with the selection step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.FiniteMasks.ActualFamily
open ActualCarriers.CurrentFullPhase ProjectedStressFrame ProtectedFlow GeometricProfile

/-- One finite tolerance admits the SAME selected coefficient radius and all
original primary-phase margins. It is chosen before the reference and history;
its reference premise is the componentwise margin supplied by the original
common source-scale initializer. The separate no-return margin is retained
(`app:ch_seed:setup:seed-current`, `app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_reference_tolerance_for_selected_full_source_margins
    {d : ℕ} {ι : Type*} [Finite ι]
    {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
    {K : Set (Euclidean (d+1))}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K M)
    (δphase : ι → ℝ) (hδphase : ∀ j, 0 < δphase j)
    (ext : BallExtension.Parameters (Euclidean (d+1)))
    (hext : ext.center = 0) {ηprotect : ℝ} (hηprotect : 0 < ηprotect) :
    ∃ δ > (0 : ℝ), (∀ j, δ ≤ δphase j) ∧
    ∃ η > (0 : ℝ), η ≤ ηprotect ∧
      ∀ Gref : FlatReference (d+1), ∀ R : ℝ,
      ext.radius < R → R < Gref.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : Euclidean (d+1)) ext.radius) 6
        (fun y ↦ projectedStress Gref.map y i - cubeStress (d+1) i) < η) →
      ∀ kMin : ℕ,
      displacementLoss (d+1) + bandExponent * (8 + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress (d+1)) f.coefficientRadius) ∧
      (∀ A : Set (Euclidean (d+1)), cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < δ) ∧
      ∀ j, ∀ A : Set (Euclidean (d+1)), cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < δphase j := by
  let := Fintype.ofFinite ι
  obtain ⟨δ, hδ, hδall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : ι ↦ (0 : ℝ)) (y := δphase) hδphase
  have hδle (j : ι) : δ ≤ δphase j := by simpa using (hδall j).le
  obtain ⟨η, hη, hadmit⟩ := exists_reference_tolerance_for_retained_history_admission
    ext hext rfl f.coefficientRadius_pos hδ
  refine ⟨δ, hδ, hδle, min η ηprotect, lt_min hη hηprotect, min_le_right _ _, ?_⟩
  intro Gref R hrR hR href kMin horder
  obtain ⟨S, hS, hhistory⟩ := hadmit Gref R ext.radius_pos hrR hR
    (fun i ↦ (href i).trans_le (min_le_left _ _)) kMin horder
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu
  obtain ⟨hQ, hQrange, hQlow⟩ := hhistory R₀ hR₀ s u ell hu
  exact ⟨hQ, hQrange, hQlow, fun j A ↦ (hQlow A).trans_le (hδle j)⟩

end JanetCartan.ResponseTransfer.RetainedFactors
