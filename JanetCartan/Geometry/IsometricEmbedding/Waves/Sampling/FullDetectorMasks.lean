module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullDetectorSupport

/-!
# Exact weighted masks on the full carrier/detector support

The cover includes every incident pair over the original compact carrier
support. Its local radii are those returned by the analytic constructors.
The same selected labels support both the carrier bumps and the angular
square masks. No section restriction or smaller detector is substituted.

Consumer: the support premise of `JointWeightedNormals`, followed by the
actual finite-family realization on these selected retained cells.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff Classical

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic SeparatedSampling

/-- Construct compatible masks on the complete original incidence support.
The cover is selected AFTER both actual local radii are known. The resulting
weighted square identity holds throughout the corresponding full input
support, including nonzero spectators (`app:ch_waves:thm:sampling`,
`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem exists_fullDetector_weighted_masks {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (ha : detectorDirectionSupport a ⊆ O)
    (r d : fullDetectorIncidenceSupport P Z a → ℝ)
    (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (localWeight : fullDetectorIncidenceSupport P Z a → Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → localWeight w z = 1) :
    ∃ labels : Finset (fullDetectorIncidenceSupport P Z a),
    let ηb := fun i : labels ↦ T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2
    let r' := fun i : labels ↦ r i.1
    ∃ hηb : ∀ i, ηb i ≠ 0,
    ∃ b : labels → Point → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i)) ∧
      (∀ i z, b i z ∈ Icc (0 : ℝ) 1) ∧
      (∀ i z, b i z ≠ 0 → localWeight i.1 z = 1) ∧
      (∀ q ∈ fullDetectorInputSupport T Z a, ∃ i : labels,
        b i q.1.ofLp = 1 ∧ q.2 ∈
          ball (normalize (ηb i)) (angularWidth (ηb i) (r' i) / 4)) ∧
    ∀ (ψ : Point → ℝ) (B Pψ : ℝ),
      PatchBounds ψ B Pψ → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ s : Finset labels,
        ContDiff ℝ ∞ (carrierSubsetWeight ψ b s) ∧
        HasCompactSupport (carrierSubsetWeight ψ b s) ∧
        PatchBounds (carrierSubsetWeight ψ b s) B Pψ) ∧
      (∀ (s : Finset labels) (i : s) z, carrierSubsetWeight ψ b s z ≠ 0 →
        localWeight i.1.1 z = 1) ∧
      (∀ (z : Point) (η : Euclidean (n - 1)),
        (WithLp.toLp 2 z, normalize η) ∈ fullDetectorInputSupport T Z a →
        ∑ s : Finset labels, ∑ i : s, carrierSubsetWeight ψ b s z *
          subsetAngularMask ηb r' hηb (fun i ↦ hr i.1) s i η ^ 2 = ψ z) := by
  classical
  obtain ⟨hW, hspec⟩ := fullDetectorIncidenceSupport_spec hP hZ hZP hroot a ha
  obtain ⟨labels, hηb, hcover⟩ := exists_finite_joint_incident_cover T hP hW
    (fun w hw ↦ (hspec w hw).1) (fun w hw ↦ (hspec w hw).2.1)
    (fun w hw ↦ (hspec w hw).2.2.1) r d hr hd localWeight hplateau
  obtain ⟨_B, _hB, b, hbs, hbc, hbb, hbone, _hbsupp, hbplateau⟩ :=
    exists_joint_cover_carrier_weights (fun i : labels ↦ i.1.1.1)
      (fun i ↦ d i.1) (fun i ↦ hd i.1) (fun i ↦ localWeight i.1) (fun i ↦ hplateau i.1)
  have hfull (q) (hq : q ∈ fullDetectorInputSupport T Z a) : ∃ i : labels,
      b i q.1.ofLp = 1 ∧ q.2 ∈ ball
        (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
        (angularWidth (n := n)
          (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) := by
    rw [← image_fullDetectorIncidenceSupport T hP hZP a] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    obtain ⟨i, hz, hdir, _hlocal⟩ := hcover w hw
    exact ⟨i, hbone i w.1.ofLp (ball_subset_closedBall hz), hdir⟩
  have hb (i : labels) (z : Point) : b i z ∈ Icc (0 : ℝ) 1 :=
    ⟨(hbb i).nonneg z, (hbb i).le_bound z⟩
  refine ⟨labels, hηb, b, fun i ↦ ⟨hbs i, hbc i⟩, hb, hbplateau, hfull, ?_⟩
  intro ψ B Pψ hψ hψs hψc
  refine ⟨fun s ↦ ⟨carrierSubsetWeight_contDiff ψ b hψs hbs s,
    carrierSubsetWeight_hasCompactSupport ψ b hψc s,
    carrierSubsetWeight_patchBounds ψ b hψ hb s⟩, ?_, ?_⟩
  · intro s i z hz
    exact hbplateau i.1 z ((carrierSubsetWeight_support ψ b s hz).2 i.1 i.2)
  · intro z η hη
    exact sum_carrierSubsetWeight_mul_subsetAngularMask_sq
      (fun i : labels ↦ T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2)
      (fun i ↦ r i.1) hηb (fun i ↦ hr i.1) ψ b z η (fun _ ↦ hfull _ hη)

end JanetCartan.Sampling
