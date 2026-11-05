module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.DetectorCover

/-!
# Joint carrier and detector covers after all local cutoffs

Select a finite family from the original compact incidence support using the
actual returned carrier plateau and angular radius simultaneously. Selecting a
carrier cover before those radii are known would not preserve its coverage.
The index is the original carrier/direction pair, so parent cells and their
scalar domains can be retained by restriction along the selected indices.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic

/-- On a compact joint incidence support, choose original parent cells and
sampling buffers pointwise BEFORE the local analytic cutoffs and finite cover
are chosen. The parent map is fixed independently of the fields and frequencies
(`app:ch_waves:thm:sampling`). -/
theorem exists_joint_incident_workingBalls
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)}
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (W : Set (Euclidean 3 × Euclidean n))
    (hz : ∀ w ∈ W, w.1 ∈ parameterInterior P.radius)
    (centers : Finset (parameterCube P.radius)) (σ : centers → ℝ)
    (hcover : ∀ z ∈ parameterCube P.radius, ∃ j : centers,
      ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ∈
        ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) :
    ∃ parent : W → centers, ∃ ρ : W → ℝ, ∀ w,
      0 < ρ w ∧
      closedBall ((0 : Euclidean n), (w.1.1, T.reference.spatialPatch w.1.1)) (2 * ρ w) ⊆
        ball ((0 : Euclidean n), ((parent w).1.1,
          T.reference.spatialPatch (parent w).1.1)) (σ (parent w)) ∧
      closedBall ((0 : Euclidean n), (w.1.1, T.reference.spatialPatch w.1.1)) (2 * ρ w) ⊆
        LeadingWave.FullModulation.domain T ∧
      closedBall (0 : Euclidean n) (2 * ρ w) ⊆ K ∧
      closedBall w.1.1 (2 * ρ w) ⊆ parameterInterior (2 * P.radius) := by
  classical
  choose parent hp using fun w : W ↦ hcover w.1.1 (fun j ↦ (hz w.1 w.2 j).le)
  choose ρ hρ hparent hphase hspace hcarrier using fun w : W ↦
    exists_sampling_workingBall_in_retained_cell hP T hball
      (fun j ↦ (hz w.1 w.2 j).le) (hp w)
  exact ⟨parent, ρ, fun w ↦ ⟨hρ w, hparent w, hphase w, hspace w, hcarrier w⟩⟩

/-- Choose a finite cover AFTER the local constructors return both their
carrier plateau radii and angular radii. The cover retains the ENTIRE supplied
joint incidence support, with the exact quarter angular width required by the
detector square partition. Its carrier component lies on the same local
cutoff's plateau (`app:ch_waves:thm:sampling`). -/
theorem exists_finite_joint_incident_cover
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {W : Set (Euclidean 3 × Euclidean n)} (hW : IsCompact W)
    (hz : ∀ w ∈ W, w.1 ∈ parameterInterior P.radius)
    (hne : ∀ w ∈ W, w.2 ≠ 0)
    (hinc : ∀ w ∈ W, incidence w.2 (P.toFun w.1) = 0)
    (r d : W → ℝ) (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (ψ : W → SeparatedSampling.Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → ψ w z = 1) :
    ∃ labels : Finset W,
      (∀ i : labels, T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2 ≠ 0) ∧
      ∀ w ∈ W, ∃ i : labels,
        w.1 ∈ ball i.1.1.1 (d i.1 / 2) ∧
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2) ∈
          ball (NormedSpace.normalize
            (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
            (angularWidth (n := n)
              (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) ∧
        ψ i.1 w.1.ofLp = 1 := by
  classical
  let e := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  have he (w : W) : e w.1.2 ≠ 0 :=
    FrozenIncidence.tangential_direction_ne_zero T hP (hz w.1 w.2)
      (hne w.1 w.2) (hinc w.1 w.2)
  have hc : Continuous (fun w : W ↦ e w.1.2) :=
    e.continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hnorm : Continuous (fun w : W ↦ NormedSpace.normalize (e w.1.2)) :=
    (hc.norm.inv₀ (fun w ↦ norm_ne_zero_iff.mpr (he w))).smul hc
  let O (w : W) : Set W :=
    {v | v.1.1 ∈ ball w.1.1 (d w / 2)} ∩
      {v | NormedSpace.normalize (e v.1.2) ∈
        ball (NormedSpace.normalize (e w.1.2)) (angularWidth (n := n) (e w.1.2) (r w) / 4)}
  have hO (w : W) : IsOpen (O w) :=
    (isOpen_ball.preimage (continuous_fst.comp continuous_subtype_val)).inter
      (isOpen_ball.preimage hnorm)
  have hcover : (univ : Set W) ⊆ ⋃ w, O w := by
    intro w _
    exact mem_iUnion.mpr ⟨w, mem_ball_self (div_pos (hd w) (by norm_num)),
      mem_ball_self (div_pos (angularWidth_spec (he w) (hr w)).1 (by norm_num))⟩
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  obtain ⟨labels, hlabels⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  refine ⟨labels, fun i ↦ he i.1, ?_⟩
  intro w hw
  obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp (hlabels (mem_univ (⟨w, hw⟩ : W)))
  refine ⟨⟨i, hi⟩, hwi.1, hwi.2, ?_⟩
  apply hplateau i
  change w.1 ∈ closedBall i.1.1 (d i)
  exact ball_subset_closedBall ((ball_subset_ball (by linarith [hd i])) hwi.1)

end JanetCartan.Sampling
