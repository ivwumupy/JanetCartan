module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedIncidence.Local
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteIncidence.Detection

/-!
# A finite cover of the realized frozen incidence patches

At each unit frequency all patches of one original incidence chart are
constructed with their smaller realized masks first. Their neighborhoods are intersected before compactness is
used. One positive root tolerance and frame threshold are then fixed, and the
actual roots are constructed only once. This is the geometric input for
`exists_canonicalFrozenMatrixSymbol_unit_gap_of_incidence`
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open ProjectedStressFrame

/-- Construct a finite sphere cover with every source patch retained, concrete
smaller realized masks, positive radial representatives of norm `1/4`,
reference equivalences and fixed minors. The centers stay on the unit sphere.
The literal unit carriers, adjoints, full normals and Fourier identities are
proved for these SAME data. One root family, chosen
at a common tolerance, simultaneously has the exact inverse-domain identities,
positive literal weights (including initial multipliers), and the full detector
inequality. All choices precede the immersion and use the supplied Hamilton
family (`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_finite_realized_frozen_incidence_cover {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b s : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hs : 0 < s) (hsradius : ∀ i, 3 * s < (T i).physicalRadius) (hsb : 3 * s < b)
    (M : ℝ) {κmet κnormal cap : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hcap : 0 < cap) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧
    ∃ c B εmax ε δ cdet : ℝ, 0 < c ∧ 0 < B ∧ 0 < εmax ∧ 0 < ε ∧ 0 < δ ∧ 0 < cdet ∧
    ∃ (m : ℕ) (chart : Fin m → Fin R.chartCount) (center : Fin m → Euclidean n)
      (ρ : Fin m → ℝ),
    ∃ scale : (l : Fin m) → Fin (D.patchCount (R.sourceChart (chart l))) → ℝ,
    ∃ d : (l : Fin m) → (a : Fin (D.patchCount (R.sourceChart (chart l)))) →
      FrozenIncidencePatchData (T ⟨R.sourceChart (chart l), a⟩)
        (D.roots (R.sourceChart (chart l)) a (center l))
        ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
          (scale l a • center l)),
    ∃ hcell : ∀ l a, 4 * (d l a).a < 1 / 2,
      (∀ l a, 0 < scale l a ∧ ‖scale l a • center l‖ = 1 / 4 ∧
        NormedSpace.normalize (scale l a • center l) = NormedSpace.normalize (center l) ∧
        NormedSpace.normalize
          ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
            (scale l a • center l)) =
        NormedSpace.normalize
          ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
            (center l))) ∧
      (∀ l, center l ∈ sphere (0 : Euclidean n) 1) ∧
      (∀ l, 0 < ρ l) ∧
      (∀ l, ball (center l) (ρ l) ⊆ ball (R.center (chart l)) (R.radius (chart l))) ∧
      (sphere (0 : Euclidean n) 1 ⊆ ⋃ l, ball (center l) (ρ l)) ∧
      (∀ l a, ρ l ≤ (d l a).frequencyRadius) ∧
      (∀ l a, 6 * (d l a).a < cap ∧ ε ≤ (d l a).rootTolerance ∧
        (d l a).rootTolerance ≤ εmax ∧ (d l a).rootTolerance / c ≤ (d l a).a / 8) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm (closedBall (0 : Euclidean n) b) 4 F ≤ M →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v,
          κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        ∃ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
            Euclidean n × Euclidean n → ℝ,
          IsConstructedIncidenceRootFamily D R s c B ε (projectedStress F)
            (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a⟩⟩) g ∧
          (∀ l a, (d l a).Geometry ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩) ∧
          (∀ l a, (d l a).UnitRealization
            ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩ F (hcell l a)) ∧
          (∀ l, ∀ k ∈ ball (center l) (ρ l), ∀ t > (0 : ℝ), ∀ a,
            frozenHighFrequencyRadius (T ⟨R.sourceChart (chart l), a⟩) (d l a).G ≤ ‖t • k‖ →
            (d l a).RootAt ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩ F (t • k)
              (incidenceParameter (D.roots (R.sourceChart (chart l)) a (R.center (chart l)))
                (g (chart l) a (0, k)))) ∧
          (∀ l, ∀ k ∈ ball (center l) (ρ l), ∀ v : Euclidean n,
            cdet * ‖v‖ ^ 2 ≤ ‖imageChannel (pencil (projectedStress F 0) k) v‖ ^ 2 +
              ∑ a, ⟪quadratic (projectedStress F 0)
                ((T ⟨R.sourceChart (chart l), a⟩).carrierGradient
                  ⟨projectedStress F, hQ, hlow _⟩ 0
                  (incidenceParameter (D.roots (R.sourceChart (chart l)) a (R.center (chart l)))
                    (g (chart l) a (0, k)))), v⟫_ℝ ^ 2) := by
  classical
  obtain ⟨R, hR, _, c, B, εmax, _, hc, hB, hemax, _, hroots⟩ :=
    exists_constructed_incidence_roots hD T hBU hframe hsradius hsb
  let S := sphere (0 : Euclidean n) 1
  have hchoose (k : S) : ∃ j, k.1 ∈ ball (R.center j) (R.radius j) :=
    mem_iUnion.mp (hR.2.2.1 k.2)
  choose j hj using hchoose
  have hk (k : S) : k.1 ≠ 0 := by
    have hh : ‖k.1‖ = 1 := by simpa only [S, mem_sphere, dist_zero_right] using k.2
    intro hz
    simp [hz] at hh
  have hkbig (k : S) : k.1 ∈ ball (R.center (j k)) (2 * R.radius (j k)) :=
    ball_subset_ball (by linarith [hR.1 (j k)]) (hj k)
  choose scale hscale hscalenorm hscaledir hprojecteddir d hcell hcaplocal htol htolradius hlocaldata
    using fun (k : S) (a : Fin (D.patchCount (R.sourceChart (j k)))) ↦
    exists_realized_frozen_incidence_patch hn hD hR T (j k) a (isCompact_closedBall _ _) hBU
      (hframe _) M hκmet hκnormal (hkbig k) (hk k) hc hemax hcap
  -- First take a common neighborhood for every patch at a given frequency.
  have hsmall (k : S) : ∃ e > (0 : ℝ), ∀ a, e < (d k a).frequencyRadius := by
    simpa using Pi.exists_forall_pos_add_lt (fun a ↦ (d k a).frequencyRadius_pos)
  choose ep hep hepa using hsmall
  choose ec hec hecball using fun k : S ↦ Metric.isOpen_iff.mp isOpen_ball k.1 (hj k)
  let rad (k : S) := min (ep k) (ec k)
  have hrad (k : S) : 0 < rad k := lt_min (hep k) (hec k)
  have hradpatch (k : S) (a) : rad k ≤ (d k a).frequencyRadius :=
    (min_le_left _ _).trans (hepa k a).le
  have hradchart (k : S) : ball k.1 (rad k) ⊆ ball (R.center (j k)) (R.radius (j k)) :=
    (ball_subset_ball (min_le_right _ _)).trans (hecball k)
  have hcover : S ⊆ ⋃ k : S, ball k.1 (rad k) := by
    intro k hk
    exact mem_iUnion.mpr ⟨⟨k, hk⟩, mem_ball_self (hrad ⟨k, hk⟩)⟩
  -- Compactness is used only after all local shrinking.
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : Euclidean n) 1).elim_finite_subcover
    (fun k : S ↦ ball k.1 (rad k)) (fun _ ↦ isOpen_ball) hcover
  let e := t.equivFin.symm
  let v : Fin t.card → S := fun l ↦ (e l).val
  let I := (l : Fin t.card) × Fin (D.patchCount (R.sourceChart (j (v l))))
  obtain ⟨εpatch, hepatch, hepatchi⟩ := Pi.exists_forall_pos_add_lt
    (fun i : I ↦ (d (v i.1) i.2).rootTolerance_pos)
  obtain ⟨δpatch, hdpatch, hdpatchi⟩ := Pi.exists_forall_pos_add_lt
    (fun i : I ↦ (d (v i.1) i.2).frameThreshold_pos)
  obtain ⟨εdet, δdet, cdet, hedet, hedetmax, hddet, hcdet, hdetect⟩ :=
    exists_same_root_frozen_detection_threshold hD hR T hBU hframe (by linarith) hc hemax
  let ε := min εpatch εdet
  have hε : 0 < ε := lt_min hepatch hedet
  obtain ⟨δroot, hdroot, hconstruct⟩ := hroots ε hε ((min_le_right _ _).trans hedetmax)
  let δ := min δroot (min δdet (δpatch / 14))
  have hδ : 0 < δ := lt_min hdroot (lt_min hddet (by positivity))
  have hep (i : I) : ε ≤ (d (v i.1) i.2).rootTolerance :=
    (min_le_left _ _).trans (by simpa using (hepatchi i).le)
  refine ⟨R, hR, c, B, εmax, ε, δ, cdet, hc, hB, hemax, hε, hδ, hcdet,
    t.card, fun l ↦ j (v l), fun l ↦ (v l).1, fun l ↦ rad (v l),
    fun l ↦ scale (v l), fun l ↦ d (v l), fun l ↦ hcell (v l),
    fun l a ↦ ⟨hscale (v l) a, hscalenorm (v l) a, hscaledir (v l) a, hprojecteddir (v l) a⟩,
    fun l ↦ (v l).2, fun l ↦ hrad (v l), fun l ↦ hradchart (v l), ?_,
    fun l ↦ hradpatch (v l),
    fun l a ↦ ⟨hcaplocal (v l) a, hep ⟨l, a⟩, htol (v l) a, htolradius (v l) a⟩, ?_⟩
  · intro k hk
    obtain ⟨q, hq, hkq⟩ := mem_iUnion₂.mp (ht hk)
    refine mem_iUnion.mpr ⟨e.symm ⟨q, hq⟩, ?_⟩
    simpa [v] using hkq
  · intro F hF hi hrank hM hmet hnormal hclose
    have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
    obtain ⟨hlow, g, hg⟩ := hconstruct (projectedStress F) hQ
      (fun i ↦ (hclose i).trans_le (min_le_left _ _))
    have hreg : ∀ x ∈ closedBall (0 : Euclidean n) b,
        ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) x := fun x hx ↦
      ((hQ.contDiffAt (hU.mem_nhds (hBU hx))).sub contDiffAt_const).of_le (by simp)
    have hglobal : cNorm (closedBall (0 : Euclidean n) b) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δpatch := by
      apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _) hreg hdpatch
      intro i
      convert (hclose i).trans_le ((min_le_right δroot _).trans (min_le_right δdet _)) using 1
      norm_num
    have hlocal (l : Fin t.card) (a : Fin (D.patchCount (R.sourceChart (j (v l))))) :=
      hlocaldata (v l) a F hF hi hrank hM hmet hnormal
        (hglobal.trans (by simpa using hdpatchi ⟨l, a⟩)) hlow
    refine ⟨hlow, g, hg, fun l a ↦ (hlocal l a).1, fun l a ↦ (hlocal l a).2.1, ?_, ?_⟩
    · intro l k hk t ht a hhigh
      exact (hlocal l a).2.2 hs (hep ⟨l, a⟩) g hg k
        (ball_subset_ball (hradpatch (v l) a) hk) t ht hhigh
    · intro l k hk w
      exact hdetect (projectedStress F) hQ
        (fun i ↦ (hclose i).trans_le ((min_le_right δroot _).trans (min_le_left _ _)))
        hlow hs (min_le_right _ _) g hg (j (v l)) k
          (ball_subset_closedBall (hradchart (v l) hk)) w

end JanetCartan.ContinuumNormal.FrozenModel
