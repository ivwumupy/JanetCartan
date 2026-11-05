module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Gap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Weights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.IncidenceMasks

/-!
# The spectral gap on a supplied retained incidence family

Consumer: `jc-continuum-normal`, on the SAME initialized retained row.
The supplied finite centers, cover, chart containment, detector inequality and
angular plateaux are the outputs of
`LeadingCarrier.exists_covering_retained_forward_adjoint_row_before_geometry`.
The primitive outer inverse and Jacobian/derivative gaps are retained by
`jc-retained-frozen-unit-realization`. `projectedStress_flatReference_zero` and
`FamilyInputs.exists_retained_seed_covector_buffer` (in `CommonCharts/SeedCovector`) supply the origin frame
and seed covector identity; `FamilyInputs.SourceMatching.current_carrierGradient_source_dilation`
retains the selected seed across positive contractions. The selected column's
nonvanishing and pencil-null relation come from the SAME
`LeadingWave.FullModulation.exists_finite_actual_leading_family` cell, via
`FullModulation.nullvector_on_carrier`.

This theorem deduces the finite spectral estimate from those primitive inputs;
the parent must instantiate them on its initialized row. It does not construct
an operator, change a mask, choose a minor, or shrink the finite cover.
Sources: `app:ch_background:prop:bg-frame`, Step 2,
`app:ch_seed:eq:seed-frozen-detection`, and `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open NullTransport ProjectedStressFrame

/-- The original center/patch index of `RetainedAdjointRow`, used without
selecting another cover (`app:ch_seed:eq:seed-frozen-detection`). -/
abbrev RetainedIncidenceChannel {n : ℕ} (D : CoverData n)
    (centers : Finset (IncidenceCenter D)) :=
  (j : centers) × Fin (D.patchCount j.1.1.1)

/-- The supplied Hamilton family at each retained center/patch channel.
Consumer: `retained_incidence_spectral_bounds` (`app:ch_background:eq:bg-Psi`). -/
abbrev retainedIncidenceFamily {n : ℕ} {D : CoverData n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (centers : Finset (IncidenceCenter D)) (i : RetainedIncidenceChannel D centers) :=
  T i.1.1.1.1 i.2

/-- The original `D.roots` at the retained cover centers. Consumer:
`retained_incidence_spectral_bounds` (`app:ch_seed:eq:seed-frozen-detection`). -/
abbrev retainedIncidenceCenters {n : ℕ} {D : CoverData n}
    (centers : Finset (IncidenceCenter D)) (i : RetainedIncidenceChannel D centers) :=
  D.roots i.1.1.1.1 i.2 i.1.1.1.2

variable {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (centers : Finset (IncidenceCenter D))


variable (G : (RetainedIncidenceChannel D centers) → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))
variable (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ j, cNorm (closedBall (0 : Euclidean n) ((retainedIncidenceFamily T centers) j).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < ((retainedIncidenceFamily T centers) j).family.threshold)
    (F : Euclidean n → Euclidean (embeddingDimension n)) (row col : (RetainedIncidenceChannel D centers) → Fin n)
    (Φ Y : (RetainedIncidenceChannel D centers) → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (ηb : (RetainedIncidenceChannel D centers) → Euclidean (n - 1)) (r a r' a' : (RetainedIncidenceChannel D centers) → ℝ)
    (hηb : ∀ j, ηb j ≠ 0) (hr : ∀ j, 0 < r j) (ha : ∀ j, 0 < a j)
    (hr' : ∀ j, 0 < r' j) (ha' : ∀ j, 0 < a' j)
    (hrr : ∀ j, r' j ≤ r j) (haa : ∀ j, a' j ≤ a j)
    {b cJ : (RetainedIncidenceChannel D centers) → ℝ} {V L : (RetainedIncidenceChannel D centers) → Set (ℝ × Euclidean (n - 1))}
    (har : ∀ j, 6 * a j ≤ 3 * r j)
    (hcarrier : ∀ j, closedBall (spectatorCenter ((retainedIncidenceCenters centers) j)) (3 * r j) ×ˢ
      closedBall ((retainedIncidenceCenters centers) j 0) (3 * r j) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * (D.patches j.1.1.1.1 j.2).radius / 2))
    (hf : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart ((retainedIncidenceFamily T centers) j) ⟨Q, hQ, hlow j⟩))
      (physicalParameterSet ((retainedIncidenceCenters centers) j) (6 * a j) ×ˢ dataSet ((retainedIncidenceCenters centers) j) (ηb j) (3 * r j)))
    (hInv : ∀ j, BufferedPhaseInverse (adaptedTransportChart ((retainedIncidenceFamily T centers) j) ⟨Q, hQ, hlow j⟩)
      (physicalParameterSet ((retainedIncidenceCenters centers) j) (6 * a j)) (dataBox ((retainedIncidenceCenters centers) j) (ηb j) (r j))
      (dataSet ((retainedIncidenceCenters centers) j) (ηb j) (2 * r j)) (dataBox ((retainedIncidenceCenters centers) j) (ηb j) (2 * r j))
      (V j) (L j) (b j) (cJ j) (G j))
    (htrans : ∀ j, ∀ p ∈ physicalParameterSet ((retainedIncidenceCenters centers) j) (6 * a j),
      ∀ u ∈ supportedCone ((retainedIncidenceCenters centers) j) (NormedSpace.normalize (ηb j)) (r j) (angularWidth (ηb j) (r j)),
        ‖(adaptedTransportChart ((retainedIncidenceFamily T centers) j) ⟨Q, hQ, hlow j⟩ p u).2 - u.2‖ ≤
          (angularWidth (ηb j) (r j) / 4) * ‖u.2‖)
    (hcJ : ∀ j, 0 < cJ j) (hV : ∀ j, IsOpen (V j)) (hLV : ∀ j, L j ⊆ V j)



include hD hr ha hrr haa har hcarrier hf hInv htrans hcJ hV hLV

/-- Continuity, boundedness, pointwise nonnegativity and a positive
high-frequency gap for the literal ideal image plus the finite reflected
carrier sum on the supplied retained incidence family. All root membership,
inverse recovery, positive weights and zero-energy detection are deduced here.
The frequency threshold is the original geometric threshold and frequencies
are Euclidean (`app:ch_background:prop:bg-frame`, Step 2). -/
theorem retained_incidence_spectral_bounds
    (hn : 5 ≤ n)
    (εcover : centers → ℝ)
    (hcover : sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j))
    (hdomain : ∀ j : centers, ball j.1.1.2 (εcover j) ⊆ D.domain j.1.1.1)
    (hgram : ∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
      c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
        ∑ l, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 l).toFun
          (D.roots j.1.1.1 l q))) s ^ 2)
    (har' : ∀ i : (RetainedIncidenceChannel D centers), a' i ≤ r' i)
    (hQzero : Q 0 = cubeStress n)
    (hproject : Q 0 = projectedStress F 0)
    (hF : ContDiffAt ℝ 2 F 0)
    (himm : Function.Injective (fderiv ℝ F 0))
    (hrank : Set.range (normalMap F 0) =
      (normalSpace F 0 : Set (Euclidean (embeddingDimension n))))
    (hgap : ∀ i : (RetainedIncidenceChannel D centers), ∀ p ∈ physicalParameterSet ((retainedIncidenceCenters centers) i) (6 * a i),
      ∀ u ∈ dataBox ((retainedIncidenceCenters centers) i) (ηb i) (2 * r i),
        ‖((G i).symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
          (fderiv ℝ (adaptedTransportChart ((retainedIncidenceFamily T centers) i) ⟨Q, hQ, hlow i⟩ p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hseed : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        ((retainedIncidenceFamily T centers) ⟨j, l⟩).carrierGradient ⟨Q, hQ, hlow ⟨j, l⟩⟩ 0 (D.roots j.1.1.1 l q) =
          (D.patches j.1.1.1 l).toFun (D.roots j.1.1.1 l q))
    (hplateau : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        angularMask ((retainedIncidenceCenters centers) ⟨j, l⟩) (NormedSpace.normalize (ηb ⟨j, l⟩))
          (ha' ⟨j, l⟩) (angularWidth_spec (hηb ⟨j, l⟩) (hr' ⟨j, l⟩)).1
          (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))
          (NormedSpace.normalize (((retainedIncidenceFamily T centers) ⟨j, l⟩).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1)
    (hnull : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        pencil (projectedStress F 0)
          (((retainedIncidenceFamily T centers) ⟨j, l⟩).carrierGradient ⟨Q, hQ, hlow ⟨j, l⟩⟩ 0 (D.roots j.1.1.1 l q)) *ᵥ
          (fun k ↦ carrierNullvector ((retainedIncidenceFamily T centers) ⟨j, l⟩) ⟨Q, hQ, hlow ⟨j, l⟩⟩ (col ⟨j, l⟩)
            (0, D.roots j.1.1.1 l q) k) = 0)
    (hcol : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        carrierNullvector ((retainedIncidenceFamily T centers) ⟨j, l⟩) ⟨Q, hQ, hlow ⟨j, l⟩⟩ (col ⟨j, l⟩)
          (0, D.roots j.1.1.1 l q) ≠ 0) :
    Continuous (retainedFrozenMatrixSymbol (retainedIncidenceFamily T centers) Q hQ hlow F row col Φ Y (retainedIncidenceCenters centers) ηb r a r' a' hηb hr' ha') ∧ (∃ B ≥ (0 : ℝ), ∀ k, ‖(retainedFrozenMatrixSymbol (retainedIncidenceFamily T centers) Q hQ hlow F row col Φ Y (retainedIncidenceCenters centers) ηb r a r' a' hηb hr' ha') k‖ ≤ B) ∧
      (∀ k, ((retainedFrozenMatrixSymbol (retainedIncidenceFamily T centers) Q hQ hlow F row col Φ Y (retainedIncidenceCenters centers) ηb r a r' a' hηb hr' ha') k).PosSemidef) ∧
      ∃ g > (0 : ℝ), ∀ k : Euclidean n, frozenFamilyHighFrequencyRadius (retainedIncidenceFamily T centers) G ≤ ‖k‖ →
        ∀ s : Euclidean n, g * ‖s‖ ^ 2 ≤ dotProduct (fun i ↦ s i) ((retainedFrozenMatrixSymbol (retainedIncidenceFamily T centers) Q hQ hlow F row col Φ Y (retainedIncidenceCenters centers) ηb r a r' a' hηb hr' ha') k *ᵥ (fun i ↦ s i)) := by
  classical
  have hP (i : (RetainedIncidenceChannel D centers)) := (hD.2.2.2.2.1 i.1.1.1.1 i.2).1
  refine ⟨retainedFrozenMatrixSymbol_unit_continuous (retainedIncidenceFamily T centers) G Q hQ hlow F row col Φ Y
    (retainedIncidenceCenters centers) ηb r a r' a' hηb hr ha hr' ha' hrr haa hP har hcarrier hf hInv htrans hcJ hV hLV,
    retainedFrozenMatrixSymbol_unit_bounded (retainedIncidenceFamily T centers) G Q hQ hlow F row col Φ Y
      (retainedIncidenceCenters centers) ηb r a r' a' hηb hr hr' ha' haa hP har hcarrier hf hInv htrans hcJ,
    retainedFrozenMatrixSymbol_posSemidef (retainedIncidenceFamily T centers) Q hQ hlow F row col Φ Y
      (retainedIncidenceCenters centers) ηb r a r' a' hηb hr' ha', ?_⟩
  have hprojzero : projectedStress F 0 = cubeStress n := hproject.symm.trans hQzero
  obtain ⟨ε, hε, _, _, hbasis⟩ := exists_projectedStress_basis_neighborhood hn
  have hframe := (hbasis F 0 hF himm hrank (by simpa [hprojzero] using hε)).1
  let active (k : Euclidean n) : Finset (RetainedIncidenceChannel D centers) :=
    Finset.univ.filter fun i ↦ NormedSpace.normalize k ∈ ball i.1.1.1.2 (εcover i.1)
  let z (k : Euclidean n) (i : (RetainedIncidenceChannel D centers)) := D.roots i.1.1.1.1 i.2 (NormedSpace.normalize k)
  have hR : 0 < frozenFamilyHighFrequencyRadius (retainedIncidenceFamily T centers) G :=
    lt_of_lt_of_le zero_lt_one (one_le_frozenFamilyHighFrequencyRadius (retainedIncidenceFamily T centers) G)
  apply exists_retainedFrozenMatrixSymbol_unit_gap_of_incidence (retainedIncidenceFamily T centers) G Q hQ hlow F row col Φ Y
    (retainedIncidenceCenters centers) ηb r a r' a' hηb hr ha hr' ha' hrr haa hP har hcarrier hf hInv htrans hcJ hV hLV
    hgap active z
  · intro k hk i hi
    have hkn : 0 < ‖k‖ := hk.symm ▸ hR
    have hki : NormedSpace.normalize k ∈ ball i.1.1.1.2 (εcover i.1) :=
      (Finset.mem_filter.mp hi).2
    have hsec := (hD.2.2.2.2.1 i.1.1.1.1 i.2).2.2.1
      (NormedSpace.normalize k) (hdomain i.1 hki)
    have hsec₀ := (hD.2.2.2.2.1 i.1.1.1.1 i.2).2.2.1 i.1.1.1.2 i.1.1.2.2
    have hv : spectatorCenter (z k i) = spectatorCenter ((retainedIncidenceCenters centers) i) := by
      simp only [z, spectatorCenter, hsec.2.1, hsec.2.2.1, hsec₀.2.1, hsec₀.2.2.1]
    have hqne : NormedSpace.normalize k ≠ 0 :=
      norm_pos_iff.mp (by rw [NormedSpace.norm_normalize (norm_pos_iff.mp hkn)]; norm_num)
    have hw := retained_cube_incidence_positive_weight ((retainedIncidenceFamily T centers) i) ⟨Q, hQ, hlow i⟩ F
      (row i) (col i) (Φ i) (Y i) (hP i) (hηb i) (hr i) (hr' i) (ha' i)
      (hrr i) (haa i) (har i) (hcarrier i) (hf i) (hInv i) (htrans i) (hcJ i)
      (har' i) hQzero (hgap i) hF hrank hframe hsec.1
      (hseed i.1 _ hki i.2) hqne hsec.2.2.2 hv (hplateau i.1 _ hki i.2)
      (hnull i.1 _ hki i.2) (hcol i.1 _ hki i.2) hkn
      (by simpa only [NormedSpace.norm_smul_normalize] using
        (frozenHighFrequencyRadius_le_family (retainedIncidenceFamily T centers) G i).trans hk.ge)
    simpa only [NormedSpace.norm_smul_normalize] using hw
  · intro k hk s hi hzero
    have hkn : 0 < ‖k‖ := hk.symm ▸ hR
    have hq : NormedSpace.normalize k ∈ sphere (0 : Euclidean n) 1 := by
      simpa only [mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (norm_pos_iff.mp hkn)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hq)
    have himage : ActualCarriers.imageChannel (cubePencil (NormedSpace.normalize k)) s = 0 := by
      have hp : pencil (Q 0) (NormedSpace.normalize k) = ‖k‖⁻¹ • pencil (Q 0) k :=
        (pencilContinuousLinearMap (Q 0)).map_smul _ _
      have he : ActualCarriers.imageChannel (pencil (Q 0) (NormedSpace.normalize k)) s =
          ‖k‖⁻¹ • ActualCarriers.imageChannel (pencil (Q 0) k) s := by
        ext i
        simp [ActualCarriers.imageChannel, hp, Matrix.smul_mulVec]
      rw [hi, smul_zero] at he
      simpa only [hQzero, pencil_cubeStress] using he
    have hd (l : Fin (D.patchCount j.1.1.1)) :
        inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 l).toFun
          (D.roots j.1.1.1 l (NormedSpace.normalize k)))) s = 0 := by
      have hh := hzero ⟨j, l⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      simpa only [z, hseed j _ hj l, hQzero, quadratic_cubeStress,
        CubeCarrier.quadratic_eq_cubeQuadraticContraction] using hh
    have hbound := hgram j _ hj s
    simp only [himage, norm_zero, zero_pow (by decide : 2 ≠ 0), hd,
      Finset.sum_const_zero, add_zero] at hbound
    by_contra hs
    exact (not_lt_of_ge hbound) (mul_pos hD.1 (pow_pos (norm_pos_iff.mpr hs) 2))

end JanetCartan.ContinuumNormal.RetainedFrozen
