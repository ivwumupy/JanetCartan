module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Reconstruction

/-!
# The actual reconstruction as a joint jet formula

The formula in `app:ch_waves:eq:reconstruction` uses the second jet of the
immersion and the value and first derivative of the covector field.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius

namespace JanetCartan.GeometricProfile

/-- The finite joint jet used in `app:ch_waves:eq:reconstruction`. -/
abbrev ReconstructionJet (n N : ℕ) :=
  SecondJet (Euclidean n) (Euclidean N) ×
    (Euclidean n × (Euclidean n →L[ℝ] Euclidean n))

/-- The actual joint jet for `app:ch_waves:eq:reconstruction`. -/
def reconstructionJet {n N : ℕ} (f : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (x : Euclidean n) : ReconstructionJet n N :=
  (secondJet f x, u x, fderiv ℝ u x)

private def matrixEntry {n : ℕ} (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))

private def tensorOfEntries (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

/-- `app:ch_waves:defn:geometry`: the actual induced Christoffel formula
as a function of the second jet. -/
def secondJetChristoffel {n N : ℕ} (J : SecondJet (Euclidean n) (Euclidean N))
    (i j k : Fin n) : ℝ :=
  ∑ l, (firstJetMetric J.1)⁻¹ k l *
    inner ℝ (J.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (J.1 (EuclideanSpace.single l 1))

/-- `app:ch_waves:eq:reconstruction`: the symmetrized covariant derivative
as a joint jet formula, including the actual Christoffel terms. -/
def reconstructionJetStrain {n N : ℕ} (q : ReconstructionJet n N) : MetricTensor n :=
  fun i j ↦ ((q.2.2 (EuclideanSpace.single i 1)) j +
    (q.2.2 (EuclideanSpace.single j 1)) i) / 2 -
    ∑ k, secondJetChristoffel q.1 i j k * q.2.1 k

/-- `app:ch_waves:eq:reconstruction`: raising the covector and applying
the differential, followed by the actual ambient normal inverse. -/
def reconstructionJetValue {n N : ℕ} (q : ReconstructionJet n N) : Euclidean N :=
  (∑ i, ∑ j, ((firstJetMetric q.1.1)⁻¹ i j * q.2.1 j) •
    q.1.1 (EuclideanSpace.single i 1)) +
    secondJetNormalInverse q.1 (reconstructionJetStrain q)

/-- `app:ch_waves:eq:reconstruction`: smoothness of the induced connection
coefficient on the immersive jet domain. -/
theorem contDiffAt_secondJetChristoffel {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : IsUnit (firstJetMetric J.1))
    (i j k : Fin n) : ContDiffAt ℝ ∞ (fun K ↦ secondJetChristoffel K i j k) J := by
  apply ContDiffAt.sum
  intro l _
  exact ((matrixEntry k l).contDiff.contDiffAt.comp J
    ((contDiffAt_firstJetMetric_inv hJ).comp J contDiffAt_fst)).mul
      (((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply contDiffAt_const).inner ℝ
        (contDiffAt_fst.clm_apply contDiffAt_const))

/-- `app:ch_waves:eq:reconstruction`: smoothness of the full reconstruction
coefficient follows from the proved inverse, with no completion hypothesis. -/
theorem contDiffAt_reconstructionJetValue {n N : ℕ} {q : ReconstructionJet n N}
    (hi : Function.Injective q.1.1)
    (hrank : Set.range (secondJetNormalMap q.1) =
      ((LinearMap.range q.1.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    ContDiffAt ℝ ∞ (@reconstructionJetValue n N) q := by
  have hJ := firstJetMetric_isUnit_of_injective hi
  have hc (i : Fin n) : ContDiffAt ℝ ∞ (fun p : ReconstructionJet n N ↦ p.2.1 i) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp q contDiffAt_snd.fst
  have hd (i j : Fin n) :
      ContDiffAt ℝ ∞ (fun p : ReconstructionJet n N ↦
        (p.2.2 (EuclideanSpace.single i 1)) j) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp q
      (contDiffAt_snd.snd.clm_apply contDiffAt_const)
  have hs : ContDiffAt ℝ ∞ (@reconstructionJetStrain n N) q := by
    apply (tensorOfEntries n).contDiff.contDiffAt.comp q
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact ((hd i j).add (hd j i) |>.div_const 2).sub (ContDiffAt.sum fun k _ ↦
      ((contDiffAt_secondJetChristoffel hJ i j k).comp q contDiffAt_fst).mul (hc k))
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (((matrixEntry i j).contDiff.contDiffAt.comp q
      ((contDiffAt_firstJetMetric_inv hJ).comp q contDiffAt_fst.fst)).mul (hc j)).smul
        (contDiffAt_fst.fst.clm_apply contDiffAt_const)
  · exact ((contDiffAt_secondJetNormalInverse hJ
      (secondJetAmbientOperator_isUnit hi hrank)).comp q contDiffAt_fst).clm_apply hs

/-- `app:ch_waves:defn:geometry`: the connection jet formula is the induced
Levi-Civita connection of the map. -/
theorem secondJetChristoffel_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) (x : Euclidean n) (i j k : Fin n) :
    secondJetChristoffel (secondJet f x) i j k = christoffel f x i j k := by
  rw [christoffel_eq_hessian_contraction
    (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt]
  unfold secondJetChristoffel secondJet partialDeriv
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hd.differentiable (by simp)).differentiableAt
    (differentiableAt_const _)]
  simp
  rfl

/-- `app:ch_waves:eq:reconstruction`: the jet strain is the actual covariant
strain; coordinate evaluation commutes with differentiation. -/
theorem reconstructionJetStrain_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {u : Euclidean n → Euclidean n} (hu : ContDiff ℝ ∞ u)
    (x : Euclidean n) :
    reconstructionJetStrain (reconstructionJet f u x) = symmCovariantDeriv f u x := by
  have hd (i j : Fin n) : partialDeriv (fun y ↦ u y j) x i =
      (fderiv ℝ u x (EuclideanSpace.single i 1)) j := by
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x
        (hu.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv)
  ext i j
  simp only [reconstructionJetStrain, reconstructionJet, symmCovariantDeriv,
    hd, secondJetChristoffel_eq hf]

/-- `app:ch_waves:eq:reconstruction`: identifies the completion map in
`LeadingWave.reconstruction` with the constructed inverse of the actual second form. -/
theorem reconstructionJetValue_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {u : Euclidean n → Euclidean n} (hu : ContDiff ℝ ∞ u)
    {x : Euclidean n} (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N))) :
    reconstructionJetValue (reconstructionJet f u x) =
      LeadingWave.reconstruction f (AmbientResponse.canonicalNormalCompletion f) u x := by
  unfold reconstructionJetValue
  rw [reconstructionJetStrain_eq hf hu]
  change tangentLift f u x + (secondJetNormalInverse (secondJet f x)).toLinearMap _ = _
  rw [secondJetNormalInverse_eq_canonicalNormalCompletion hf hi hrank]
  rfl

end JanetCartan.GeometricProfile
