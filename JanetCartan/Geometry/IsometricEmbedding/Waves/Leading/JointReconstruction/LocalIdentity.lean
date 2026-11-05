module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.JetFormula

/-!
# Local identification of the joint reconstruction jets

The formulas used for `app:ch_waves:eq:joint-tame` agree with the same actual
canonical completion and physical reconstruction on local charts. The proofs
need only the derivatives at the point in question. The final neighborhood
identities preserve every ambient derivative on the working closed product.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.LeadingWave.JointReconstruction

open GeometricProfile AmbientResponse

/-- The projected second-jet formula agrees with the physical second form
using only local `C²` regularity (`app:ch_waves:defn:geometry`). -/
theorem secondJetSecondForm_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (hi : Function.Injective (fderiv ℝ F x))
    (i j : Fin n) :
    secondJetSecondForm (secondJet F x) i j = secondFundamentalForm F x i j := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hF.fderiv_right (by norm_num)
  rw [secondJetSecondForm, secondJet, firstJetNormalProjection_eq hi,
    secondFundamentalForm_eq_normalProjection]
  congr 1
  unfold partialDeriv
  rw [fderiv_clm_apply (hd.differentiableAt (by norm_num)) (differentiableAt_const _)]
  simp

/-- The finite-jet normal map is the actual ambient normal map under local
`C²` regularity. This connects primitive normal-pairing gaps to the jet domain
in `app:ch_waves:eq:joint-tame`. -/
theorem secondJetNormalMap_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (hi : Function.Injective (fderiv ℝ F x)) :
    secondJetNormalMap (secondJet F x) = NormalRankStability.ambientNormalMap F x := by
  ext H : 1
  change (∑ i, ∑ j, H i j • secondJetSecondForm (secondJet F x) i j) =
    ∑ i, ∑ j, H i j • secondFundamentalForm F x i j
  simp_rw [secondJetSecondForm_eq_of_contDiffAt hF hi]

/-- The finite-jet ambient operator agrees with the actual operator on the
local chart (`app:ch_waves:eq:ambient-normal-inverse`). -/
theorem secondJetAmbientOperator_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (hi : Function.Injective (fderiv ℝ F x)) :
    secondJetAmbientOperator (secondJet F x) = ambientNormalOperator F x := by
  rw [secondJetAmbientOperator, secondJetNormalMap_eq_of_contDiffAt hF hi]
  have hp := firstJetNormalProjection_eq hi
  change firstJetNormalProjection (secondJet F x).1 = normalProjection F x at hp
  rw [hp]
  ext w : 1
  change _ + (w - normalProjection F x w) = _ + tangentProjection F x w
  rw [normalProjection_eq_sub_tangentProjection, sub_sub_cancel]
  rfl

/-- The jet inverse is the same actual canonical normal completion, with
local hypotheses only (`app:ch_waves:eq:ambient-normal-inverse`). -/
theorem secondJetNormalInverse_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    (secondJetNormalInverse (secondJet F x)).toLinearMap = canonicalNormalCompletion F x := by
  ext H : 1
  change Ring.inverse (secondJetAmbientOperator (secondJet F x))
    (secondJetNormalMap (secondJet F x) H) = _
  rw [secondJetAmbientOperator_eq_of_contDiffAt hF hi,
    secondJetNormalMap_eq_of_contDiffAt hF hi]
  exact (canonicalNormalCompletion_eq_ambient_inverse hrank H).symm

/-- The connection formula uses only the local second jet of the immersion
(`app:ch_waves:defn:geometry`). -/
theorem secondJetChristoffel_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (i j k : Fin n) :
    secondJetChristoffel (secondJet F x) i j k = christoffel F x i j k := by
  rw [christoffel_eq_hessian_contraction hF]
  unfold secondJetChristoffel secondJet partialDeriv
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hF.fderiv_right (by norm_num)
  rw [fderiv_clm_apply (hd.differentiableAt (by norm_num)) (differentiableAt_const _)]
  simp
  rfl

/-- The reconstruction strain is the actual symmetrized covariant derivative
at a local chart point (`app:ch_waves:eq:reconstruction`). -/
theorem reconstructionJetStrain_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (hu : DifferentiableAt ℝ u x) :
    reconstructionJetStrain (reconstructionJet F u x) = symmCovariantDeriv F u x := by
  have hd (i j : Fin n) : partialDeriv (fun y ↦ u y j) x i =
      (fderiv ℝ u x (EuclideanSpace.single i 1)) j := by
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hu.hasFDerivAt).fderiv)
  ext i j
  simp only [reconstructionJetStrain, reconstructionJet, symmCovariantDeriv, hd,
    secondJetChristoffel_eq_of_contDiffAt hF]

/-- The local reconstruction jet gives the literal ambient reconstruction
with the canonical completion (`app:ch_waves:eq:reconstruction`). -/
theorem reconstructionJetValue_eq_of_contDiffAt {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (hu : DifferentiableAt ℝ u x)
    (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    reconstructionJetValue (reconstructionJet F u x) =
      reconstruction F (canonicalNormalCompletion F) u x := by
  unfold reconstructionJetValue
  rw [reconstructionJetStrain_eq_of_contDiffAt hF hu]
  change tangentLift F u x + (secondJetNormalInverse (secondJet F x)).toLinearMap _ = _
  rw [secondJetNormalInverse_eq_of_contDiffAt hF hi hrank]
  rfl

/-- The principal-normal jet gives the same canonical principal normal at
each local chart point (`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem principalNormalValue_jointJet_eq {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} (b ξ : Euclidean n × Z → Euclidean n)
    {p : Euclidean n × Z} (hF : ContDiffAt ℝ 2 F p.1)
    (hi : Function.Injective (fderiv ℝ F p.1))
    (hrank : Set.range (normalMap F p.1) = (normalSpace F p.1 : Set (Euclidean N))) :
    principalNormalValue (jointJet F b ξ p) =
      principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p) := by
  exact LinearMap.congr_fun (secondJetNormalInverse_eq_of_contDiffAt hF hi hrank) _

/-- The principal-matrix jet gives the literal principal matrix at each
local chart point (`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem principalMatrixValue_jointJet_eq {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} (b ξ : Euclidean n × Z → Euclidean n)
    {p : Euclidean n × Z} (hF : ContDiffAt ℝ 2 F p.1)
    (hi : Function.Injective (fderiv ℝ F p.1))
    (hrank : Set.range (normalMap F p.1) = (normalSpace F p.1 : Set (Euclidean N))) :
    principalMatrixValue (jointJet F b ξ p) =
      principalMatrix (principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p))
        (ξ p) := by
  unfold principalMatrixValue
  rw [principalNormalValue_jointJet_eq b ξ hF hi hrank]
  rfl

/-- The reconstruction part of the joint jet uses exactly the physical slice
of the joint covector (`app:ch_waves:eq:reconstruction`). -/
theorem reconstructionValue_jointJet_eq {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b : Euclidean n × Z → Euclidean n}
    (ξ : Euclidean n × Z → Euclidean n) {p : Euclidean n × Z}
    (hF : ContDiffAt ℝ 2 F p.1) (hb : DifferentiableAt ℝ b p)
    (hi : Function.Injective (fderiv ℝ F p.1))
    (hrank : Set.range (normalMap F p.1) = (normalSpace F p.1 : Set (Euclidean N))) :
    reconstructionJetValue (jointJet F b ξ p).1 =
      reconstruction F (canonicalNormalCompletion F) (fun y ↦ b (y, p.2)) p.1 := by
  rw [jointJet_fst_eq F ξ hb]
  exact reconstructionJetValue_eq_of_contDiffAt hF
    (hb.comp p.1 (differentiableAt_id.prodMk (differentiableAt_const _))) hi hrank

/-- The joint-jet formulas agree near every point of the open product chart,
so all joint derivatives, including derivatives at a working closed-ball
boundary, agree (`app:ch_waves:eq:joint-tame`). No smoothness of `ξ` is needed
for these identities. -/
theorem jointJet_fields_eventuallyEq {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b : Euclidean n × Z → Euclidean n}
    (ξ : Euclidean n × Z → Euclidean n) {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F U)
    (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {p : Euclidean n × Z} (hp : p ∈ U ×ˢ V) :
    (principalNormalValue ∘ jointJet F b ξ) =ᶠ[𝓝 p]
      (fun q ↦ principalNormal (canonicalNormalCompletion F q.1) (ξ q) (b q)) ∧
    (fun q ↦ reconstructionJetValue (jointJet F b ξ q).1) =ᶠ[𝓝 p]
      (fun q ↦ reconstruction F (canonicalNormalCompletion F) (fun y ↦ b (y, q.2)) q.1) ∧
    (principalMatrixValue ∘ jointJet F b ξ) =ᶠ[𝓝 p]
      (fun q ↦ principalMatrix
        (principalNormal (canonicalNormalCompletion F q.1) (ξ q) (b q)) (ξ q)) := by
  have hmem : ∀ᶠ q in 𝓝 p, q ∈ U ×ˢ V := (hU.prod hV).mem_nhds hp
  have hF' (q : Euclidean n × Z) (hq : q ∈ U ×ˢ V) : ContDiffAt ℝ 2 F q.1 :=
    (hF.contDiffAt (hU.mem_nhds hq.1)).of_le (by simp)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hmem] with q hq
    exact principalNormalValue_jointJet_eq b ξ (hF' q hq) (hi _ hq.1) (hrank _ hq.1)
  · filter_upwards [hmem] with q hq
    exact reconstructionValue_jointJet_eq ξ (hF' q hq)
      ((hb.contDiffAt ((hU.prod hV).mem_nhds hq)).differentiableAt (by simp))
      (hi _ hq.1) (hrank _ hq.1)
  · filter_upwards [hmem] with q hq
    exact principalMatrixValue_jointJet_eq b ξ (hF' q hq) (hi _ hq.1) (hrank _ hq.1)

/-- The actual canonical reconstruction is jointly smooth in the physical
and parameter variables on the supplied open product chart. This is the
local regularity needed by `app:ch_waves:eq:joint-tame`; the covector is
differentiated in its physical variables by the original reconstruction. -/
theorem contDiffOn_joint_reconstruction_canonical {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {b : Euclidean n × Z → Euclidean n}
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞
      (fun p ↦ reconstruction F (canonicalNormalCompletion F) (fun y ↦ b (y, p.2)) p.1)
      (U ×ˢ V) := by
  have hjet := contDiffOn_jointJet hU hV hF hb (contDiffOn_const (c := (0 : Euclidean n)))
  intro p hp
  have hFp : ContDiffAt ℝ 2 F p.1 :=
    (hF.contDiffAt (hU.mem_nhds hp.1)).of_le (by simp)
  have hri : Set.range (secondJetNormalMap (secondJet F p.1)) =
      ((LinearMap.range (fderiv ℝ F p.1).toLinearMap)ᗮ : Set (Euclidean N)) := by
    rw [secondJetNormalMap_eq_of_contDiffAt hFp (hi _ hp.1)]
    exact hrank _ hp.1
  have hcoef := contDiffAt_reconstructionValue
    (q := jointJet F b (fun _ ↦ 0) p) (hi _ hp.1) hri
  have he := (jointJet_fields_eventuallyEq (fun _ ↦ 0) hU hV hF hb hi hrank hp).2.1
  exact ((hcoef.comp p (hjet.contDiffAt ((hU.prod hV).mem_nhds hp))).congr_of_eventuallyEq
    he.symm).contDiffWithinAt

end JanetCartan.LeadingWave.JointReconstruction
