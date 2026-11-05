module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedProductSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.HistoryPhaseJets

/-!
# Sampled signed phases in the actual normalized source

The original whole-family signed band and closed angular set are applied to
one pair representing each sampled source. The same pair supplies its true
frequency. Joint phase jets give the normalized phase profile through the
convex short-chord estimate, with no inverse separation cost. The original
source cutoff, auxiliary cutoff, stress row and full tensor amplitudes remain.

The geometric producer is `exists_constructed_signed_geometry`, applied on the
same retained Hamilton family. `FamilyPhases` and the retained phase-profile
producers supply the joint jets; the sampling event supplies separation. Their
application on the initialized reference and the actual sampled-amplitude
profiles remain explicit obligations. This leaf proves the corrected angular
source contribution, not the full inverse's residual-chain decay or size.

Consumers: `UniformStep.SampledProduct`, `ProductProfiles`, and
`app:ch_pairs:prop:pairs-lag-sum`, Steps 1–3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open SignedPairs InnerProductSpace ResponseTransfer.RetainedFactors
variable {d : ℕ} {G : Type*}
local notation "E" => Euclidean (d+1)

/-- Joint jets of the original phase pay the mixed parameter derivative
before division by the true beat (`app:ch_pairs:setup:pairs-lag`). -/
private theorem normalized_pair_joint_jet_bound
    {Z : G → Set (Euclidean 3)} (hZ : ∀ g, Convex ℝ (Z g))
    (q : Pair G (Euclidean 3) Z) (Φ : G → E × Euclidean 3 → ℝ)
    (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g)) {L : ℝ} (hL : 1 ≤ L)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) (x : E)
    (hjoint : ∀ g z, z ∈ Z g → ∀ m,
      ‖iteratedFDeriv ℝ m (Φ g) (x,z)‖ ≤ P m * L^(m-2))
    (m : ℕ) :
    ‖iteratedFDeriv ℝ (m+1)
      (fun y ↦ q.vector (fun g z ↦ Φ g (y,z)) / q.beat) x‖ ≤
        (2 * (P (m+1)+P (m+2))) * L^m := by
  have hs g z : ContDiff ℝ ∞ (fun y : E ↦ Φ g (y,z)) :=
    (hΦ g).comp (contDiff_id.prodMk contDiff_const)
  apply (norm_iteratedFDeriv_normalized_signed_pair_phase_le hZ q
    (fun g z y ↦ Φ g (y,z))
    (fun g z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ (m+1)
      (fun y : E ↦ Φ g (y,w)) x) z)
    (add_nonneg (hP _) (hP _)) (zero_le_one.trans hL)
    (fun g z _ ↦ (hs g z).contDiffAt.of_le (by simp)) ?_ ?_ ?_).trans_eq
      (by rw [Nat.add_sub_cancel])
  · intro g z hz
    apply (primary_phase_spatial_jet_le_joint (Φ g) (hΦ g) x z (m+1)).trans
    apply (hjoint g z hz (m+1)).trans
    apply mul_le_mul (le_add_of_nonneg_right (hP _))
      (pow_le_pow_right₀ hL (by omega))
      (pow_nonneg (zero_le_one.trans hL) _) (add_nonneg (hP _) (hP _))
  · intro g z _
    exact ((contDiff_parameter_spatial_phase_jet (Φ g) (hΦ g) (m+1) x).differentiable
      (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  · intro g z hz
    apply (norm_parameter_spatial_phase_jet_le_joint (Φ g) (hΦ g) (m+1) x z).trans
    apply (hjoint g z hz (m+2)).trans
    simp only [show m+2-2=m by omega, Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hP _))
      (pow_nonneg (zero_le_one.trans hL) _)


open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization LocalSobolev
open RegularSector.Characteristic.RetardedLocalization
variable {N : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Apply the corrected normalized source to literal sampled sums and
separated differences. The original whole-family band, angular inclusion and
joint phase jets supply all normalized-phase hypotheses; no normalized pair
profile or individual discrepancy estimate is assumed. The same pair supplies
its phase and true beat, including the doubled plus diagonal. Constants precede
sample choices, source data and history (`app:ch_pairs:eq:pairs-lag-one-error`,
`app:ch_seed:eq:seed-actual-chord`). -/
theorem exists_normalized_sampled_source_discrepancy_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    {T : Set E} (hT : IsCompact T) (hTK : T ⊆ K) (hTneg : ∀ v ∈ T, -v ∈ T)
    {S : Set E} (hS : IsCompact S) (hScore : S ⊆ closedBall center f.physicalRadius)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hop : ∀ y ∈ S, output y = 1)
    {a b csep : ℝ} (ha : 0 < a) (hb : 0 < b) (hsepConst : 0 < csep)
    (Cscale : ℝ) (P X Y CQ C : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) (s : ℕ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ q : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set E), IsOpen U → S ⊆ U →
      ∀ (χ ψ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
        (Φ : G → E × Euclidean 3 → ℝ) (Z : G → Set (Euclidean 3))
        (R L sep : ℝ),
      (∀ g, Convex ℝ (Z g)) → (∀ g, ContDiff ℝ ∞ (Φ g)) →
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
      tsupport χ ⊆ S → 1 ≤ L → Rmin ≤ R → 0 < sep → sep ≤ 1 →
      csep * R^(-separationExponent) ≤ sep → L ≤ Cscale * R^(1+meanSlack) →
      (∀ y ∈ U, ∀ p : Pair G (Euclidean 3) Z,
        a*p.beat ≤ ‖p.vector (fun g z ↦ gradient (fun x ↦ Φ g (x,z)) y)‖ ∧
        ‖p.vector (fun g z ↦ gradient (fun x ↦ Φ g (x,z)) y)‖ ≤ b*p.beat) →
      closure (directionSet (fun y : U ↦ fun g z ↦
        gradient (fun x ↦ Φ g (x,z)) y) Z) ⊆ T →
      (∀ y ∈ S, ∀ g z, z ∈ Z g → ∀ m,
        ‖iteratedFDeriv ℝ m (Φ g) (y,z)‖ ≤ P m * L^(m-2)) →
      (∀ y ∈ U, ∀ m, ‖iteratedFDeriv ℝ m χ y‖ ≤ X m * L^m) →
      (∀ y ∈ U, ∀ m, ‖iteratedFDeriv ℝ m ψ y‖ ≤ Y m * L^m) →
      (∀ y ∈ U, ∀ m, ‖iteratedFDeriv ℝ m Q y‖ ≤ CQ m * L^m) →
      ∀ (group : ι → G) (z : ι → Euclidean 3), (∀ i, z i ∈ Z (group i)) →
      (∀ i j, i ≠ j → group i = group j → sep ≤ ‖z i-z j‖) →
      ∀ A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ,
      (∀ i, ContDiffOn ℝ ∞ (A i) U) →
      (∀ i y, y ∈ U → ∀ m, ‖iteratedFDeriv ℝ m (A i) y‖ ≤ C m * L^m) →
      ∀ (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let θ := fun i y ↦ R^carrierExponent * Φ (group i) (y,z i)
      let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
        (AmbientResponse.stressSource Q (fun x ↦ χ x •
          (if minus then ProductSum.minusSource θ A i j x else ProductSum.plusSource θ A i j x))) y)
      ∃ hg : MemLp g 2 volume,
        (∀ t : ℝ, t ≤ s →
          let e := (realSource f hK L₀ output ho.continuous hob - 1) (hg.toLp g)
          MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ∧
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ≤
            D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹) ∧
        ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W → ∀ Vout : Set E,
          let localError := localRealCompression hW Vout
            (pairedSource f hK L₀ output ho.continuous hob - 1)
            ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g)
          MemRestrictionSobolev Vout s localError ∧ restrictionSobolevNorm Vout s localError ≤
            D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹ := by
  let Ppair := fun m ↦ 2 * (P (m+1) + P (m+2))
  have hPpair m : 0 ≤ Ppair m := mul_nonneg (by norm_num) (add_nonneg (hP _) (hP _))
  obtain ⟨Rmin, hmin, htail⟩ := exists_normalized_product_source_discrepancy_constants
    (N := N) (ι := ι) f hK L₀ hL₀ hT hTK hTneg hS hScore output ho hoc hob hop
    ha hb hsepConst Cscale Ppair X Y CQ C hPpair hX hY hCQ hC s
  refine ⟨Rmin, hmin, fun q ↦ ?_⟩
  obtain ⟨D, hD, hsource⟩ := htail q
  refine ⟨D, hD, ?_⟩
  intro U hU hSU χ ψ Q Φ Z R L sep hZ hΦ hχ hψ hQ hχS hL hR hsep hsepOne
    hsepStage hslow hband hprotected hphase hχb hψb hQb group z hz hsample A hA hAb minus i j hdiag θ g
  have hRp : 0 < R := (by norm_num : (0 : ℝ) < 2).trans_le (hmin.trans hR)
  have hlam : 0 < R^carrierExponent := Real.rpow_pos_of_pos hRp _
  obtain ⟨p, hpsep, hp⟩ : (∃ p : Pair G (Euclidean 3) Z, sep ≤ p.beat ∧
      ∀ v : G → Euclidean 3 → ℝ,
        p.vector v = if minus then v (group i) (z i)-v (group j) (z j)
          else v (group i) (z i)+v (group j) (z j)) := by
    cases minus with
    | false =>
      obtain ⟨p, hpbeat, hp⟩ := sample_plus_represented_with_beat («E» := ℝ) group z hz i j
      exact ⟨p, hpbeat ▸ hsepOne, hp⟩
    | true =>
      obtain ⟨p, hpsep, _, _, hp⟩ := sample_minus_represented_with_beat
        («E» := ℝ) hsep hsepOne group z hz hsample (hdiag rfl)
      exact ⟨p, hpsep, hp⟩
  let φ := fun y ↦ p.vector (fun g z ↦ Φ g (y,z)) / p.beat
  have hφeq : (fun y ↦ (if minus then θ i y-θ j y else θ i y+θ j y) /
      (R^carrierExponent*p.beat)) = φ := by
    funext y
    dsimp only [φ, θ]
    rw [hp]
    cases minus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      field_simp
  have hs g z : ContDiff ℝ ∞ (fun y : E ↦ Φ g (y,z)) :=
    (hΦ g).comp (contDiff_id.prodMk contDiff_const)
  have hφ : ContDiff ℝ ∞ φ := by
    apply ContDiff.div_const
    cases p with
    | difference g z w hne => exact (hs g z).sub (hs g w)
    | sum g z w => exact (hs g z).add (hs g w)
    | cross g h hne z w s t hs' ht =>
      exact ((hs g z).const_smul s).add ((hs h w).const_smul t)
  have hgeometry y (hy : y ∈ U) :
      a ≤ ‖fderiv ℝ φ y‖ ∧ ‖fderiv ℝ φ y‖ ≤ b ∧
        NormedSpace.normalize (fderiv ℝ φ y) ∈ (toDual ℝ E) '' T := by
    apply normalized_signed_pair_phase_geometry p (fun g z y ↦ Φ g (y,z))
      (fun g z _ ↦ ((hs g z).differentiable (by simp)).differentiableAt) (hband y hy p)
    apply hprotected
    apply subset_closure
    exact ⟨⟨y,hy⟩, p, rfl⟩
  have hfrequency : csep*(R^carrierExponent*R^(-separationExponent)) ≤
      R^carrierExponent*p.beat := by
    calc
      _ = R^carrierExponent*(csep*R^(-separationExponent)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsepStage.trans hpsep) hlam.le
  have hnormalized := hsource U hU hSU χ ψ Q θ A minus i j hdiag R L
    (R^carrierExponent*p.beat)
  dsimp only at hnormalized
  rw [hφeq] at hnormalized
  exact hnormalized hχ hψ hQ hφ.contDiffOn (hA i) (hA j) hχS hL hR hfrequency hslow
    (fun y hy ↦ ⟨(hgeometry y hy).1, (hgeometry y hy).2.1⟩)
    (fun y hy ↦ (hgeometry y hy).2.2)
    (fun y hy m _ ↦ normalized_pair_joint_jet_bound hZ p Φ hΦ hL P hP y (hphase y hy) m)
    hχb hψb hQb (hAb i) (hAb j)

end JanetCartan.SignedProductEstimates
