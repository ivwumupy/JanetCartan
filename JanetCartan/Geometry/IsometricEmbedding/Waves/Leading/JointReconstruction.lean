module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.CompactRange
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.Estimates

/-!
# Local joint reconstruction for the leading wave

The finite-jet connection for `app:ch_waves:eq:joint-tame` uses the same
canonical normal completion, principal normal, and reconstruction as the
leading-wave construction. The imported results prove coefficient smoothness,
local formula identities, neighborhood equality of the actual joint fields,
and joint smoothness of the physical reconstruction.

The uniform compact range is derived from a fixed C4 bound and separate
metric-energy and normal-pairing gaps. The resulting joint bounds have losses
two, one and zero for the immersion, transported covector and phase covector,
respectively, and contain only a sum of single high norms. All orders use the
same working product, and the constants precede the varying charts and fields.

The leading-wave parent must instantiate the primitive geometry from
`CurrentGeometricNeighborhood.exists_geometric_neighborhood`, the transported
covector from `NullTransport`, and the phase covector from `SharpPhaseBounds`
and `ConstructedCarrierJets`. This deduction does not construct those inputs
or assert completion of the leading-wave theorem.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.LeadingWave.JointReconstruction

open GeometricProfile AmbientResponse

private theorem norm_secondJet_le_cNorm_four {n N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) {F : Euclidean n → Euclidean N}
    (hF : ∀ x ∈ K, ContDiffAt ℝ 4 F x) {x : Euclidean n} (hx : x ∈ K) :
    ‖secondJet F x‖ ≤ cNorm K 4 F := by
  change max ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ _
  apply max_le
  · have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hF hx (by omega : 1 ≤ 4)
    simpa only [norm_iteratedFDeriv_one] using h
  · have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hF hx (by omega : 2 ≤ 4)
    simpa only [show 2 = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using h

/-- The reconstruction part of `app:ch_waves:eq:joint-tame` from primitive
local geometry. A fixed C4 bound and the separate positive metric-energy and
normal-pairing gaps produce the common compact second-jet range; fixed joint
C1 bounds produce its covector factors. Compact containment and estimates of
the reconstructed fields are conclusions, not inputs.

The actual principal normal, reconstruction and principal matrix have one
high norm of each input, with fixed losses two, one and zero. The constant
family is chosen before the varying open charts and fields; no global
smoothness, parameter-dependent constant, frequency or accuracy is required.
The leading-wave parent retains the actual geometry, transport and phase
instantiations described in the module docstring. -/
theorem exists_cNorm_joint_reconstruction_le_of_primitive_bounds
    {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {M γ κ : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hκ : 0 < κ) (B : ℝ) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (U : Set (Euclidean n)) (V : Set Z), IsOpen U → IsOpen V →
      Metric.closedBall a.1 ρ ⊆ U → Metric.closedBall a.2 ρ ⊆ V →
      ∀ (F : Euclidean n → Euclidean N) (b ξ : Euclidean n × Z → Euclidean n),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞ b (U ×ˢ V) → ContDiffOn ℝ ∞ ξ (U ×ˢ V) →
      cNorm (Metric.closedBall a.1 ρ) 4 F ≤ M →
      (∀ x ∈ Metric.closedBall a.1 ρ, ∀ v,
        γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Metric.closedBall a.1 ρ, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (Metric.closedBall a ρ) 1 b ≤ B → cNorm (Metric.closedBall a ρ) 1 ξ ≤ B →
      ∀ r : ℕ,
      cNorm (Metric.closedBall a ρ) r
          (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) +
        cNorm (Metric.closedBall a ρ) r
          (fun p ↦ reconstruction F (canonicalNormalCompletion F) (fun y ↦ b (y, p.2)) p.1) +
        cNorm (Metric.closedBall a ρ) r
          (fun p ↦ principalMatrix
            (principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) (ξ p)) ≤
        C r * (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
          cNorm (Metric.closedBall a ρ) (r + 1) b + cNorm (Metric.closedBall a ρ) r ξ) := by
  obtain ⟨T, hT, hTi, hTr, hmem⟩ :=
    exists_compact_secondJet_range (n := n) (N := N) hM hγ hκ
  choose C hC hbound using fun r ↦
    exists_cNorm_joint_reconstruction_le_of_compact_range a hρ hT hTi hTr B r
  refine ⟨C, hC, ?_⟩
  intro U V hU hV hKU hKV F b ξ hF hi hrank hb hξ hFM hmetric hnormal hbB hξB r
  apply hbound r U V hU hV hKU hKV F b ξ hF hi hrank hb hξ _ hbB hξB
  intro x hx
  have hFat (y) (hy : y ∈ Metric.closedBall a.1 ρ) :=
    hF.contDiffAt (hU.mem_nhds (hKU hy))
  exact hmem F x ((hFat x hx).of_le (by simp)) (hi x (hKU hx)) (hrank x (hKU hx))
    ((norm_secondJet_le_cNorm_four (isCompact_closedBall ..)
      (fun y hy ↦ (hFat y hy).of_le (by simp)) hx).trans hFM)
    (hmetric x hx) (hnormal x hx)

end JanetCartan.LeadingWave.JointReconstruction
