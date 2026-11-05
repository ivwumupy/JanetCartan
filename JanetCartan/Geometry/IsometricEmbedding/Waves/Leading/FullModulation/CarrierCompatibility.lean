module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.CarrierCompatibility.Amplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.CarrierCompatibility.Buffers

/-!
# The full transport extension retains the actual carrier amplitude

For `app:ch_waves:thm:leading`, ODE uniqueness identifies the two supplied
forward flows on the carrier graph; their individual inverse identities then
identify their footpoints. The literal characteristic integrals therefore
agree for every prescribed initial scalar, and so do their null amplitudes.

`compatibility_on_common_buffer` deduces the common trajectory containments
from speed bounds. Choose its constants BEFORE the immersion:

* `exists_local_carrierLabel_lipschitz` produces `Rg,L` from the frozen
  reference at a point of the original closed carrier cube.
* `exists_comparison_radii` produces `r,δ` from `Rc,Rf,Rg,τc,τf,M,L` alone.
* The original carrier producer is
  `NullTransport.exists_projected_local_positive_amplitude`; the full
  modulation transport producer must supply the corresponding full maps.
  They must use the same `T,Q,F,row,col`. The parent instantiates their own
  initial, velocity and inverse identities, covered cylinders, and the
  fixed coefficient speed/Lipschitz bounds on the larger domains.

These are conditional comparison theorems, not a new transport existence
claim. The parent leading-wave construction retains simultaneous instantiation
of the two actual constructors. No equality of their maps or amplitudes is
an input. No Hamilton family is reconstructed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius NNReal

namespace JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Compatibility on a common smaller cylinder, with all trajectory range
obligations discharged by fixed velocity and graph bounds. The two own-flow
inverse identities suffice; neither equality of maps nor equality of
amplitudes is assumed. This is the quantitative comparison consumed by the
parent leading-wave assembly (`app:ch_waves:thm:leading`). -/
theorem compatibility_on_common_buffer
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc Rf Rg τc τf M r δ : ℝ} {L K : ℝ≥0}
    (hRc : 0 < Rc) (hRf : 0 < Rf) (hr : 0 < r) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hL : 1 ≤ (L : ℝ))
    (hδc : δ ≤ τc) (hδf : δ ≤ τf)
    (hrc : 8 * r ≤ Rc / 32) (hrf : 8 * (L : ℝ) * r ≤ Rf / 32)
    (hMδ : M * δ ≤ r) (hrg : 3 * r ≤ Rg)
    (hg : LipschitzOnWith L (carrierLabel T) (closedBall p₀ Rg))
    {φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))}
    {Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    {Df : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))))}
    (hcoverc : Ioo (-τc) τc ×ˢ ball p₀ (Rc / 32) ⊆ Dc)
    (hcoverf : Ioo (-τf) τf ×ˢ ball (carrierLabel T p₀) (Rf / 32) ⊆ Df)
    (hy : ∀ q ∈ Dc, y q ∈ ball p₀ (Rc / 8))
    (hφy : ∀ q ∈ Dc, φ (q.1, y q) = q.2)
    (hYΦ : ∀ p ∈ ball (carrierLabel T p₀) (Rf / 8), ∀ t ∈ Ioo (-τf) τf,
      Y (t, Φ (t, p)) = p)
    (hi : ∀ p ∈ ball p₀ (Rc / 8), φ (0, p) = p)
    (hI : ∀ p ∈ ball (carrierLabel T p₀) (Rf / 8), Φ (0, p) = p)
    (hd : ∀ p ∈ ball p₀ (Rc / 8), ∀ t ∈ Ioo (-τc) τc,
      HasDerivAt (fun s ↦ φ (s, p)) (carrierVelocity T Q row col t (φ (t, p))) t)
    (hD : ∀ p ∈ ball (carrierLabel T p₀) (Rf / 8), ∀ t ∈ Ioo (-τf) τf,
      HasDerivAt (fun s ↦ Φ (s, p)) (fullVelocity T Q row col t (Φ (t, p))) t)
    (hv : ∀ p ∈ ball p₀ (Rc / 8), ∀ t ∈ Ioo (-τc) τc,
      ‖carrierVelocity T Q row col t (φ (t, p))‖ ≤ M)
    (hV : ∀ p ∈ ball (carrierLabel T p₀) (Rf / 8), ∀ t ∈ Ioo (-τf) τf,
      ‖fullVelocity T Q row col t (Φ (t, p))‖ ≤ M)
    (hlip : ∀ t ∈ Ioo (-δ) δ, LipschitzOnWith K (fullVelocity T Q row col t)
      (closedBall (carrierLabel T p₀) (Rf / 2))) :
    ∀ q ∈ Ioo (-δ) δ ×ˢ ball p₀ r,
      q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ Df ∧
      (∀ t ∈ Ioo (-δ) δ,
        Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
      Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
      ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w ∧
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) •
            nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w := by
  have hb := common_trajectory_buffers hRc hRf hr hδ hM hL hδc hδf hrc hrf hMδ hrg hg
    hcoverc hcoverf hy hφy hi hI hd hD hv hV
  have htC {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-τc) τc := by
    constructor <;> linarith [ht.1, ht.2]
  have htF {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-τf) τf := by
    constructor <;> linarith [ht.1, ht.2]
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  intro q hq
  obtain ⟨hqc, hqf, _, hypf, htraj⟩ := hb q hq
  have hypc := hy q hqc
  have hdf := fun t ht ↦ hD _ hypf t (htF ht)
  have hdc := fun t ht ↦ hd _ hypc t (htC ht)
  have hrangef := fun t ht ↦ (htraj t ht).2
  have hrangec := fun t ht ↦ (htraj t ht).1
  refine ⟨hqc, hqf,
    forward_eq_on_carrier T Q row col h0 hlip (hI _ hypf) (hi _ hypc)
      hdf hdc hrangef hrangec, ?_⟩
  exact amplitudes_eq_on_carrier T Q F row col h0 hq.1 hlip (hI _ hypf) (hi _ hypc)
    hdf hdc hrangef hrangec (hYΦ _ hypf q.1 (htF hq.1)) (hφy q hqc)

end JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
