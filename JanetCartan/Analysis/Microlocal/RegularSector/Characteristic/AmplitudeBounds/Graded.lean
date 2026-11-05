module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PrimitiveAssembly

/-!
# Graded estimates for the same literal characteristic amplitudes

Primitive profiles `G j * T^(j-R₀)` give amplitude profiles with the fixed
loss nine in `R₀`. Natural subtraction denotes the nonnegative part. The
profiles themselves supply every low-order bound used in the construction;
constants precede the scale and all primitive functions. These are the
local graded inputs for `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds
variable {n d : ℕ}

/-- Primitive profiles alone imply the graded estimates for the actual datum,
potential, signed row, real columns, and complex Frobenius matrices. Fixed
primitive C9 bounds follow at order nine from `R₀≥9`; no separate low
amplitude or primitive budget is assumed. The reserve nine is independent of
output order (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_pencilPrimitiveAmplitudes_graded_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (t₀ : ℝ) (p x : Euclidean d × Euclidean d) (xQ : Euclidean n)
    {ρ ρo σ R τ S L F RQ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hτ : 0 < τ)
    (hρo : ρ < ρo) (hσR : σ < R) (hτS : τ < S)
    (hρoS : ρo ≤ S) (hRL : R < L) (hRF : 2 * R ≤ F)
    (hRQ : 0 < RQ) (r c : Fin n)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hrootImage : MapsTo (rootPhysicalPosition e)
      (closedBall (t₀, p) L) (closedBall xQ RQ))
    (hphysicalImage : MapsTo (PhysicalAction.physicalPosition e)
      (closedBall (t₀, (t₀, x)) S) (closedBall xQ RQ))
    (G : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) {R₀ : ℕ} (hR₀ : 9 ≤ R₀) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (T : ℝ), 1 ≤ T →
      ∀ (Ω : Set (Euclidean n)) (D : Set (RootState (Euclidean d)))
        (V : Set (TwoTimePoint (Euclidean d))) (W : Set (RootState (Euclidean d) × ℝ)),
        IsOpen Ω → IsOpen D → IsOpen V → IsOpen W →
        closedBall xQ RQ ⊆ Ω → closedBall (t₀, p) L ⊆ D →
        closedBall (t₀, (t₀, x)) S ⊆ V → closedBall ((t₀, p), 0) F ⊆ W →
        MapsTo (rootPhysicalPosition e) D Ω → MapsTo (PhysicalAction.physicalPosition e) V Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
          (h mask : RootState (Euclidean d) → ℝ)
          (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          ContDiffOn ℝ ∞ h D → ContDiffOn ℝ ∞ mask D →
          ContDiffOn ℝ ∞ Φ W → ContDiffOn ℝ ∞ C.symm V →
          (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ →
          MapsTo (twoTimeFlowInput ∘ C.symm) V W →
          MapsTo (twoTimeFlowInput ∘ C.symm) (closedBall (t₀, (t₀, x)) S)
            (closedBall ((t₀, p), 0) F) →
          MapsTo (fun y ↦ twoTimeState Φ (C.symm y)) V D →
          MapsTo (fun y ↦ twoTimeState Φ (C.symm y)) (closedBall (t₀, (t₀, x)) S)
            (closedBall (t₀, p) L) →
          MapsTo C (closedBall (t₀, (t₀, p)) σ) (closedBall (t₀, (t₀, x)) τ) →
          MapsTo C (ball (t₀, (t₀, p)) R) (ball (t₀, (t₀, x)) S) →
          MapsTo C.symm (closedBall (t₀, (t₀, x)) ρ) (closedBall (t₀, (t₀, p)) σ) →
          MapsTo C.symm (ball (t₀, (t₀, x)) ρo) (ball (t₀, (t₀, p)) R) →
          ball (t₀, (t₀, x)) ρo ⊆ C.target →
          (∀ j, cNorm (closedBall xQ RQ) j Q ≤ G j * T ^ (j - R₀)) →
          (∀ j, cNorm (closedBall xQ RQ) j B ≤ G j * T ^ (j - R₀)) →
          (∀ j, cNorm (closedBall (t₀, p) L) j h ≤ G j * T ^ (j - R₀)) →
          (∀ j, cNorm (closedBall (t₀, p) L) j mask ≤ G j * T ^ (j - R₀)) →
          (∀ j, cNorm (closedBall ((t₀, p), 0) F) j Φ ≤ G j * T ^ (j - R₀)) →
          (∀ j, cNorm (closedBall (t₀, (t₀, x)) S) j C.symm ≤ G j * T ^ (j - R₀)) →
          (∀ w ∈ closedBall (t₀, p) L, (rootPencil e Q h w).det = 0 ∧
            μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) →
          ContDiffOn ℝ ∞ (pencilSignedDatum e Q h r c mask) (ball (t₀, p) L) ∧
          ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) (ball (t₀, (t₀, x)) S) ∧
          ContDiffOn ℝ ∞ (pencilSignedRow e Q B h Φ C r c mask) (ball (t₀, (t₀, x)) ρo) ∧
          (∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c mask j)
              (ball (t₀, (t₀, x)) ρo) ∧
            ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c mask j)
              (ball (t₀, (t₀, x)) ρo) ∧
            ContDiffOn ℝ ∞ (adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c mask j))
              (ball (t₀, (t₀, x)) ρo)) ∧
          ∀ m,
            cNorm (closedBall (t₀, p) L) m (pencilSignedDatum e Q h r c mask) ≤ A m * T ^ (m - (R₀ - 9)) ∧
            cNorm (closedBall (t₀, (t₀, x)) S) m (pencilTransportPotential e Q B h Φ C r c) ≤
              A m * T ^ (m - (R₀ - 9)) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m (pencilSignedRow e Q B h Φ C r c mask) ≤
              A m * T ^ (m - (R₀ - 9)) ∧
            (∀ j, cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilLeadingColumn e Q B h Φ C r c mask j) ≤ A m * T ^ (m - (R₀ - 9)) ∧
              cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilCorrectionColumn e Q B h Φ C r c mask j) ≤ A m * T ^ (m - (R₀ - 9)) ∧
              cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c mask j)) ≤
                  A m * T ^ (m - (R₀ - 9))) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilLeadingComplexMatrix e Q B h Φ C r c mask) ≤ A m * T ^ (m - (R₀ - 9)) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilCorrectionComplexMatrix e Q B h Φ C r c mask) ≤ A m * T ^ (m - (R₀ - 9)) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilCorrectionResidualComplexMatrix e Q B h Φ C r c mask) ≤ A m * T ^ (m - (R₀ - 9)) := by
  obtain ⟨A, hA, hb⟩ := exists_pencilPrimitiveAmplitudes_cNorm_bounds e t₀ p x xQ
    hρ hσ hτ hρo hσR hτS hρoS hRL hRF hRQ (hG 9) r c hμ hν hrootImage hphysicalImage
  refine ⟨fun m ↦ A m * (1 + 6 * G (m + 9)),
    fun m ↦ mul_pos (hA m) (by linarith [hG (m + 9)]), ?_⟩
  intro T hT Ω D V W hΩ hD hV hW hKQ hKz hKC hKΦ hrootPhys hphys
    Q B h mask Φ C hQ hB hh hmask hΦ hCi hC hflow hflowK hstate hstateK
    hforwardK hforward hinverseK hinverse htarget hQG hBG hhG hmG hΦG hCiG hgaps
  have hlo : T ^ (9 - R₀) = 1 := by rw [Nat.sub_eq_zero_of_le hR₀, pow_zero]
  obtain ⟨hdatum, hpot, hrow, hsmooth, hbound⟩ := hb Ω D V W hΩ hD hV hW hKQ hKz hKC hKΦ
    hrootPhys hphys Q B h mask Φ C hQ hB hh hmask hΦ hCi hC hflow hflowK hstate hstateK
    hforwardK hforward hinverseK hinverse htarget
    (by simpa only [hlo, mul_one] using hQG 9)
    (by simpa only [hlo, mul_one] using hBG 9)
    (by simpa only [hlo, mul_one] using hhG 9)
    (by simpa only [hlo, mul_one] using hmG 9)
    (by simpa only [hlo, mul_one] using hΦG 9)
    (by simpa only [hlo, mul_one] using hCiG 9) hgaps
  refine ⟨hdatum, hpot, hrow, hsmooth, ?_⟩
  intro m
  have he : m + 9 - R₀ = m - (R₀ - 9) := by omega
  have hpow : 1 ≤ T ^ (m + 9 - R₀) := one_le_pow₀ hT
  have hsum : pencilPrimitiveNorm (closedBall xQ RQ) (closedBall (t₀, p) L)
      (closedBall ((t₀, p), 0) F) (closedBall (t₀, (t₀, x)) S) Q B h mask Φ C.symm (m + 9) ≤
        (1 + 6 * G (m + 9)) * T ^ (m - (R₀ - 9)) := by
    rw [← he]
    dsimp [pencilPrimitiveNorm]
    nlinarith only [hpow, hQG (m + 9), hBG (m + 9), hhG (m + 9), hmG (m + 9),
      hΦG (m + 9), hCiG (m + 9)]
  have hmajor := mul_le_mul_of_nonneg_left hsum (hA m).le
  rw [← mul_assoc] at hmajor
  have hout := hbound m
  exact ⟨hout.1.trans hmajor, hout.2.1.trans hmajor, hout.2.2.1.trans hmajor,
    fun j ↦ ⟨(hout.2.2.2.1 j).1.trans hmajor, (hout.2.2.2.1 j).2.1.trans hmajor,
      (hout.2.2.2.1 j).2.2.trans hmajor⟩,
    hout.2.2.2.2.1.trans hmajor, hout.2.2.2.2.2.1.trans hmajor,
    hout.2.2.2.2.2.2.trans hmajor⟩

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
