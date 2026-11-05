module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.MatrixMultiplication

/-!
# Derivative envelope estimates from the root Sobolev profile

The reconstruction in `app:ch_response:eq:response-graded-displacement` consumes
one derivative of the reduced envelope, and its physical derivative in
`app:ch_response:eq:response-graded-derivative` consumes two. These estimates
derive every derivative bound from the root profile. The supplied L² jets must
satisfy the distributional recursion; they carry no quantitative assumptions.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- A finite ordered derivative loses exactly its length in Sobolev order,
with the Fourier normalization `(2π)^length`. This is the envelope derivative
step in `app:ch_response:eq:response-reconstruction-grading`. -/
theorem reconstructionJet_sobolev_bound (m : ℕ) (v : List (Fin d) → L2)
    (hv : ∀ is, is.length < m → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v is) (v (i :: is)))
    (is : List (Fin d)) (p : ℕ) (hpm : p + is.length ≤ m)
    (hu : MemFourierSobolev ((p + is.length : ℕ) : ℝ) (v [])) :
    MemFourierSobolev (p : ℝ) (v is) ∧
      fourierSobolevNorm (p : ℝ) (v is) ≤
        (2 * Real.pi) ^ is.length *
          fourierSobolevNorm ((p + is.length : ℕ) : ℝ) (v []) := by
  induction is generalizing p with
  | nil => simpa using And.intro hu (le_refl (fourierSobolevNorm (p : ℝ) (v [])))
  | cons i is ih =>
    have hm : p + 1 + is.length ≤ m := by simp only [List.length_cons] at hpm; omega
    have hu' : MemFourierSobolev ((p + 1 + is.length : ℕ) : ℝ) (v []) := by
      simpa only [List.length_cons, Nat.add_right_comm p 1 is.length, Nat.add_assoc] using hu
    obtain ⟨hmem, hnorm⟩ := ih (p + 1) hm hu'
    have hd := hv is (by simp only [List.length_cons] at hpm; omega) i
    have hmem' : MemFourierSobolev ((p : ℝ) + 1) (v is) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hmem
    refine ⟨hd.memFourierSobolev (by positivity) hmem', ?_⟩
    calc
      _ ≤ (2 * Real.pi) * fourierSobolevNorm ((p : ℝ) + 1) (v is) :=
        hd.fourierSobolevNorm_le (by positivity) hmem'
      _ ≤ (2 * Real.pi) * ((2 * Real.pi) ^ is.length *
          fourierSobolevNorm ((p + 1 + is.length : ℕ) : ℝ) (v [])) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using hnorm
      _ = _ := by
        simp only [List.length_cons, pow_succ]
        rw [show p + 1 + is.length = p + (is.length + 1) by omega]
        ring

/-- The derivative profile used by the actual reconstruction, obtained from
the root profile in `app:ch_response:eq:response-graded-reduced` (or the source
profile in `app:ch_response:eq:response-graded-source`). No derivative-envelope
estimate is an input. -/
theorem reconstructionJet_graded_bound (m : ℕ) (v : List (Fin d) → L2)
    (hv : ∀ is, is.length < m → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v is) (v (i :: is)))
    (B : ℕ → ℝ) {A K : ℝ}
    (hu : MemFourierSobolev (m : ℝ) (v []))
    (hub : ∀ p, p ≤ m → fourierSobolevNorm (p : ℝ) (v []) ≤ B p * A * K ^ p)
    (is : List (Fin d)) (p : ℕ) (hp : p + is.length ≤ m) :
    MemFourierSobolev (p : ℝ) (v is) ∧
      fourierSobolevNorm (p : ℝ) (v is) ≤
        ((2 * Real.pi) ^ is.length * B (p + is.length)) *
          (A * K ^ is.length) * K ^ p := by
  obtain ⟨hm, hb⟩ := reconstructionJet_sobolev_bound m v hv is p hp
    (hu.mono (by exact_mod_cast hp))
  refine ⟨hm, hb.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left (hub _ hp) (by positivity)).trans_eq
  rw [pow_add]
  ring

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Selecting the finite derivative coordinates needed by one term of
`app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionJetInput (v : J → List (Fin d) → L2) (w : J → List (Fin d)) :
    PiLp 2 (fun _ : J ↦ L2) := WithLp.toLp 2 (fun j ↦ v j (w j))

omit [Fintype I] in
/-- The root Hilbert profile bounds all selected derivative coordinates.
This supplies the input budget to the matrix multiplier, rather than assuming
it, for `app:ch_response:eq:response-graded-derivative`. -/
theorem reconstructionJetInput_graded_bound (m ℓ : ℕ)
    (v : J → List (Fin d) → L2) (w : J → List (Fin d)) (hw : ∀ j, (w j).length = ℓ)
    (hv : ∀ j is, is.length < m → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v j is) (v j (i :: is)))
    (B : ℕ → ℝ) {A K : ℝ}
    (hu : MemMatrixFourierSobolev (m : ℝ) (reconstructionJetInput v (fun _ ↦ [])))
    (hub : ∀ p, p ≤ m →
      matrixFourierSobolevNorm (p : ℝ) (reconstructionJetInput v (fun _ ↦ [])) ≤
        B p * A * K ^ p)
    (p : ℕ) (hp : p + ℓ ≤ m) :
    MemMatrixFourierSobolev (p : ℝ) (reconstructionJetInput v w) ∧
      matrixFourierSobolevNorm (p : ℝ) (reconstructionJetInput v w) ≤
        ((Fintype.card J : ℝ) * (2 * Real.pi) ^ ℓ * B (p + ℓ)) *
          (A * K ^ ℓ) * K ^ p := by
  have hj (j : J) := reconstructionJet_graded_bound m (v j) (hv j) B (hu j)
    (fun r hr ↦ (fourierSobolevNorm_coordinate_le _
      (reconstructionJetInput v (fun _ ↦ [])) j).trans (hub r hr))
    (w j) p (by rw [hw]; exact hp)
  refine ⟨fun j ↦ (hj j).1, (matrixFourierSobolevNorm_le_sum _ _).trans ?_⟩
  calc
    _ ≤ ∑ _j : J, ((2 * Real.pi) ^ ℓ * B (p + ℓ)) * (A * K ^ ℓ) * K ^ p := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [reconstructionJetInput, PiLp.toLp_apply, hw] using (hj j).2
    _ = _ := by simp; ring

/-- Real-order graded multiplication of an actual derivative envelope. Its
profile is derived entirely from the root Hilbert bounds. This is the analytic
term estimate for both `app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`; `ℓ` is respectively at most one
or two in those expansions. The constant has no dependence on `A`, `L`, or `K`. -/
theorem localizedMatrixJetProduct_graded_bound (k ℓ : ℕ) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k)
    (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (C B : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {A L K : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hbudget : ∀ i j r, r ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ r (c i j) x‖ ≤ C r * L ^ r)
    (v : J → List (Fin d) → L2) (w : J → List (Fin d)) (hw : ∀ j, (w j).length = ℓ)
    (hv : ∀ j is, is.length < k + ℓ → ∀ i,
      HasEuclideanL2CoordinateDerivative i (v j is) (v j (i :: is)))
    (hu : MemMatrixFourierSobolev ((k + ℓ : ℕ) : ℝ)
      (reconstructionJetInput v (fun _ ↦ [])))
    (hub : ∀ p, p ≤ k + ℓ →
      matrixFourierSobolevNorm (p : ℝ) (reconstructionJetInput v (fun _ ↦ [])) ≤
        B p * A * K ^ p) :
    let B' := fun p ↦ (Fintype.card J : ℝ) * (2 * Real.pi) ^ ℓ * B (p + ℓ)
    MemMatrixFourierSobolev s
        (localizedMatrixProduct c hc hcs (reconstructionJetInput v w)) ∧
      matrixFourierSobolevNorm s
        (localizedMatrixProduct c hc hcs (reconstructionJetInput v w)) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
          (C 0 * B' 0 + localizedMultiplierConstant d k *
            ∑ r ∈ Finset.range (k + 1), C (k - r) * B' r)) *
          (A * K ^ ℓ) * K ^ s := by
  dsimp only
  apply localizedMatrixProduct_graded_bound k hk hs hsk c hc hcs C
    (fun p ↦ (Fintype.card J : ℝ) * (2 * Real.pi) ^ ℓ * B (p + ℓ)) hC
    (fun p ↦ mul_nonneg (by positivity) (hB _))
    (mul_nonneg hA (pow_nonneg (by linarith) ℓ)) hL hLK hbudget
  · exact (reconstructionJetInput_graded_bound (k + ℓ) ℓ v w hw hv B hu hub k le_rfl).1
  · intro p hp
    exact (reconstructionJetInput_graded_bound (k + ℓ) ℓ v w hw hv B hu hub p
      (by omega)).2

omit [Fintype I] in
/-- The multiplier on supplied jets is the literal classical derivative
product almost everywhere. The separate smooth-jet producer must discharge the
representation premises when assembling
`app:ch_response:eq:response-graded-displacement` and its physical derivative. -/
theorem localizedMatrixJetProduct_ae (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (v : J → List (Fin d) → L2) (w : J → List (Fin d)) (f : J → E → ℂ)
    (hrep : ∀ j, v j (w j) =ᵐ[volume]
      JanetCartan.AmplitudeBound.euclideanCoordinateDerivList (w j) (f j)) (i : I) :
    localizedMatrixProduct c hc hcs (reconstructionJetInput v w) i =ᵐ[volume]
      fun x ↦ ∑ j, c i j x *
        JanetCartan.AmplitudeBound.euclideanCoordinateDerivList (w j) (f j) x := by
  filter_upwards [localizedMatrixProduct_ae c hc hcs (reconstructionJetInput v w) i,
    ae_all_iff.mpr hrep] with x hx hvx
  exact hx.trans (Finset.sum_congr rfl fun j _ ↦ congrArg (c i j x * ·) (hvx j))

end JanetCartan.IsometricEmbedding.Reconstruction
