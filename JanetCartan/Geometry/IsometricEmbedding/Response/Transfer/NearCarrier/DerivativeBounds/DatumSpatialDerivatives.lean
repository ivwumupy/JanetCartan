module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.SobolevAssembly

/-!
# Actual spatial derivatives of the datum

The spatial part of the mixed datum construction needed by
`app:ch_response:eq:direct-envelope-profile`. Derivative representatives are
constructed from the published Euclidean Fourier Sobolev characterization.
The ordered-word operation is reused, and each spatial derivative retains
its physical `2π` factor. No mixed datum estimate is an input.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d : ℕ}
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Canonical actual coordinate derivative of an `H¹` datum, for the mixed
datum construction in `app:ch_response:eq:direct-envelope-profile`. Its value
outside `H¹` is irrelevant; every derivative theorem requires membership. -/
def datumSpatialDerivative (i : Fin d) (f : L2) : L2 := by
  classical
  exact if h : MemFourierSobolev (0 + 1 : ℝ) f then
    (h.exists_coordinateDerivative (by norm_num) i).choose
  else 0

/-- The representative constructed for
`app:ch_response:eq:direct-envelope-profile` is the actual distributional
coordinate derivative, with literal Lebesgue measure. -/
theorem datumSpatialDerivative_hasDerivative (i : Fin d) (f : L2)
    (hf : MemFourierSobolev 1 f) :
    HasEuclideanL2CoordinateDerivative i f (datumSpatialDerivative i f) := by
  have h : MemFourierSobolev (0 + 1 : ℝ) f := by simpa using hf
  simp only [datumSpatialDerivative, dite_eq_left h]
  exact (h.exists_coordinateDerivative (by norm_num) i).choose_spec.1

/-- One datum derivative loses one Sobolev order and costs `2π`, as used in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem datumSpatialDerivative_mem_and_norm (s : ℕ) (i : Fin d) (f : L2)
    (hf : MemFourierSobolev ((s + 1 : ℕ) : ℝ) f) :
    MemFourierSobolev (s : ℝ) (datumSpatialDerivative i f) ∧
      fourierSobolevNorm (s : ℝ) (datumSpatialDerivative i f) ≤
        (2 * Real.pi) * fourierSobolevNorm ((s + 1 : ℕ) : ℝ) f := by
  have hd := datumSpatialDerivative_hasDerivative i f
    (hf.mono (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)))
  have hf' : MemFourierSobolev ((s : ℝ) + 1) f := by simpa using hf
  exact ⟨hd.memFourierSobolev (by positivity) hf', by
    simpa using hd.fourierSobolevNorm_le (by positivity) hf'⟩

/-- The actual ordered spatial datum jet for
`app:ch_response:eq:direct-envelope-profile`, using the shared ordered-word
operation. The first letter is the outermost derivative. -/
def datumSpatialJet (z : List (Fin d)) (f : L2) : L2 :=
  orderedTransferAction datumSpatialDerivative z f

/-- Spatial mixed-datum membership and its quantitative bound, derived from
the pure datum Sobolev norm in `app:ch_response:eq:direct-envelope-profile`.
Exactly `s + z.length` datum orders are used. -/
theorem datumSpatialJet_mem_and_norm (s : ℕ) (z : List (Fin d)) (f : L2)
    (hf : MemFourierSobolev ((s + z.length : ℕ) : ℝ) f) :
    MemFourierSobolev (s : ℝ) (datumSpatialJet z f) ∧
      fourierSobolevNorm (s : ℝ) (datumSpatialJet z f) ≤
        (2 * Real.pi) ^ z.length * fourierSobolevNorm ((s + z.length : ℕ) : ℝ) f := by
  induction z generalizing s with
  | nil => simpa [datumSpatialJet, orderedTransferAction] using And.intro hf (le_refl
      (fourierSobolevNorm (s : ℝ) f))
  | cons i z ih =>
    have hf' : MemFourierSobolev ((s + 1 + z.length : ℕ) : ℝ) f := by
      simpa only [List.length_cons, Nat.add_right_comm s 1 z.length, Nat.add_assoc] using hf
    obtain ⟨hm, hn⟩ := ih (s + 1) hf'
    obtain ⟨hout, hbound⟩ := datumSpatialDerivative_mem_and_norm s i (datumSpatialJet z f) hm
    refine ⟨hout, hbound.trans ?_⟩
    have h := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * Real.pi by positivity)
    simpa only [List.length_cons, pow_succ, Nat.add_right_comm s 1 z.length, Nat.add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using h

/-- Consing a spatial letter gives its actual weak derivative in the mixed
datum construction of `app:ch_response:eq:direct-envelope-profile`. -/
theorem datumSpatialJet_hasDerivative (i : Fin d) (z : List (Fin d)) (f : L2)
    (hf : MemFourierSobolev ((1 + z.length : ℕ) : ℝ) f) :
    HasEuclideanL2CoordinateDerivative i (datumSpatialJet z f)
      (datumSpatialJet (i :: z) f) := by
  exact datumSpatialDerivative_hasDerivative i _ (by
    simpa using (datumSpatialJet_mem_and_norm 1 z f hf).1)

end JanetCartan.IsometricEmbedding.Response.NearCarrier
