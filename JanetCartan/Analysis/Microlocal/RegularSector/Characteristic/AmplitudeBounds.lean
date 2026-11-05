module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.EvolutionCoordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.ComplexPhysical

/-!
# Primitive budgets for the literal characteristic amplitudes

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`,
`AmplitudeBounds.exists_pencilPrimitiveAmplitudes_cNorm_bounds` proves joint
single-high bounds for the existing signed datum, physical potential, signed
exponential row, leading and correction columns, and the full physical action
on the correction. The finite complex matrices `W₀`, `W₁=i b₋₁PW₀`, and
`PW₁` have the same bounds in the Frobenius norm.

The reserve is nine, independently of derivative order. Constants precede
`Q,B,h,Φ,C.symm,σ`. All intermediate low bounds are derived from fixed C9
primitive bounds on explicit nested compact balls with open margins and the
original adjugate/transport gaps. The row and complement estimates instantiate
the published producers. No potential, row, complement or amplitude budget
is assumed. The full `B` term and physical derivatives with fixed source time
and initial covector are retained.

`exists_pencilPrimitiveAmplitudes_graded_bounds` derives the fixed loss nine
in the primitive profile index, including the required low bounds from the
profiles themselves. `pencilCorrectionResidualComplexMatrix_column_eq_physicalApply`
identifies the estimated residual matrix with the original physical operator
on the constructed coordinate split. `curryCharacteristicMatrix` and its
checked linear pullback place these matrices in the exact joint coordinates
of `EvolutionIntegral.SymbolBudgets` without an additional derivative loss.

Consumers are `EvolutionIntegral.SymbolBudgets` and the residual in
`app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual`. The regular-sector parent
still supplies the actual uniform primitive family and its common domains,
and extends these same local amplitudes conically. These local estimates do
not assert the unconditional sector or the paper's final existence theorem.
-/
