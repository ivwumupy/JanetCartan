module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Retained
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Restriction

/-!
# Signed Sobolev transport for the actual finite physical evolutions

Exact cycle and physical Fourier change of variables for the selected
volume-preserving coordinate permutation gives Sobolev membership and norm
invariance at every real order, including positive and negative integers.
The actual chart estimates and their literal adjoints therefore transfer
with unchanged constants, coefficient profiles and fixed shifts. Finite sums
retain membership and the summed bounds, including H⁻¹ → L² on L² inputs.

Positive output bounds are converted to genuine restriction norms through
`Local.Fourier`; the existing localization and measurement-cutoff APIs supply
the corresponding local results. This is the coordinate deduction consumed
by the finite physical solver and complete residual. The parent still selects
and instantiates the actual charts, masks, all PDO terms, full PDE identity,
and real pairing. No unconditional solver existence is asserted here.
Sources: `app:ch_regular_base:eq:sector-theorem-solution`,
`app:ch_regular_base:eq:sector-theorem-residual`, and
`app:ch_regular_base:eq:measured-adjoint` in `paper.tex`;
`fixed-time-representation` and `energy-complete-residual` in `paper-v2.tex`.
-/
