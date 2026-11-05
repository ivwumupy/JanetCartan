module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Dyadic

/-!
# Kernel bounds and Sobolev shell summation

The analytic bridge for the common kernel estimate in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.

* `exists_kernelSobolevExtension` derives a unique L²-to-Sobolev extension from
  smoothness, compact supports and pointwise output-jet bounds. Its constant is
  `C √μ(input) √ν(output)`.
* `exists_shell_kernel_extensions` proves operator-norm convergence for countable
  shell kernels and identifies the completed output jets with integrals of their
  summed derivatives. `exists_commonSupport_shell_extensions` specializes to
  explicit common compact supports and proves L² membership of those integrals.
* `exists_dyadic_kernel_extension` absorbs shell-volume growth of degree `a`
  using `q + a + 1` integrations, retaining the amplitude prefactor and giving
  the explicit geometric constant two. `shell_extension_unique` ensures that
  different bounds describing the same shell actions give the same operator.

All derivatives and completions are those of the existing Cartesian L² jet
spaces. Differentiation under the integral is proved from kernel smoothness and
support; it is not an extra hypothesis of the final bridge. The parent must
supply the pointwise bounds for its actual localized retarded kernels. This
module does not assert the retarded leakage theorem.
-/
