# QHilbert

A Lean 4 formalization of quantum computing foundations over finite-dimensional Hilbert spaces, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

QHilbert provides verified definitions and proofs for quantum states, operators, tensor products, and spectral theory. 

## Modules

| Module | Description |
|---|---|
| `OuterProduct` | Outer product `\|x⟩⟨y\|`, its adjoint, trace, and spectral completeness |
| `Commons` | Standard qubits (`\|0⟩`, `\|1⟩`, `\|+⟩`, `\|-⟩`), Hadamard, Pauli-X |
| `CommonsTensor` | Two-qubit basis states and their outer products |
| `LinearMapPropositions` | Density operators, effects, isometries, unitaries, pure states |
| `TensorProduct` | Semilinear map extensions for tensor products |
| `InnerTensorProduct` | Inner product on tensor product spaces |
| `PartialTrace` | Partial trace over first/second subsystem |
| `Projection` | Projection lemmas for 2-dimensional spaces |
| `ProjectionSubmodule` | Bijection between projections and submodules; Sasaki implication |
| `Properties` | Lemmas A.7 and A.8 (scalar, addition, norm, adjoint properties) |
| `Spectrum` | Eigenvalue theory and spectral decomposition in dimension 2 |

## Building

Requires [Lean 4](https://lean-lang.org/) (v4.22.0-rc4) and [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```sh
lake build
```

## License

See [LICENSE](LICENSE) for details.
