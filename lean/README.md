# Lean formalisation

The formal proofs of the two theorems of the paper (Section 7):

* Theorem 1.2, the bound 2√2 − 1: `MovingSofa.ambidextrousSofaConstant_le_two_sqrt_two_sub_one` and
  `MovingSofa.zSofaConstant_le_two_sqrt_two_sub_one`;
* Theorem 1.1: `MovingSofa.ambidextrousSofaConstant_le_of_checkCert` and
  `MovingSofa.zSofaConstant_le_of_checkCert`, which say that if the checker `SofaCert.checkCert T bytes`
  returns `true` for some `T ≥ 5/3`, then the constant is at most `T`.

All four depend only on the axioms `propext`, `Classical.choice` and `Quot.sound` (`../runs/lean_axioms.txt`).

## Files

* `SofaBounds/Defs.lean`: the definitions the statements rest on. `IsMovingSofa`, `IsAmbidextrousSofa`
  and `ambidextrousSofaConstant` are copied without change from Formal Conjectures (Apache 2.0): the file
  `FormalConjectures/Wikipedia/MovingSofa.lean` at commit `b022feb`, and pull request 6424 at commit
  `ae26cdc`. The Z-shaped corridor is defined in the same style.
* `SofaBounds/Hand.lean` and `SofaBounds/ZCorridor.lean`: the bound 2√2 − 1.
* `SofaBounds/Computed.lean`: the final theorems for the computed bound.
* `SofaCertCore/`: the executable checker; it does not import Mathlib.
* `SofaBounds/Cert/`: the proof that the checker is sound (`checkCert_sound`).
* `CheckCertMain.lean`: the command line of the checker.
* `PrintAxioms.lean`: prints the axioms and statements of the four final theorems.

## Building and running

Lean `v4.34.0-rc2` and Mathlib commit `141f6b6` are pinned in `lean-toolchain` and `lake-manifest.json`.
From this folder:

```
lake exe cache get                 # compiled Mathlib (optional download)
lake build                         # checks all proofs
lake env lean PrintAxioms.lean
lake build checkcert
LEAN_NUM_THREADS=30 .lake/build/bin/checkcert 353/200 ../data/certs/cert_c_3653_1765.txt
```

The checker prints `checkCert 353/200 <file> = true`, the number of leaves and the running time, and exits
with status 0 only if it accepts the certificate.
