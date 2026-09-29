import Lake
open Lake DSL

package sofa_bounds where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "141f6b6455959bfeb0b2a6b04118031191d62683"

/-- The computational core of the certificate checker. It imports only core Lean, so that it can
be compiled to native code quickly. -/
lean_lib SofaCertCore where

/-- The formal proofs. -/
@[default_target]
lean_lib SofaBounds where

/-- The compiled certificate checker. -/
lean_exe checkcert where
  root := `CheckCertMain
