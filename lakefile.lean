import Lake open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0-rc2"

package "ThePolynomialMethod" where

lean_lib "ThePolynomialMethod" where
  srcDir := "."
  globs := #[.submodules `ThePolynomialMethod]
