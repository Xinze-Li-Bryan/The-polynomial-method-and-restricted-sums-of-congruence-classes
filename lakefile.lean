import Lake open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0-rc2"

package "ThePolynomialMethod" where

lean_lib "ThePolynomialMethod" where
  srcDir := "."
  globs := #[.submodules `ThePolynomialMethod]

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"