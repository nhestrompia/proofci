import Lake
open Lake DSL
package spike
require aeneas from "/opt/aeneas/backends/lean"
lean_lib ProofciJs
lean_lib F64
lean_lib Core
lean_lib Spike where
  globs := #[.submodules `Spike]
