import Lake
open Lake DSL
-- The Lean side of the TypeScript bridge: the model of JavaScript (Core, F64) and the
-- tactics that prove a typed view equal to it. Built into the image, never taken from a pull request.
package proofci_bridge
require aeneas from "/opt/aeneas/backends/lean"
lean_lib F64
lean_lib ProofciJs
lean_lib Core
lean_lib Spike where
  globs := #[.one `Spike.Rules, .one `Spike.LoopInd, .one `Spike.Safe, .one `Spike.Sim, .one `Spike.Tac]
