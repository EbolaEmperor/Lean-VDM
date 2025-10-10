import Lake
open Lake DSL

package "Lean_VDM" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxHeartbeats, .ofNat 10000000⟩,
    ⟨`maxRecDepth, .ofNat 1000000⟩
  ]

require "leanprover-community" / "mathlib"

lean_lib «examples»

lean_lib «MIL»

@[default_target]
lean_lib «LeanVDM» where
  -- add library configuration options here
