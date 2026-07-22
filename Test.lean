-- Root of the `Test` library: build-time test assertions. Elaborating this (part
-- of `lake build`) checks the `checkSafe` battery; a moved verdict fails the build.
import Test.Battery
-- The Prompt-13 implicit-flow refutation of `shellwall_noninterference`.
import Test.ImplicitFlow
