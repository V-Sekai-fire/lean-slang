import Lake
open Lake DSL System

package LeanSlang where

@[default_target] lean_lib LeanSlang where

/-! ## libslang FFI: compile emitted Slang → SPIR-V in-process (no `slangc` CLI).
    `ffi/slang_shim.cpp` calls libslang's modern API; built into an extern_lib
    and linked by the `slangcheck` end-to-end test exe. The Slang SDK is vendored
    under `vendor/` (gitignored — see `vendor/fetch.sh`), mirroring how other
    Lean bindings vendor their native lib. -/
target slangShimO pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "slang_shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / "slang_shim.cpp"
  let incs := #["-I", (← getLeanIncludeDir).toString,
                "-I", (pkg.dir / "vendor" / "include").toString]
  buildO oFile srcJob incs #["-fPIC", "-O2", "-std=c++17"] "c++" getLeanTrace

extern_lib libslangshim pkg := do
  let name := nameToStaticLib "slangshim"
  buildStaticLib (pkg.staticLibDir / name) #[← slangShimO.fetch]

@[default_target] lean_exe slangcheck where
  root := `Slangcheck
  -- link libslang + its siblings (vendored). rpath so the exe finds them at run.
  moreLinkArgs := #[
    "-ldl",
    "-Wl,-rpath,vendor/lib"]
