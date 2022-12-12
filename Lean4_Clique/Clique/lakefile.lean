import Lake

open System Lake DSL

package Clique {
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    { name := `Mathlib, src := Source.path (FilePath.mk "../Mathlib") }
  ]
}
