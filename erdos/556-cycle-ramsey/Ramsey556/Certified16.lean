import Ramsey556.Cert16.Rows
import Ramsey556.Cert16.Stitch

namespace Ramsey556

open Cert16 in
/-- Complete extension catalog up to order sixteen. Each intermediate order is available for reuse. -/
theorem Cert16.completeCatalog : CatalogProof (fun n => (table n).graphs) := by
  apply catalog_of_layers
  intro n lo hi
  match n with
  | 0 => omega
  | 1 => exact rows1
  | 2 => exact rows2
  | 3 => exact rows3
  | 4 => exact rows4
  | 5 => exact rows5
  | 6 => exact rows6
  | 7 => exact rows7
  | 8 => exact rows8
  | 9 => exact rows9
  | 10 => exact rows10
  | 11 => exact rows11
  | 12 => exact rows12
  | 13 => exact rows13
  | 14 => exact rows14
  | 15 => exact rows15
  | m + 16 => omega

/-- On 16 vertices, any color graph with at least sixty edges is bipartite
or contains a nine-cycle. The certificate includes every density-preserving
extension up to relabeling and an explicit bipartition at every leaf. -/
theorem denseC9Free16Bipartite : DenseC9Free16Bipartite :=
  Cert16.denseC9Free16Bipartite_of_catalog Cert16.completeCatalog

/-- The two-color classification used by the vertex-deletion theorems. -/
theorem twoColorOctets16 : TwoColorOctets16 :=
  twoColorOctets16_of_edgeBound denseC9Free16Bipartite

end Ramsey556
