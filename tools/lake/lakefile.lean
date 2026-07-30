import Lake
open Lake DSL

-- Minimal Lake workspace pinning the toolchain this module type-checks under.
-- Dep-free: everything above Lean core arrives as compiled oleans from @pgcatalog
-- and @pgquery, not as Lake packages.
package «pgmigrate» where
