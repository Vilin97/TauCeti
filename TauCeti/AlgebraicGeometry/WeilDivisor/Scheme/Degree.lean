/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.DegreeZero

/-!
# Relative degrees and the proper-curve product formula

This compatibility facade preserves the public `Scheme.Degree` module while exporting both the
relative-degree API from `Scheme.Degree.Basic` and the completed smooth-proper-curve product
formula. The product-formula proof cone imports the basic layer directly, avoiding an import
cycle.
-/
