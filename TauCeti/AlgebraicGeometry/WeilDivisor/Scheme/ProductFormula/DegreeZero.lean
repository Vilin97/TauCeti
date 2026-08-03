/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.FibreInfinity
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.FibreResidueDegree

/-!
# Degree-zero assembly for the divisor product formula

This file assembles the zero- and infinity-fibre calculations into the residue-degree-weighted
product formula for rational functions on smooth proper curves.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped BigOperators

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The positive-order locus of a non-global rational function is finite, with its canonical
fintype transported from the finite zero fibre. -/
@[instance_reducible]
noncomputable def positiveOrderFintype
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    Fintype {x : CodimensionOnePoint X // 0 < orderAt x g} := by
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.standardAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_standardAffineOpen K
  let V := φ ⁻¹ᵁ U
  let a := φ.appLE U V le_rfl
  let hz := ProjectiveLine.zeroPoint_mem_standardAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.zeroPoint K) hz
  letI : Fintype {x : X // φ x = ProjectiveLine.zeroPoint K} :=
    Fintype.ofEquiv (p.primesOver Γ(X, V)) e.symm
  exact Fintype.ofEquiv
    {x : X // φ x = ProjectiveLine.zeroPoint K}
    (zeroFibreEquivPositiveOrder K X f g hg)

/-- The negative-order locus of a non-global rational function is finite, with its canonical
fintype transported from the finite infinity fibre. -/
@[instance_reducible]
noncomputable def negativeOrderFintype
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    Fintype {x : CodimensionOnePoint X // orderAt x g < 0} := by
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.infinityAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_infinityAffineOpen K
  let V := φ ⁻¹ᵁ U
  let a := φ.appLE U V le_rfl
  let hinf := ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.infinityPoint K, hinf⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf
    ⟨ProjectiveLine.infinityPoint K, hinf⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.infinityPoint K) hinf
  letI : Fintype {x : X // φ x = ProjectiveLine.infinityPoint K} :=
    Fintype.ofEquiv (p.primesOver Γ(X, V)) e.symm
  exact Fintype.ofEquiv
    {x : X // φ x = ProjectiveLine.infinityPoint K}
    (infinityFibreEquivNegativeOrder K X f g hg)

/-- The residue-degree-weighted sum of the positive orders is the finite-flat degree of the
zero fibre. -/
theorem sum_positiveOrder_residueDegree_eq_finrank
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    let φ := rationalFunctionMorphism K X f g
    letI := positiveOrderFintype K X f g hg
    ∑ x : {x : CodimensionOnePoint X // 0 < orderAt x g},
      orderAt x.1 g * (f.residueDegree x.1.1 : ℤ) =
        (φ.finrank (ProjectiveLine.zeroPoint K) : ℤ) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : Flat φ := flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.standardAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_standardAffineOpen K
  let V := φ ⁻¹ᵁ U
  let a := φ.appLE U V le_rfl
  let hz := ProjectiveLine.zeroPoint_mem_standardAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.zeroPoint K) hz
  letI : Fintype {x : X // φ x = ProjectiveLine.zeroPoint K} :=
    Fintype.ofEquiv (p.primesOver Γ(X, V)) e.symm
  letI : Fintype {x : CodimensionOnePoint X // 0 < orderAt x g} :=
    positiveOrderFintype K X f g hg
  let epos := zeroFibreEquivPositiveOrder K X f g hg
  have hzero := sum_orderAt_residueDegree_zero_eq_finrank K X f g hg
  dsimp only at hzero
  have hFibre :
      ∑ x : {x : X // φ x = ProjectiveLine.zeroPoint K},
        orderAt (zeroFibreCodimensionOnePoint K X f g hg x) g *
          (φ.residueDegree x.1 : ℤ) =
        (φ.finrank (ProjectiveLine.zeroPoint K) : ℤ) := by
    calc
      _ = ∑ q : p.primesOver Γ(X, V),
          orderAt (zeroFibreCodimensionOnePoint K X f g hg (e.symm q)) g *
            (φ.residueDegree (e.symm q).1 : ℤ) :=
        (Equiv.sum_comp e.symm (fun x ↦
          orderAt (zeroFibreCodimensionOnePoint K X f g hg x) g *
            (φ.residueDegree x.1 : ℤ))).symm
      _ = (φ.finrank (ProjectiveLine.zeroPoint K) : ℤ) := hzero
  calc
    ∑ x : {x : CodimensionOnePoint X // 0 < orderAt x g},
        orderAt x.1 g * (f.residueDegree x.1.1 : ℤ) =
      ∑ x : {x : X // φ x = ProjectiveLine.zeroPoint K},
        orderAt (epos x).1 g * (f.residueDegree (epos x).1.1 : ℤ) :=
      (Equiv.sum_comp epos (fun x ↦
        orderAt x.1 g * (f.residueDegree x.1.1 : ℤ))).symm
    _ = ∑ x : {x : X // φ x = ProjectiveLine.zeroPoint K},
        orderAt (zeroFibreCodimensionOnePoint K X f g hg x) g *
          (φ.residueDegree x.1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show (epos x).1 = zeroFibreCodimensionOnePoint K X f g hg x by
        exact zeroFibreEquivPositiveOrder_apply_val K X f g hg x]
      rw [zeroFibreCodimensionOnePoint_val K X f g hg x]
      change orderAt (zeroFibreCodimensionOnePoint K X f g hg x) g *
          (f.residueDegree x.1 : ℤ) =
        orderAt (zeroFibreCodimensionOnePoint K X f g hg x) g *
          (φ.residueDegree x.1 : ℤ)
      rw [residueDegree_eq_rationalFunctionMorphism_of_eq_zeroPoint
        K X f g x.1 x.2]
    _ = (φ.finrank (ProjectiveLine.zeroPoint K) : ℤ) := hFibre

/-- The residue-degree-weighted sum of the negative orders is the negative finite-flat degree
of the infinity fibre. -/
theorem sum_negativeOrder_residueDegree_eq_neg_finrank
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    let φ := rationalFunctionMorphism K X f g
    letI := negativeOrderFintype K X f g hg
    ∑ x : {x : CodimensionOnePoint X // orderAt x g < 0},
      orderAt x.1 g * (f.residueDegree x.1.1 : ℤ) =
        -(φ.finrank (ProjectiveLine.infinityPoint K) : ℤ) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : Flat φ := flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.infinityAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_infinityAffineOpen K
  let V := φ ⁻¹ᵁ U
  let a := φ.appLE U V le_rfl
  let hinf := ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.infinityPoint K, hinf⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf
    ⟨ProjectiveLine.infinityPoint K, hinf⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.infinityPoint K) hinf
  letI : Fintype {x : X // φ x = ProjectiveLine.infinityPoint K} :=
    Fintype.ofEquiv (p.primesOver Γ(X, V)) e.symm
  letI : Fintype {x : CodimensionOnePoint X // orderAt x g < 0} :=
    negativeOrderFintype K X f g hg
  let eneg := infinityFibreEquivNegativeOrder K X f g hg
  have hinfinity := sum_orderAt_residueDegree_infinity_eq_neg_finrank K X f g hg
  dsimp only at hinfinity
  have hFibre :
      ∑ x : {x : X // φ x = ProjectiveLine.infinityPoint K},
        orderAt (infinityFibreCodimensionOnePoint K X f g hg x) g *
          (φ.residueDegree x.1 : ℤ) =
        -(φ.finrank (ProjectiveLine.infinityPoint K) : ℤ) := by
    calc
      _ = ∑ q : p.primesOver Γ(X, V),
          orderAt (infinityFibreCodimensionOnePoint K X f g hg (e.symm q)) g *
            (φ.residueDegree (e.symm q).1 : ℤ) :=
        (Equiv.sum_comp e.symm (fun x ↦
          orderAt (infinityFibreCodimensionOnePoint K X f g hg x) g *
            (φ.residueDegree x.1 : ℤ))).symm
      _ = -(φ.finrank (ProjectiveLine.infinityPoint K) : ℤ) := hinfinity
  calc
    ∑ x : {x : CodimensionOnePoint X // orderAt x g < 0},
        orderAt x.1 g * (f.residueDegree x.1.1 : ℤ) =
      ∑ x : {x : X // φ x = ProjectiveLine.infinityPoint K},
        orderAt (eneg x).1 g * (f.residueDegree (eneg x).1.1 : ℤ) :=
      (Equiv.sum_comp eneg (fun x ↦
        orderAt x.1 g * (f.residueDegree x.1.1 : ℤ))).symm
    _ = ∑ x : {x : X // φ x = ProjectiveLine.infinityPoint K},
        orderAt (infinityFibreCodimensionOnePoint K X f g hg x) g *
          (φ.residueDegree x.1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show (eneg x).1 = infinityFibreCodimensionOnePoint K X f g hg x by
        exact infinityFibreEquivNegativeOrder_apply_val K X f g hg x]
      rw [infinityFibreCodimensionOnePoint_val K X f g hg x]
      change orderAt (infinityFibreCodimensionOnePoint K X f g hg x) g *
          (f.residueDegree x.1 : ℤ) =
        orderAt (infinityFibreCodimensionOnePoint K X f g hg x) g *
          (φ.residueDegree x.1 : ℤ)
      rw [residueDegree_eq_rationalFunctionMorphism_of_eq_infinityPoint
        K X f g x.1 x.2]
    _ = -(φ.finrank (ProjectiveLine.infinityPoint K) : ℤ) := hFibre

/-- The finite support sum of a non-global rational function splits into its positive-order and
negative-order loci. -/
theorem sum_support_eq_sum_positive_add_sum_negative
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    letI := positiveOrderFintype K X f g hg
    letI := negativeOrderFintype K X f g hg
    ∑ x ∈ ((orderSystem X).principalDivisor g).support,
        orderAt x g * (f.residueDegree x.1 : ℤ) =
      (∑ x : {x : CodimensionOnePoint X // 0 < orderAt x g},
        orderAt x.1 g * (f.residueDegree x.1.1 : ℤ)) +
      ∑ x : {x : CodimensionOnePoint X // orderAt x g < 0},
        orderAt x.1 g * (f.residueDegree x.1.1 : ℤ) := by
  letI : Fintype {x : CodimensionOnePoint X // 0 < orderAt x g} :=
    positiveOrderFintype K X f g hg
  letI : Fintype {x : CodimensionOnePoint X // orderAt x g < 0} :=
    negativeOrderFintype K X f g hg
  let D := (orderSystem X).principalDivisor g
  let s := D.support
  let F : CodimensionOnePoint X → ℤ := fun x ↦
    orderAt x g * (f.residueDegree x.1 : ℤ)
  have hsupp_ne (x : CodimensionOnePoint X) (hx : x ∈ s) : orderAt x g ≠ 0 := by
    change x ∈ ((orderSystem X).principalDivisor g).support at hx
    rw [WeilDivisor.mem_support_iff,
      WeilDivisor.OrderSystem.coeff_principalDivisor, orderSystem_ord] at hx
    exact hx
  have hpos :
      ∑ x ∈ s.filter (fun x ↦ 0 < orderAt x g), F x =
        ∑ x : {x : CodimensionOnePoint X // 0 < orderAt x g}, F x.1 := by
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx ↦ hx.2
    · intro hx
      refine ⟨?_, hx⟩
      change x ∈ ((orderSystem X).principalDivisor g).support
      rw [WeilDivisor.mem_support_iff,
        WeilDivisor.OrderSystem.coeff_principalDivisor, orderSystem_ord]
      exact hx.ne'
  have hneg :
      ∑ x ∈ s.filter (fun x ↦ orderAt x g < 0), F x =
        ∑ x : {x : CodimensionOnePoint X // orderAt x g < 0}, F x.1 := by
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx ↦ hx.2
    · intro hx
      refine ⟨?_, hx⟩
      change x ∈ ((orderSystem X).principalDivisor g).support
      rw [WeilDivisor.mem_support_iff,
        WeilDivisor.OrderSystem.coeff_principalDivisor, orderSystem_ord]
      exact hx.ne
  have hfilter :
      s.filter (fun x ↦ ¬ 0 < orderAt x g) =
        s.filter (fun x ↦ orderAt x g < 0) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxs, hxnot⟩
      refine ⟨hxs, lt_of_le_of_ne (le_of_not_gt hxnot) ?_⟩
      exact hsupp_ne x hxs
    · rintro ⟨hxs, hxneg⟩
      exact ⟨hxs, not_lt_of_ge (le_of_lt hxneg)⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun x ↦ 0 < orderAt x g) F
  rw [hfilter] at hsplit
  change ∑ x ∈ s, F x = _
  calc
    ∑ x ∈ s, F x =
        (∑ x ∈ s.filter (fun x ↦ 0 < orderAt x g), F x) +
          ∑ x ∈ s.filter (fun x ↦ orderAt x g < 0), F x := hsplit.symm
    _ = (∑ x : {x : CodimensionOnePoint X // 0 < orderAt x g}, F x.1) +
        ∑ x : {x : CodimensionOnePoint X // orderAt x g < 0}, F x.1 := by
      rw [hpos, hneg]

/-- The principal divisor of a non-global rational function on a smooth proper curve has
relative degree zero. -/
theorem relativeDegree_principalDivisor_eq_zero_of_nonGlobal
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    relativeDegree f ((orderSystem X).principalDivisor g) = 0 := by
  letI : Fintype {x : CodimensionOnePoint X // 0 < orderAt x g} :=
    positiveOrderFintype K X f g hg
  letI : Fintype {x : CodimensionOnePoint X // orderAt x g < 0} :=
    negativeOrderFintype K X f g hg
  rw [relativeDegree_orderSystem_principalDivisor_apply]
  rw [sum_support_eq_sum_positive_add_sum_negative K X f g hg]
  rw [sum_positiveOrder_residueDegree_eq_finrank K X f g hg,
    sum_negativeOrder_residueDegree_eq_neg_finrank K X f g hg]
  have hrank := finrank_rationalFunctionMorphism_eq_of_nonGlobal K X f g hg
    (ProjectiveLine.zeroPoint K) (ProjectiveLine.infinityPoint K)
  rw [hrank]
  ring

/-- Product formula for the scheme-theoretic order system of a smooth proper curve: every
principal divisor has residue-degree-weighted degree zero. -/
theorem orderSystem_isWeightedDegreeZero
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f] :
    (orderSystem X).IsWeightedDegreeZero
      (fun x ↦ (f.residueDegree x.1 : ℤ)) := by
  apply orderSystem_isWeightedDegreeZero_of_nonGlobal K f
  intro g hg
  exact relativeDegree_principalDivisor_eq_zero_of_nonGlobal K X f g hg

/-- Public adapter name for the divisor product formula on smooth proper curves. -/
theorem divisorProductFormula
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f] :
    (orderSystem X).IsWeightedDegreeZero
      (fun x ↦ (f.residueDegree x.1 : ℤ)) :=
  orderSystem_isWeightedDegreeZero K X f

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
