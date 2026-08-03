/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveLine.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness and integrality of the projective line

This file identifies both standard affine charts of the projective line with a one-variable
polynomial ring. The explicit presentations prove that the structure morphism is smooth of
relative dimension one. The same charts, together with the homogeneous zero ideal, show that
the projective line is integral; properness and finite type then imply it is Noetherian.

These instances are the target-side geometric input for the finite morphism used in the
product-formula proof.
-/

public section

open scoped DirectSum
open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.ProjectiveLine

universe u

noncomputable section

private lemma X_one_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (1 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (1 : Fin 2)

private lemma X_zero_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (0 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (0 : Fin 2)

private noncomputable def t (K : Type u) [Field K] :
    HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

private lemma adjoin_X_over_degreeZero (K : Type u) [Field K] :
    Algebra.adjoin (homogeneousPieces K 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) = ⊤ := by
  apply top_unique
  intro p _
  have hall : ∀ p : MvPolynomial (Fin 2) K,
      p ∈ Algebra.adjoin (homogeneousPieces K 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r =>
        have h := (Algebra.adjoin (homogeneousPieces K 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K))).algebraMap_mem
          (degreeZeroRingEquiv K r)
        simpa using h
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
        exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact hall p

private lemma adjoin_t (K : Type u) [Field K] :
    Algebra.adjoin (homogeneousPieces K 0) ({t K} : Set
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))) = ⊤ := by
  let hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_one_mem_degree_one K) (Fin 2)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
    (adjoin_X_over_degreeZero K) (fun _ ↦ 1)
    (fun i ↦ MvPolynomial.isHomogeneous_X K i)
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hprod : (∏ i, MvPolynomial.X i ^ ai i) ∈ homogeneousPieces K (a • 1) := by
    rw [← hai]
    exact SetLike.prod_pow_mem_graded (homogeneousPieces K) (fun _ ↦ 1)
      MvPolynomial.X ai (fun i _ ↦ MvPolynomial.isHomogeneous_X K i)
  have h0 : ai 0 ≤ 1 := hai_le 0
  have h1 : ai 1 ≤ 1 := hai_le 1
  interval_cases h0a : ai 0 <;> interval_cases h1a : ai 1
  · have ha : a = 0 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.val_mk, ha, h0a, h1a,
        Fin.prod_univ_two]
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      have hX1 : MvPolynomial.X (1 : Fin 2) ∈
          Submonoid.powers (MvPolynomial.X (1 : Fin 2)) :=
        (Submonoid.mem_powers_iff
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
          (MvPolynomial.X (1 : Fin 2))).mpr ⟨1, by simp⟩
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        Localization.mk_eq_mk']
      trans IsLocalization.mk' (Localization (Submonoid.powers (MvPolynomial.X (1 : Fin 2))))
        (MvPolynomial.X (1 : Fin 2))
        ⟨MvPolynomial.X (1 : Fin 2), hX1⟩
      · apply IsLocalization.mk'_eq_of_eq
        simp [ha, h0a, h1a, Fin.prod_univ_two]
      · exact IsLocalization.mk'_self (S :=
          Localization (Submonoid.powers (MvPolynomial.X (1 : Fin 2))))
          hX1
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = t K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, t, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (t K))
  · have ha : a = 2 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = t K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, t, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
      ring
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (t K))

private def coordinateToPolynomialHom (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* Polynomial (homogeneousPieces K 0) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : homogeneousPieces K 0 →+*
      Polynomial (homogeneousPieces K 0)).comp (degreeZeroRingEquiv K).toRingHom)
    (fun i : Fin 2 ↦ if i = 0 then
      (Polynomial.X : Polynomial (homogeneousPieces K 0)) else 1)

private lemma coordinateToPolynomialHom_X_zero (K : Type u) [Field K] :
    coordinateToPolynomialHom K (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [coordinateToPolynomialHom]

private lemma coordinateToPolynomialHom_X_one (K : Type u) [Field K] :
    coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinateToPolynomialHom]

private noncomputable def awayToPolynomial (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →+*
      Polynomial (homogeneousPieces K 0) :=
  (Localization.awayLift (coordinateToPolynomialHom K)
      (MvPolynomial.X (1 : Fin 2)) (by
        change IsUnit (coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)))
        rw [coordinateToPolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

private lemma awayToPolynomial_t (K : Type u) [Field K] :
    awayToPolynomial K (t K) = Polynomial.X := by
  simp only [awayToPolynomial, RingHom.comp_apply, t,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have hinv : coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHom_X_one]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHom K)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    hinv 1
  simpa [coordinateToPolynomialHom] using h

private lemma awayToPolynomial_fromZero (K : Type u) [Field K]
    (r : homogeneousPieces K 0) :
    awayToPolynomial K
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2))) r) = Polynomial.C r := by
  obtain ⟨s, rfl⟩ := (degreeZeroRingEquiv K).surjective r
  simp only [awayToPolynomial, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have hinv : coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHom_X_one]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHom K)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C s) 1
    hinv 0
  convert h using 1
  · congr 1
  · simp [coordinateToPolynomialHom]

private noncomputable def awayToPolynomialAlgHom (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →ₐ[homogeneousPieces K 0]
      Polynomial (homogeneousPieces K 0) :=
  { awayToPolynomial K with
    commutes' := awayToPolynomial_fromZero K }

private lemma transcendental_t (K : Type u) [Field K] :
    Transcendental (homogeneousPieces K 0) (t K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have h := congrArg (awayToPolynomialAlgHom K) hpq
  have ht : (awayToPolynomialAlgHom K) (t K) = Polynomial.X :=
    awayToPolynomial_t K
  calc
    p = Polynomial.aeval Polynomial.X p := (Polynomial.aeval_X_left_apply p).symm
    _ = Polynomial.aeval ((awayToPolynomialAlgHom K) (t K)) p := by
      rw [ht]
    _ = (awayToPolynomialAlgHom K) (Polynomial.aeval (t K) p) :=
      AlgHom.congr_fun (Polynomial.aeval_algHom (awayToPolynomialAlgHom K) (t K)) p
    _ = (awayToPolynomialAlgHom K) (Polynomial.aeval (t K) q) := h
    _ = Polynomial.aeval ((awayToPolynomialAlgHom K) (t K)) q :=
      (AlgHom.congr_fun (Polynomial.aeval_algHom (awayToPolynomialAlgHom K) (t K)) q).symm
    _ = Polynomial.aeval Polynomial.X q := by rw [ht]
    _ = q := Polynomial.aeval_X_left_apply q

private noncomputable def polynomialAwayAlgEquiv (K : Type u) [Field K] :
    Polynomial (homogeneousPieces K 0) ≃ₐ[homogeneousPieces K 0]
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  (Polynomial.algEquivOfTranscendental (homogeneousPieces K 0) (t K)
    (transcendental_t K)).trans
      ((Subalgebra.equivOfEq _ _ (adjoin_t K)).trans Subalgebra.topEquiv)

private noncomputable def mvPolynomialPresentation (R : Type u) [CommRing R] :
    Algebra.Presentation R (MvPolynomial Unit R) Unit Empty where
  toGenerators := Algebra.Generators.mvPolynomial R Unit
  relation := Empty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact Algebra.Generators.ker_mvPolynomial.symm

private noncomputable def mvPolynomialPreSubmersivePresentation
    (R : Type u) [CommRing R] :
    Algebra.PreSubmersivePresentation R (MvPolynomial Unit R) Unit Empty where
  toPresentation := mvPolynomialPresentation R
  map := Empty.elim
  map_inj a := Empty.elim a

private noncomputable def mvPolynomialSubmersivePresentation
    (R : Type u) [CommRing R] :
    Algebra.SubmersivePresentation R (MvPolynomial Unit R) Unit Empty where
  toPreSubmersivePresentation := mvPolynomialPreSubmersivePresentation R
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

private lemma mvPolynomial_isStandardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial Unit R) := by
  apply (mvPolynomialSubmersivePresentation R).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension]

private lemma polynomial_isStandardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial Unit R) :=
    mvPolynomial_isStandardSmoothOfRelativeDimension_one R
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv R Unit)

private lemma away_isStandardSmoothOfRelativeDimension_one
    (K : Type u) [Field K] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 (homogeneousPieces K 0)
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      (homogeneousPieces K 0) (Polynomial (homogeneousPieces K 0)) :=
    polynomial_isStandardSmoothOfRelativeDimension_one (homogeneousPieces K 0)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (S := Polynomial (homogeneousPieces K 0)) 1
    (polynomialAwayAlgEquiv K)

private noncomputable def tZero (K : Type u) [Field K] :
    HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

private lemma adjoin_tZero (K : Type u) [Field K] :
    Algebra.adjoin (homogeneousPieces K 0) ({tZero K} : Set
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))) = ⊤ := by
  let hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_zero_mem_degree_one K) (Fin 2)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
    (adjoin_X_over_degreeZero K) (fun _ ↦ 1)
    (fun i ↦ MvPolynomial.isHomogeneous_X K i)
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hprod : (∏ i, MvPolynomial.X i ^ ai i) ∈ homogeneousPieces K (a • 1) := by
    rw [← hai]
    exact SetLike.prod_pow_mem_graded (homogeneousPieces K) (fun _ ↦ 1)
      MvPolynomial.X ai (fun i _ ↦ MvPolynomial.isHomogeneous_X K i)
  have h0 : ai 0 ≤ 1 := hai_le 0
  have h1 : ai 1 ≤ 1 := hai_le 1
  interval_cases h0a : ai 0 <;> interval_cases h1a : ai 1
  · have ha : a = 0 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.val_mk, ha, h0a, h1a,
        Fin.prod_univ_two]
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = tZero K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, tZero,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (tZero K))
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      have hX0 : MvPolynomial.X (0 : Fin 2) ∈
          Submonoid.powers (MvPolynomial.X (0 : Fin 2)) :=
        (Submonoid.mem_powers_iff
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
          (MvPolynomial.X (0 : Fin 2))).mpr ⟨1, by simp⟩
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        Localization.mk_eq_mk']
      trans IsLocalization.mk' (Localization (Submonoid.powers (MvPolynomial.X (0 : Fin 2))))
        (MvPolynomial.X (0 : Fin 2)) ⟨MvPolynomial.X (0 : Fin 2), hX0⟩
      · apply IsLocalization.mk'_eq_of_eq
        simp [ha, h0a, h1a, Fin.prod_univ_two]
      · exact IsLocalization.mk'_self (S :=
          Localization (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))) hX0
    rw [heq]
    exact one_mem _
  · have ha : a = 2 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = tZero K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, tZero,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
      ring
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (tZero K))

private def coordinateToPolynomialHomZero (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* Polynomial (homogeneousPieces K 0) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : homogeneousPieces K 0 →+*
      Polynomial (homogeneousPieces K 0)).comp (degreeZeroRingEquiv K).toRingHom)
    (fun i : Fin 2 ↦ if i = 1 then
      (Polynomial.X : Polynomial (homogeneousPieces K 0)) else 1)

private lemma coordinateToPolynomialHomZero_X_zero (K : Type u) [Field K] :
    coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [coordinateToPolynomialHomZero]

private lemma coordinateToPolynomialHomZero_X_one (K : Type u) [Field K] :
    coordinateToPolynomialHomZero K (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
  simp [coordinateToPolynomialHomZero]

private noncomputable def awayToPolynomialZero (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →+*
      Polynomial (homogeneousPieces K 0) :=
  (Localization.awayLift (coordinateToPolynomialHomZero K)
      (MvPolynomial.X (0 : Fin 2)) (by
        change IsUnit (coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)))
        rw [coordinateToPolynomialHomZero_X_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

private lemma awayToPolynomialZero_tZero (K : Type u) [Field K] :
    awayToPolynomialZero K (tZero K) = Polynomial.X := by
  simp only [awayToPolynomialZero, RingHom.comp_apply, tZero,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have hinv : coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHomZero_X_zero]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHomZero K)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1 hinv 1
  simpa [coordinateToPolynomialHomZero] using h

private lemma awayToPolynomialZero_fromZero (K : Type u) [Field K]
    (r : homogeneousPieces K 0) :
    awayToPolynomialZero K
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2))) r) = Polynomial.C r := by
  obtain ⟨s, rfl⟩ := (degreeZeroRingEquiv K).surjective r
  simp only [awayToPolynomialZero, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have hinv : coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHomZero_X_zero]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHomZero K)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C s) 1 hinv 0
  convert h using 1
  · congr 1
  · simp [coordinateToPolynomialHomZero]

private noncomputable def awayToPolynomialZeroAlgHom (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →ₐ[homogeneousPieces K 0]
      Polynomial (homogeneousPieces K 0) :=
  { awayToPolynomialZero K with
    commutes' := awayToPolynomialZero_fromZero K }

private lemma transcendental_tZero (K : Type u) [Field K] :
    Transcendental (homogeneousPieces K 0) (tZero K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have h := congrArg (awayToPolynomialZeroAlgHom K) hpq
  have ht : (awayToPolynomialZeroAlgHom K) (tZero K) = Polynomial.X :=
    awayToPolynomialZero_tZero K
  calc
    p = Polynomial.aeval Polynomial.X p := (Polynomial.aeval_X_left_apply p).symm
    _ = Polynomial.aeval ((awayToPolynomialZeroAlgHom K) (tZero K)) p := by rw [ht]
    _ = (awayToPolynomialZeroAlgHom K) (Polynomial.aeval (tZero K) p) :=
      AlgHom.congr_fun
        (Polynomial.aeval_algHom (awayToPolynomialZeroAlgHom K) (tZero K)) p
    _ = (awayToPolynomialZeroAlgHom K) (Polynomial.aeval (tZero K) q) := h
    _ = Polynomial.aeval ((awayToPolynomialZeroAlgHom K) (tZero K)) q :=
      (AlgHom.congr_fun
        (Polynomial.aeval_algHom (awayToPolynomialZeroAlgHom K) (tZero K)) q).symm
    _ = Polynomial.aeval Polynomial.X q := by rw [ht]
    _ = q := Polynomial.aeval_X_left_apply q

private noncomputable def polynomialAwayZeroAlgEquiv (K : Type u) [Field K] :
    Polynomial (homogeneousPieces K 0) ≃ₐ[homogeneousPieces K 0]
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  (Polynomial.algEquivOfTranscendental (homogeneousPieces K 0) (tZero K)
    (transcendental_tZero K)).trans
      ((Subalgebra.equivOfEq _ _ (adjoin_tZero K)).trans Subalgebra.topEquiv)

private lemma away_zero_isStandardSmoothOfRelativeDimension_one
    (K : Type u) [Field K] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 (homogeneousPieces K 0)
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      (homogeneousPieces K 0) (Polynomial (homogeneousPieces K 0)) :=
    polynomial_isStandardSmoothOfRelativeDimension_one (homogeneousPieces K 0)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (S := Polynomial (homogeneousPieces K 0)) 1
    (polynomialAwayZeroAlgEquiv K)

private lemma chartRingHom_isStandardSmoothOfRelativeDimension_one
    (K : Type u) [Field K] (i : Fin 2) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X i))).comp
          (degreeZeroRingEquiv K).toRingHom) := by
  have hBase : RingHom.IsStandardSmoothOfRelativeDimension 0
      (degreeZeroRingEquiv K).toRingHom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (degreeZeroRingEquiv K)
  have hAway : RingHom.IsStandardSmoothOfRelativeDimension 1
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X i))) := by
    fin_cases i
    · exact away_zero_isStandardSmoothOfRelativeDimension_one K
    · exact away_isStandardSmoothOfRelativeDimension_one K
  simpa using hAway.comp hBase

noncomputable instance (K : Type u) [Field K] :
    SmoothOfRelativeDimension 1 (structureMap K) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  letI : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) := by
    rw [HasRingHomProperty.eq_affineLocally (@SmoothOfRelativeDimension 1)]
    exact affineLocally_respectsIso _
      (HasRingHomProperty.isLocal_ringHomProperty
        (@SmoothOfRelativeDimension 1)).respectsIso
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 1)
    (fun i : Fin 2 ↦ Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i))
    (Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero K))]
  intro i
  have hXi : MvPolynomial.X i ∈ homogeneousPieces K 1 :=
    MvPolynomial.isHomogeneous_X K i
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1)
      (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X i)
        hXi (Nat.zero_lt_one)).inv,
    ← Category.assoc, Proj.basicOpenIsoSpec_inv_ι, structureMap, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact chartRingHom_isStandardSmoothOfRelativeDimension_one K i

private def genericPointCandidate (K : Type u) [Field K] :
    ProjectiveSpectrum (homogeneousPieces K) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa using (Ideal.isPrime_bot : (⊥ : Ideal (MvPolynomial (Fin 2) K)).IsPrime)
  not_irrelevant_le := by
    intro h
    have hx : MvPolynomial.X (0 : Fin 2) ∈
        (⊥ : HomogeneousIdeal (homogeneousPieces K)) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousPieces K)
        Nat.zero_lt_one (X_zero_mem_degree_one K))
    have hx' : MvPolynomial.X (0 : Fin 2) ∈
        (⊥ : Ideal (MvPolynomial (Fin 2) K)) := hx
    exact MvPolynomial.X_ne_zero (R := K) (0 : Fin 2) (Ideal.mem_bot.mp hx')

private lemma irreducibleSpace_projectiveLine (K : Type u) [Field K] :
    IrreducibleSpace (scheme K) := by
  rw [irreducibleSpace_def]
  have hclosure : closure ({genericPointCandidate K} : Set (scheme K)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change ProjectiveSpectrum (homogeneousPieces K) at x
    change x ∈ closure ({genericPointCandidate K} :
      Set (ProjectiveSpectrum (homogeneousPieces K)))
    apply (ProjectiveSpectrum.le_iff_mem_closure (homogeneousPieces K)
      (genericPointCandidate K) x).mp
    change (⊥ : HomogeneousIdeal (homogeneousPieces K)) ≤ x.asHomogeneousIdeal
    exact bot_le
  change IsIrreducible (Set.univ : Set (scheme K))
  rw [← hclosure]
  exact isIrreducible_singleton.closure

private lemma isDomain_away (K : Type u) [Field K] (i : Fin 2) :
    IsDomain (HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X i)) := by
  letI : IsDomain (homogeneousPieces K 0) :=
    (degreeZeroRingEquiv K).toMulEquiv.isDomain_iff.mp inferInstance
  fin_cases i
  · exact (polynomialAwayZeroAlgEquiv K).toRingEquiv.toMulEquiv.isDomain_iff.mp
      (inferInstanceAs (IsDomain (Polynomial (homogeneousPieces K 0))))
  · exact (polynomialAwayAlgEquiv K).toRingEquiv.toMulEquiv.isDomain_iff.mp
      (inferInstanceAs (IsDomain (Polynomial (homogeneousPieces K 0))))

private lemma isReduced_projectiveLine (K : Type u) [Field K] :
    IsReduced (scheme K) := by
  let U : Fin 2 → (scheme K).Opens := fun i ↦
    Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i)
  have hU : ⨆ i, U i = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero K)
  let C : (scheme K).OpenCover := (scheme K).openCoverOfIsOpenCover U hU
  letI (i : C.I₀) : IsReduced (C.X i) := by
    change Fin 2 at i
    change IsReduced (U i)
    have hXi : MvPolynomial.X i ∈ homogeneousPieces K 1 :=
      MvPolynomial.isHomogeneous_X K i
    letI : IsDomain (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X i)) := isDomain_away K i
    haveI : IsIntegral
        (Spec (.of (HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X i)))) := inferInstance
    haveI : IsIntegral (U i) := IsIntegral.of_isIso
      (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X i)
        hXi Nat.zero_lt_one).inv
    exact isReduced_of_isIntegral (U i)
  exact IsReduced.of_openCover (scheme K) C

noncomputable instance (K : Type u) [Field K] : IsIntegral (scheme K) := by
  letI : IrreducibleSpace (scheme K) := irreducibleSpace_projectiveLine K
  letI : IsReduced (scheme K) := isReduced_projectiveLine K
  exact isIntegral_of_irreducibleSpace_of_isReduced (scheme K)

noncomputable instance (K : Type u) [Field K] : IsNoetherian (scheme K) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (structureMap K)
  toCompactSpace := compactSpace_of_universallyClosed (structureMap K)


end
end TauCeti.AlgebraicGeometry.ProjectiveLine

