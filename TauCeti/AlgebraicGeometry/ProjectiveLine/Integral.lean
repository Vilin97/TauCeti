/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveLine.Smooth

/-!
# Integrality of the projective line

This file proves that the projective line over a field is integral and Noetherian.  It also
separates its zero and infinity points from the generic point.  These facts are downstream of
the chart calculations and relative-smoothness instance in `ProjectiveLine.Smooth`.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace

namespace TauCeti.AlgebraicGeometry.ProjectiveLine

noncomputable section

universe u

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

/-- The point `[0 : 1]` is not the generic point of the projective line. -/
lemma zeroPoint_ne_genericPoint (K : Type u) [Field K] :
    zeroPoint K ≠ genericPoint (scheme K) := by
  intro h
  let U := standardAffineOpen K
  let hU := isAffineOpen_standardAffineOpen K
  let hz : zeroPoint K ∈ U := zeroPoint_mem_standardAffineOpen K
  letI : Nonempty U := ⟨⟨zeroPoint K, hz⟩⟩
  have hη : genericPoint (scheme K) ∈ U :=
    ((genericPoint_spec (scheme K)).mem_open_set_iff U.isOpen).mpr
      ⟨zeroPoint K, trivial, hz⟩
  have heq : hU.primeIdealOf ⟨zeroPoint K, hz⟩ =
      hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩ := by
    congr 1
    exact Subtype.ext h
  have hηIdeal : (hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩).asIdeal = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  have heqIdeal := congrArg PrimeSpectrum.asIdeal heq
  rw [primeIdealOf_zeroPoint_asIdeal_of_mem K hz, hηIdeal] at heqIdeal
  exact affineCoordinate_ne_zero K (Ideal.span_singleton_eq_bot.mp heqIdeal)

/-- The point `[1 : 0]` is not the generic point of the projective line. -/
lemma infinityPoint_ne_genericPoint (K : Type u) [Field K] :
    infinityPoint K ≠ genericPoint (scheme K) := by
  intro h
  let U := infinityAffineOpen K
  let hU := isAffineOpen_infinityAffineOpen K
  let hinf : infinityPoint K ∈ U := infinityPoint_mem_infinityAffineOpen K
  letI : Nonempty U := ⟨⟨infinityPoint K, hinf⟩⟩
  have hη : genericPoint (scheme K) ∈ U :=
    ((genericPoint_spec (scheme K)).mem_open_set_iff U.isOpen).mpr
      ⟨infinityPoint K, trivial, hinf⟩
  have heq : hU.primeIdealOf ⟨infinityPoint K, hinf⟩ =
      hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩ := by
    congr 1
    exact Subtype.ext h
  have hηIdeal : (hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩).asIdeal = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  have heqIdeal := congrArg PrimeSpectrum.asIdeal heq
  rw [primeIdealOf_infinityPoint_asIdeal_of_mem K hinf, hηIdeal] at heqIdeal
  exact inverseAffineCoordinate_ne_zero K (Ideal.span_singleton_eq_bot.mp heqIdeal)

noncomputable instance (K : Type u) [Field K] : IsNoetherian (scheme K) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (structureMap K)
  toCompactSpace := compactSpace_of_universallyClosed (structureMap K)

end

end TauCeti.AlgebraicGeometry.ProjectiveLine
