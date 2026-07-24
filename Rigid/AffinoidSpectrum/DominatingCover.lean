import Rigid.AffinoidSpectrum.GeneratedRestriction
import Rigid.AffinoidSpectrum.RationalRefinement
import Rigid.Berkovich.Unit

set_option linter.style.header false

/-!
# Čech acyclicity for dominating-family covers

A pointwise dominating subfamily of a finite unit-ideal family itself spans
the unit ideal.  Its standard generated cover has exactly the same rational
domains as the associated dominating-family cover.  This connects the BGR
product refinement of an arbitrary rational cover to generated-cover
acyclicity.
-/

open scoped BigOperators

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

private theorem sections_subsingleton_of_subsingleton [Subsingleton A]
    (V : AffinoidRationalSubdomain K A) : Subsingleton V.Sections := by
  apply subsingleton_of_zero_eq_one
  have h := congrArg
    (RationalLocalization.baseMap K A V.n V.g V.f)
    (Subsingleton.elim (0 : A) 1)
  simpa using h

/-- If the affinoid algebra is the zero ring, every term of every rational
Čech complex is zero. -/
theorem normalizedCechComplex_acyclic_of_subsingleton [Subsingleton A]
    (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (𝒰.normalizedCechComplex K A hA).Acyclic := by
  intro n
  apply HomologicalComplex.ExactAt.of_isZero
  cases n with
  | zero =>
      change CategoryTheory.Limits.IsZero (ModuleCat.of K U.Sections)
      letI : Subsingleton U.Sections :=
        sections_subsingleton_of_subsingleton K A U
      exact ModuleCat.isZero_of_subsingleton _
  | succ n =>
      change CategoryTheory.Limits.IsZero
        (ModuleCat.of K ((𝒰.cechFamily K A hA).NormalizedCochains n))
      letI : Subsingleton ((𝒰.cechFamily K A hA).NormalizedCochains n) :=
        ⟨fun x y ↦ funext fun σ ↦
          @Subsingleton.elim _
            (sections_subsingleton_of_subsingleton K A
              ((𝒰.cechFamily K A hA).tupleInter n σ)) (x σ) (y σ)⟩
      exact ModuleCat.isZero_of_subsingleton _

private def denominatorFamily {r s : ℕ} (p : Fin r → A)
    (denominator : Fin s → Fin r) : Fin s → A :=
  fun i ↦ p (denominator i)

/-- A pointwise dominating subfamily of a finite unit-ideal family also
spans the unit ideal. -/
theorem span_range_denominatorFamily_eq_top {r s : ℕ} (p : Fin r → A)
    (hp : Ideal.span (Set.range p) = ⊤) (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i))) :
    Ideal.span (Set.range (denominatorFamily A p denominator)) = ⊤ := by
  by_contra htop
  obtain ⟨m, hm, hle⟩ :=
    (Ideal.span (Set.range (denominatorFamily A p denominator))
      ).exists_le_maximal htop
  letI : m.IsMaximal := hm
  letI : IsClosed (m : Set A) := Ideal.IsMaximal.isClosed
  let quotientMap : ContinuousAlgHom K A (A ⧸ m) :=
    { toAlgHom := Ideal.Quotient.mkₐ K m
      cont := continuous_quot_mk }
  let y : BerkovichSpectrumOver K (A ⧸ m) :=
    Classical.choice (BerkovichSpectrumOver.nonempty_of_nontrivial K (A ⧸ m))
  let x : BerkovichSpectrumOver K A :=
    BerkovichSpectrumOver.comapContinuous K A quotientMap y
  obtain ⟨i, hi⟩ := hdom x
  have hden_mem : p (denominator i) ∈ m := by
    apply hle
    apply Ideal.subset_span
    exact ⟨i, rfl⟩
  have hden_quotient : quotientMap (p (denominator i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hden_mem
  have hden_zero : x (p (denominator i)) = 0 := by
    simp [x, hden_quotient]
  have hp_zero (j : Fin r) : x (p j) = 0 := by
    apply le_antisymm
    · simpa only [hden_zero] using hi j
    · exact BerkovichSpectrumOver.nonneg K A x (p j)
  have hone : (1 : A) ∈ Ideal.span (Set.range p) := by
    rw [hp]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  have hterm (j : Fin r) : x (a j * p j) = 0 := by
    rw [BerkovichSpectrumOver.map_mul, hp_zero, mul_zero]
  have hsum : x (∑ j, a j * p j) = 0 := by
    classical
    let t : Finset (Fin r) := Finset.univ
    change x (∑ j ∈ t, a j * p j) = 0
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
        rw [Finset.sum_insert hj]
        apply le_antisymm
        · exact (BerkovichSpectrum.map_add_le_max x.toBerkovichSpectrum
            (a j * p j) (∑ k ∈ t, a k * p k)).trans
              (by rw [hterm, ih, max_self])
        · exact BerkovichSpectrumOver.nonneg K A x _
  rw [ha, BerkovichSpectrumOver.map_one] at hsum
  exact one_ne_zero hsum

private noncomputable abbrev generatedDenominatorCover {r s : ℕ}
    (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i))) :
    Cover K A (whole K A) :=
  generated K A (denominatorFamily A p denominator)
    (span_range_denominatorFamily_eq_top K A p hp denominator hdom)

private theorem dominatingDomain_carrier_eq_generatedDenominatorDomain
    {r s : ℕ} (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i)))
    (i : Fin s) :
    (dominatingDomain K A p hp denominator i).carrier =
      (generatedDomain K A (denominatorFamily A p denominator)
        (span_range_denominatorFamily_eq_top K A p hp denominator hdom) i).carrier := by
  ext x
  rw [mem_dominatingDomain_carrier, mem_generatedDomain_carrier]
  constructor
  · intro h j
    exact h (denominator j)
  · intro h j
    obtain ⟨owner, howner⟩ := hdom x
    exact (howner j).trans (h owner)

private noncomputable def dominatingRefinementGeneratedDenominator
    {r s : ℕ} (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i))) :
    Refinement K A
      (ofDominatingFamily K A p hp denominator hdom)
      (generatedDenominatorCover K A p hp denominator hdom) where
  index i := i
  subset i := by
    change Fin s at i
    exact
      (dominatingDomain_carrier_eq_generatedDenominatorDomain
        K A p hp denominator hdom i).le

private noncomputable def generatedDenominatorRefinementDominating
    {r s : ℕ} (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i))) :
    Refinement K A
      (generatedDenominatorCover K A p hp denominator hdom)
      (ofDominatingFamily K A p hp denominator hdom) where
  index i := i
  subset i := by
    change Fin s at i
    exact
      (dominatingDomain_carrier_eq_generatedDenominatorDomain
        K A p hp denominator hdom i).ge

private noncomputable def restrictRefinement
    {U : AffinoidRationalSubdomain K A} {𝒱 𝒰 : Cover K A U}
    (r : Refinement K A 𝒱 𝒰)
    (W : AffinoidRationalSubdomain K A) (hWU : W.carrier ⊆ U.carrier) :
    Refinement K A
      (𝒱.restrictTo K A W hWU)
      (𝒰.restrictTo K A W hWU) where
  index := r.index
  subset i x hx := by
    rw [carrier_inter] at hx ⊢
    exact ⟨hx.1, r.subset i hx.2⟩

/-- A pointwise dominating-family cover is Čech-acyclic. -/
theorem ofDominatingFamily_normalizedCechComplex_acyclic
    (hA : IsAffinoidAlgebra K A) {r s : ℕ}
    (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i))) :
    ((ofDominatingFamily K A p hp denominator hdom
      ).normalizedCechComplex K A hA).Acyclic := by
  by_cases hnontrivial : Nontrivial A
  · letI : Nontrivial A := hnontrivial
    let x : BerkovichSpectrumOver K A :=
      Classical.choice (BerkovichSpectrumOver.nonempty_of_nontrivial K A)
    obtain ⟨i, -⟩ := hdom x
    let hr : Nonempty (Fin s) := ⟨i⟩
    exact
      (normalizedCechComplex_acyclic_iff_of_mutual_refinement K A hA
        (ofDominatingFamily K A p hp denominator hdom)
        (generatedDenominatorCover K A p hp denominator hdom)
        (generatedDenominatorRefinementDominating K A p hp denominator hdom)
        (dominatingRefinementGeneratedDenominator K A p hp denominator hdom)).2
        (generated_normalizedCechComplex_acyclic K A hA
          (denominatorFamily A p denominator)
          (span_range_denominatorFamily_eq_top K A p hp denominator hdom) hr)
  · letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnontrivial
    exact normalizedCechComplex_acyclic_of_subsingleton K A hA _

/-- A dominating-family cover remains acyclic after restriction to every
rational subdomain. -/
theorem restrictTo_ofDominatingFamily_normalizedCechComplex_acyclic
    (hA : IsAffinoidAlgebra K A) {r s : ℕ}
    (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i)))
    (W : AffinoidRationalSubdomain K A) :
    (((ofDominatingFamily K A p hp denominator hdom).restrictTo K A W (by
      simpa only [carrier_whole] using Set.subset_univ W.carrier)
        ).normalizedCechComplex K A hA).Acyclic := by
  by_cases hnontrivial : Nontrivial A
  · letI : Nontrivial A := hnontrivial
    let x : BerkovichSpectrumOver K A :=
      Classical.choice (BerkovichSpectrumOver.nonempty_of_nontrivial K A)
    obtain ⟨i, -⟩ := hdom x
    let hr : Nonempty (Fin s) := ⟨i⟩
    let hW : W.carrier ⊆ (whole K A).carrier := by
      simpa only [carrier_whole] using Set.subset_univ W.carrier
    exact
      (normalizedCechComplex_acyclic_iff_of_mutual_refinement K A hA
        ((ofDominatingFamily K A p hp denominator hdom).restrictTo K A W hW)
        ((generatedDenominatorCover K A p hp denominator hdom).restrictTo K A W hW)
        (restrictRefinement K A
          (generatedDenominatorRefinementDominating K A p hp denominator hdom)
          W hW)
        (restrictRefinement K A
          (dominatingRefinementGeneratedDenominator K A p hp denominator hdom)
          W hW)).2
        (restrictTo_generated_normalizedCechComplex_acyclic K A hA W
          (denominatorFamily A p denominator)
          (span_range_denominatorFamily_eq_top K A p hp denominator hdom) hr)
  · letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnontrivial
    exact normalizedCechComplex_acyclic_of_subsingleton K A hA _

private theorem productFamily_globally_dominated
    (𝒰 : Cover K A (whole K A))
    (x : BerkovichSpectrumOver K A) :
    ∃ i : Fin (Fintype.card (DenominatorChoice K A 𝒰)),
      ∀ j : Fin (Fintype.card (ProductChoice K A 𝒰)),
        x (productFamily K A 𝒰 j) ≤
          x (productFamily K A 𝒰 (denominatorIndex K A 𝒰 i)) := by
  apply productFamily_dominated_by_denominator K A 𝒰 x
  rw [carrier_whole]
  exact Set.mem_univ x

private noncomputable abbrev productDominatingCover
    (𝒰 : Cover K A (whole K A)) : Cover K A (whole K A) :=
  ofDominatingFamily K A (productFamily K A 𝒰)
    (span_range_productFamily_eq_top K A 𝒰)
    (denominatorIndex K A 𝒰)
    (productFamily_globally_dominated K A 𝒰)

private noncomputable def productCoverRefinementProductDominating
    (𝒰 : Cover K A (whole K A)) :
    Refinement K A (productCover K A 𝒰) (productDominatingCover K A 𝒰) where
  index i := i
  subset i := Set.Subset.rfl

private noncomputable def productDominatingRefinementProductCover
    (𝒰 : Cover K A (whole K A)) :
    Refinement K A (productDominatingCover K A 𝒰) (productCover K A 𝒰) where
  index i := i
  subset i := Set.Subset.rfl

/-- The BGR product refinement of a cover of the whole spectrum is
Čech-acyclic. -/
theorem productCover_normalizedCechComplex_acyclic
    (hA : IsAffinoidAlgebra K A) (𝒰 : Cover K A (whole K A)) :
    ((productCover K A 𝒰).normalizedCechComplex K A hA).Acyclic := by
  exact
    (normalizedCechComplex_acyclic_iff_of_mutual_refinement K A hA
      (productCover K A 𝒰) (productDominatingCover K A 𝒰)
      (productDominatingRefinementProductCover K A 𝒰)
      (productCoverRefinementProductDominating K A 𝒰)).2
      (ofDominatingFamily_normalizedCechComplex_acyclic K A hA
        (productFamily K A 𝒰) (span_range_productFamily_eq_top K A 𝒰)
        (denominatorIndex K A 𝒰)
        (productFamily_globally_dominated K A 𝒰))

/-- The BGR product refinement of a cover of the whole spectrum remains
acyclic after restriction to every rational subdomain. -/
theorem restrictTo_productCover_normalizedCechComplex_acyclic
    (hA : IsAffinoidAlgebra K A) (𝒰 : Cover K A (whole K A))
    (W : AffinoidRationalSubdomain K A) :
    (((productCover K A 𝒰).restrictTo K A W (by
      simpa only [carrier_whole] using Set.subset_univ W.carrier)
        ).normalizedCechComplex K A hA).Acyclic := by
  let hW : W.carrier ⊆ (whole K A).carrier := by
    simpa only [carrier_whole] using Set.subset_univ W.carrier
  exact
    (normalizedCechComplex_acyclic_iff_of_mutual_refinement K A hA
      ((productCover K A 𝒰).restrictTo K A W hW)
      ((productDominatingCover K A 𝒰).restrictTo K A W hW)
      (restrictRefinement K A
        (productDominatingRefinementProductCover K A 𝒰) W hW)
      (restrictRefinement K A
        (productCoverRefinementProductDominating K A 𝒰) W hW)).2
      (restrictTo_ofDominatingFamily_normalizedCechComplex_acyclic K A hA
        (productFamily K A 𝒰) (span_range_productFamily_eq_top K A 𝒰)
        (denominatorIndex K A 𝒰)
        (productFamily_globally_dominated K A 𝒰) W)

end AffinoidRationalSubdomain.Cover

end Rigid
