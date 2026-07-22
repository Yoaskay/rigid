import Rigid.AffinoidAlgebra.RationalLocalization
import Rigid.Berkovich.AffinoidDomain

set_option linter.style.header false
set_option linter.unusedSectionVars false

open scoped Pointwise

/-!
# Rational subdomains of an affinoid spectrum

This file bundles rational data and proves that rational subdomains are closed under
intersection.  The intersection datum is the standard product datum: if
`(g, fᵢ)` and `(h, kⱼ)` define two rational domains, their intersection is defined by
denominator `g * h` and all products of one member of `{g, fᵢ}` with one member of
`{h, kⱼ}`.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- A rational subdomain bundled with a rational datum defining it. -/
structure AffinoidRationalSubdomain
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] where
  n : ℕ
  g : A
  f : Fin n → A
  isRational : IsRationalDatum g f

namespace AffinoidRationalSubdomain

/-- The point set defined by a bundled rational datum. -/
def carrier (U : AffinoidRationalSubdomain K A) : Set (BerkovichSpectrumOver K A) :=
  BerkovichSpectrumOver.rationalDomainSet K A U.g U.f

/-- The rational localization representing analytic functions on the domain. -/
abbrev Sections (U : AffinoidRationalSubdomain K A) :=
  RationalLocalization K A U.n U.g U.f

/-- The denominator followed by all numerators of a rational datum. -/
private def extendedNumerator (U : AffinoidRationalSubdomain K A) : Fin (U.n + 1) → A :=
  Fin.cases U.g U.f

private theorem range_extendedNumerator (U : AffinoidRationalSubdomain K A) :
    Set.range (extendedNumerator K A U) = Set.insert U.g (Set.range U.f) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩

/-- The intersection of two rational subdomains, represented by the product rational datum. -/
noncomputable def inter (U V : AffinoidRationalSubdomain K A) :
    AffinoidRationalSubdomain K A where
  n := (U.n + 1) * (V.n + 1)
  g := U.g * V.g
  f k :=
    extendedNumerator K A U (finProdFinEquiv.symm k).1 *
      extendedNumerator K A V (finProdFinEquiv.symm k).2
  isRational := by
    let u := extendedNumerator K A U
    let v := extendedNumerator K A V
    let p : Fin ((U.n + 1) * (V.n + 1)) → A := fun k ↦
      u (finProdFinEquiv.symm k).1 * v (finProdFinEquiv.symm k).2
    have hp : Set.range u * Set.range v = Set.range p := by
      ext a
      constructor
      · rw [Set.mem_mul]
        rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
        refine ⟨finProdFinEquiv (i, j), ?_⟩
        change u (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 *
          v (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = u i * v j
        rw [Equiv.symm_apply_apply]
      · rintro ⟨k, rfl⟩
        rw [Set.mem_mul]
        exact ⟨u (finProdFinEquiv.symm k).1, ⟨_, rfl⟩,
          v (finProdFinEquiv.symm k).2, ⟨_, rfl⟩, rfl⟩
    have hspan : Ideal.span (Set.range u * Set.range v) = ⊤ := by
      rw [← Ideal.span_mul_span', range_extendedNumerator K A U,
        range_extendedNumerator K A V, U.isRational, V.isRational]
      simp
    apply top_unique
    rw [← hspan]
    apply Ideal.span_mono
    rw [hp]
    exact Set.subset_insert _ _

/-- The product rational datum cuts out the set-theoretic intersection. -/
@[simp]
theorem carrier_inter (U V : AffinoidRationalSubdomain K A) :
    (inter K A U V).carrier = U.carrier ∩ V.carrier := by
  ext x
  change
    (∀ k,
      x (extendedNumerator K A U (finProdFinEquiv.symm k).1 *
          extendedNumerator K A V (finProdFinEquiv.symm k).2) ≤ x (U.g * V.g)) ↔
      (∀ i, x (U.f i) ≤ x U.g) ∧ ∀ j, x (V.f j) ≤ x V.g
  constructor
  · intro hx
    have hdenom : x (U.g * V.g) ≠ 0 :=
      BerkovichSpectrumOver.RationalDomain.denominator_ne_zero K A
        (inter K A U V).isRational ⟨x, hx⟩
    have hUg_ne : x U.g ≠ 0 := by
      intro h
      apply hdenom
      simp [h]
    have hVg_ne : x V.g ≠ 0 := by
      intro h
      apply hdenom
      simp [h]
    have hUg_pos : 0 < x U.g :=
      lt_of_le_of_ne (BerkovichSpectrumOver.nonneg K A x U.g) hUg_ne.symm
    have hVg_pos : 0 < x V.g :=
      lt_of_le_of_ne (BerkovichSpectrumOver.nonneg K A x V.g) hVg_ne.symm
    constructor
    · intro i
      have h := hx (finProdFinEquiv (i.succ, 0))
      rw [Equiv.symm_apply_apply] at h
      simp only [extendedNumerator, Fin.cases_succ, Fin.cases_zero,
        BerkovichSpectrumOver.map_mul] at h
      exact (mul_le_mul_iff_left₀ hVg_pos).mp h
    · intro j
      have h := hx (finProdFinEquiv (0, j.succ))
      rw [Equiv.symm_apply_apply] at h
      simp only [extendedNumerator, Fin.cases_succ, Fin.cases_zero,
        BerkovichSpectrumOver.map_mul] at h
      exact (mul_le_mul_iff_right₀ hUg_pos).mp h
  · rintro ⟨hU, hV⟩ k
    have hu : x (extendedNumerator K A U (finProdFinEquiv.symm k).1) ≤ x U.g := by
      refine Fin.cases ?_ (fun i ↦ ?_) (finProdFinEquiv.symm k).1
      · exact le_rfl
      · exact hU i
    have hv : x (extendedNumerator K A V (finProdFinEquiv.symm k).2) ≤ x V.g := by
      refine Fin.cases ?_ (fun j ↦ ?_) (finProdFinEquiv.symm k).2
      · exact le_rfl
      · exact hV j
    simpa only [BerkovichSpectrumOver.map_mul] using
      mul_le_mul hu hv
        (BerkovichSpectrumOver.nonneg K A x _)
        (BerkovichSpectrumOver.nonneg K A x _)

/-- The intersection is contained in its left factor. -/
theorem inter_subset_left (U V : AffinoidRationalSubdomain K A) :
    (inter K A U V).carrier ⊆ U.carrier := by
  rw [carrier_inter]
  exact Set.inter_subset_left

/-- The intersection is contained in its right factor. -/
theorem inter_subset_right (U V : AffinoidRationalSubdomain K A) :
    (inter K A U V).carrier ⊆ V.carrier := by
  rw [carrier_inter]
  exact Set.inter_subset_right

end AffinoidRationalSubdomain

end Rigid
