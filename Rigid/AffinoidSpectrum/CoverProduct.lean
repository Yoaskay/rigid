import Rigid.AffinoidSpectrum.CechComparison

set_option linter.style.header false

/-!
# Products of finite rational covers

The product of two covers consists of all pairwise intersections.  Restricting such a product
to a tuple intersection of the first cover gives a cover mutually refining the corresponding
restriction of the second cover.  Together with Čech comparison this proves BGR 8.1.4,
Corollary 4.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

variable {U : AffinoidRationalSubdomain K A}

/-- The finite index type used for the product of two covers. -/
abbrev ProductIndex (𝒰 𝒱 : Cover K A U) :=
  Fin 𝒰.m × Fin 𝒱.m

/-- Decode the finite index of a product cover into its two components. -/
noncomputable def productPair (𝒰 𝒱 : Cover K A U) :
    Fin (𝒰.m * 𝒱.m) → ProductIndex K A 𝒰 𝒱 :=
  finProdFinEquiv.symm

/-- Encode a pair of cover indices as an index of the product cover. -/
noncomputable def productIndex (𝒰 𝒱 : Cover K A U) :
    ProductIndex K A 𝒰 𝒱 → Fin (𝒰.m * 𝒱.m) :=
  finProdFinEquiv

@[simp]
theorem productPair_productIndex (𝒰 𝒱 : Cover K A U)
    (ij : ProductIndex K A 𝒰 𝒱) :
    productPair K A 𝒰 𝒱 (productIndex K A 𝒰 𝒱 ij) = ij :=
  finProdFinEquiv.symm_apply_apply ij

@[simp]
theorem productIndex_productPair (𝒰 𝒱 : Cover K A U)
    (k : Fin (𝒰.m * 𝒱.m)) :
    productIndex K A 𝒰 𝒱 (productPair K A 𝒰 𝒱 k) = k :=
  finProdFinEquiv.apply_symm_apply k

/-- The product cover consisting of all intersections `Uᵢ ∩ Vⱼ`. -/
noncomputable abbrev product (𝒰 𝒱 : Cover K A U) : Cover K A U where
  m := 𝒰.m * 𝒱.m
  domain k :=
    inter K A
      (𝒰.domain (productPair K A 𝒰 𝒱 k).1)
      (𝒱.domain (productPair K A 𝒰 𝒱 k).2)
  subset k :=
    (inter_subset_left K A _ _).trans
      (𝒰.subset (productPair K A 𝒰 𝒱 k).1)
  covers := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [𝒰.covers] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      have hxU : x ∈ U.carrier := 𝒰.subset i hxi
      rw [𝒱.covers] at hxU
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
      refine Set.mem_iUnion.mpr
        ⟨productIndex K A 𝒰 𝒱 (i, j), ?_⟩
      rw [carrier_inter, productPair_productIndex]
      exact ⟨hxi, hxj⟩
    · intro x hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      exact (inter_subset_left K A _ _) hxk |> 𝒰.subset _

/-- The product cover refines its left factor. -/
noncomputable def productRefinementLeft (𝒰 𝒱 : Cover K A U) :
    Refinement K A (product K A 𝒰 𝒱) 𝒰 where
  index k := (productPair K A 𝒰 𝒱 k).1
  subset k := inter_subset_left K A
    (𝒰.domain (productPair K A 𝒰 𝒱 k).1)
    (𝒱.domain (productPair K A 𝒰 𝒱 k).2)

/-- The product cover refines its right factor. -/
noncomputable def productRefinementRight (𝒰 𝒱 : Cover K A U) :
    Refinement K A (product K A 𝒰 𝒱) 𝒱 where
  index k := (productPair K A 𝒰 𝒱 k).2
  subset k := inter_subset_right K A
    (𝒰.domain (productPair K A 𝒰 𝒱 k).1)
    (𝒱.domain (productPair K A 𝒰 𝒱 k).2)

variable (hA : IsAffinoidAlgebra K A)

private noncomputable def restrictedProductRefinementRight
    (𝒰 𝒱 : Cover K A U) (p : ℕ)
    (σ : (𝒰.cechFamily K A hA).StrictTuple p) :
    let W := (𝒰.cechFamily K A hA).tupleInter p σ
    let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
      ((𝒰.cechFamily K A hA).subset (σ 0))
    Refinement K A
      ((product K A 𝒰 𝒱).restrictTo K A W hWU)
      (𝒱.restrictTo K A W hWU) := by
  dsimp only
  let W := (𝒰.cechFamily K A hA).tupleInter p σ
  let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
    ((𝒰.cechFamily K A hA).subset (σ 0))
  exact
    { index := fun k ↦ (productPair K A 𝒰 𝒱 k).2
      subset := by
        intro k x hx
        rw [carrier_inter] at hx ⊢
        exact ⟨hx.1, (inter_subset_right K A _ _) hx.2⟩ }

private noncomputable def restrictedRightRefinementProduct
    (𝒰 𝒱 : Cover K A U) (p : ℕ)
    (σ : (𝒰.cechFamily K A hA).StrictTuple p) :
    let W := (𝒰.cechFamily K A hA).tupleInter p σ
    let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
      ((𝒰.cechFamily K A hA).subset (σ 0))
    Refinement K A
      (𝒱.restrictTo K A W hWU)
      ((product K A 𝒰 𝒱).restrictTo K A W hWU) := by
  dsimp only
  let W := (𝒰.cechFamily K A hA).tupleInter p σ
  let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
    ((𝒰.cechFamily K A hA).subset (σ 0))
  let owner : Fin 𝒰.m := σ 0
  exact
    { index := fun j ↦ productIndex K A 𝒰 𝒱 (owner, j)
      subset := by
        intro j x hx
        rw [carrier_inter] at hx ⊢
        rw [carrier_inter, productPair_productIndex]
        have hxowner :
            x ∈ (𝒰.domain owner).carrier :=
          (𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0 hx.1
        exact ⟨hx.1, hxowner, hx.2⟩ }

/-- **Product-cover comparison.** If the restriction of `𝒱` to every tuple intersection of
`𝒰` is acyclic, then the product cover `𝒰 × 𝒱` is acyclic exactly when `𝒰` is.

This is BGR 8.1.4, Corollary 4. -/
theorem product_normalizedCechComplex_acyclic_iff_left
    (𝒰 𝒱 : Cover K A U)
    (hrestrict : ∀ p (σ : (𝒰.cechFamily K A hA).StrictTuple p),
      let W := (𝒰.cechFamily K A hA).tupleInter p σ
      let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
        ((𝒰.cechFamily K A hA).subset (σ 0))
      ((𝒱.restrictTo K A W hWU).normalizedCechComplex K A hA).Acyclic) :
    ((product K A 𝒰 𝒱).normalizedCechComplex K A hA).Acyclic ↔
      (𝒰.normalizedCechComplex K A hA).Acyclic := by
  have hproductRestrict :
      ∀ p (σ : (𝒰.cechFamily K A hA).StrictTuple p),
        let W := (𝒰.cechFamily K A hA).tupleInter p σ
        let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
          ((𝒰.cechFamily K A hA).subset (σ 0))
        (((product K A 𝒰 𝒱).restrictTo K A W hWU).normalizedCechComplex
          K A hA).Acyclic := by
    intro p σ
    exact
      (normalizedCechComplex_acyclic_iff_of_mutual_refinement K A hA
        (𝒱.restrictTo K A
          ((𝒰.cechFamily K A hA).tupleInter p σ)
          (((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
            ((𝒰.cechFamily K A hA).subset (σ 0))))
        ((product K A 𝒰 𝒱).restrictTo K A
          ((𝒰.cechFamily K A hA).tupleInter p σ)
          (((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
            ((𝒰.cechFamily K A hA).subset (σ 0))))
        (restrictedProductRefinementRight K A hA 𝒰 𝒱 p σ)
        (restrictedRightRefinementProduct K A hA 𝒰 𝒱 p σ)).1
          (hrestrict p σ)
  exact
    (normalizedCechComplex_acyclic_iff_of_refinement K A hA
      𝒰 (product K A 𝒰 𝒱) (productRefinementLeft K A 𝒰 𝒱)
      hproductRestrict).symm

end AffinoidRationalSubdomain.Cover

end Rigid
