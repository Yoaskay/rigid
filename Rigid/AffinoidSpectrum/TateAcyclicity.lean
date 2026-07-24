import Rigid.AffinoidSpectrum.DominatingCover

set_option linter.style.header false

/-!
# Tate acyclicity for finite rational covers

An arbitrary rational cover is first rebased to a cover of a whole affinoid
spectrum.  The BGR product construction refines it by a universally acyclic
dominating-family cover.  Čech refinement comparison then proves exactness of
the original augmented normalized Čech complex.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

/-- **Tate acyclicity.** The augmented normalized Čech complex of every
finite rational cover is exact. -/
theorem tateAcyclicity (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (𝒰.normalizedCechComplex K A hA).Acyclic := by
  rw [normalizedCechComplex_acyclic_iff_rebase K A hA]
  let hU : IsAffinoidAlgebra K U.Sections :=
    isAffinoidAlgebra_sections K A hA U
  let 𝒰' : Cover K U.Sections (whole K U.Sections) := 𝒰.rebase K A
  let 𝒱 : Cover K U.Sections (whole K U.Sections) :=
    productCover K U.Sections 𝒰'
  apply
    (normalizedCechComplex_acyclic_iff_of_refinement K U.Sections hU
      𝒰' 𝒱 (productCoverRefinement K U.Sections 𝒰') ?_).2
  · exact productCover_normalizedCechComplex_acyclic K U.Sections hU 𝒰'
  · intro p σ
    exact restrictTo_productCover_normalizedCechComplex_acyclic
      K U.Sections hU 𝒰'
      ((𝒰'.cechFamily K U.Sections hU).tupleInter p σ)

end AffinoidRationalSubdomain.Cover

end Rigid
