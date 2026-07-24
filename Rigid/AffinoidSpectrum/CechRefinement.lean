import Rigid.AffinoidSpectrum.Cech
import Rigid.Cech.Refinement

set_option linter.style.header false

/-!
# Refinement maps for rational Čech complexes

This file connects rational-cover refinements to the generic chain-level refinement map.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

/-- A rational-cover refinement as a refinement of the corresponding Čech families. -/
noncomputable def Refinement.cechRefinement (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} {𝒱 𝒰 : Cover K A U}
    (r : Refinement K A 𝒱 𝒰) :
    (𝒱.cechFamily K A hA).Refinement (𝒰.cechFamily K A hA) where
  index := r.index
  subset := r.subset

/-- Restriction of ordinary Čech cochains along a rational-cover refinement. -/
noncomputable def Refinement.cechComplexMap (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} {𝒱 𝒰 : Cover K A U}
    (r : Refinement K A 𝒱 𝒰) :
    (𝒰.cechFamily K A hA).cofaceModule.complex ⟶
      (𝒱.cechFamily K A hA).cofaceModule.complex :=
  (r.cechRefinement K A hA).complexMap

end AffinoidRationalSubdomain.Cover

end Rigid
