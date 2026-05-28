import Mathlib.Algebra.Group.Conj

/-!
## API for `ConjClasses.map`

These lemmas belong upstream in mathlib; we keep them here until a mathlib PR lands.
-/

namespace ConjClasses

variable {G H K : Type*} [Group G] [Group H] [Group K]

@[simp] lemma map_mk (f : G →* H) (g : G) :
    ConjClasses.map f (ConjClasses.mk g) = ConjClasses.mk (f g) := by
  rfl

lemma map_id (C : ConjClasses G) :
    ConjClasses.map (MonoidHom.id G) C = C := by
  refine Quotient.inductionOn C (fun _ => rfl)

lemma map_comp (f : G →* H) (g : H →* K) (C : ConjClasses G) :
    ConjClasses.map (g.comp f) C = ConjClasses.map g (ConjClasses.map f C) := by
  refine Quotient.inductionOn C (fun _ => rfl)

end ConjClasses
