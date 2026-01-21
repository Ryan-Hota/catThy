structure Category.{u_1, u_2} (Obj : Type u_1) where
  mk ::
  hom : Obj -> Obj -> Type u_2
  seq {x y z : Obj} (f : hom x y) (g : hom y z) : hom x z
  id {x : Obj} : hom x x
  id_is_left_identity  {x y : Obj} {f : hom x y} : seq id f  = f
  id_is_right_identity {x y : Obj} {f : hom x y} : seq f  id = f

infixr : 60 " ⟶ " => Category.hom _
infixl : 70 " ▷ " => Category.seq _

namespace Cat
  variable {obj} {cat : Category obj}

  -- Isomorphism of objects
  def isom {x y : obj} : Prop :=
    ∃ (f : x ⟶ y), ∃ g, f ▷ g = cat.id ∧ g ▷ f = cat.id

  infix : 50 " ≅ " => @isom


  theorem eq_id_left {obj} {cat : Category obj} {x : obj}
    {e : x ⟶ x} (h : ∀ y, ∀ (f : x ⟶ y), e ▷ f = f)
    : e = cat.id :=
      cat.id_is_right_identity.symm.trans (h x cat.id)

  theorem eq_id_right {obj} {cat : Category obj} {x : obj}
    {e : x ⟶ x} (h : ∀ y, ∀ (f : y ⟶ x), f ▷ e = f)
    : e = cat.id :=
      cat.id_is_left_identity.symm.trans (h x cat.id)
end Cat
