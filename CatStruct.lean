namespace Category

  structure Category.{u_1, u_2} (Obj : Type u_1) where
    mk ::
      hom : Obj -> Obj -> Type u_2
      seq {x y z : Obj} (f : hom x y) (g : hom y z) : hom x z
      id {x : Obj} : hom x x
      id_is_left_identity  {x y : Obj} {f : hom x y} : seq id f  = f
      id_is_right_identity {x y : Obj} {f : hom x y} : seq f  id = f

  infixr : 60 " ⟶ " => Category.hom _
  infixl : 70 " ▷ " => Category.seq _

  -- Isomorphism of objects
  def isom {obj} {cat : Category obj} {x y : obj} : Prop :=
    ∃ (f : x ⟶ y), ∃ g, f ▷ g = cat.id ∧ g ▷ f = cat.id

  infix : 50 " ≅ " => @isom

end Category

-----------------------------------------------------------------------

namespace Definitions

  open Category

  variable {obj} {cat : Category obj}

  structure Init where
    mk ::
      object : obj
      get_morphism (x : obj) : cat.hom object x
      proof (x : obj) : ∀ (f : cat.hom object x), f = get_morphism x

  structure Terminal where
    mk ::
      object : obj
      get_morphism (x : obj) : cat.hom x object
      proof (x : obj) : ∀ (f : cat.hom x object), f = get_morphism x

  structure Product (a b : obj) where
    mk ::
      object : obj
      fst : cat.hom object a
      snd : cat.hom object b
      pairing {x : obj} : cat.hom x a -> cat.hom x b -> cat.hom x object
      proof (x : obj) :
        ∀ (fa : cat.hom x a), ∀ fb,
          pairing fa fb ▷ fst = fa ∧ pairing fa fb ▷ snd = fb
        ∧
        ∀ (g : cat.hom x object), pairing (g ▷ fst) (g ▷ snd) = g


  structure Coproduct (a b : obj) where
    mk ::
      object : obj
      inl : cat.hom a object
      inr : cat.hom b object
      either {x : obj} : cat.hom a x -> cat.hom b x -> cat.hom object x
      proof (x : obj) :
        ∀ (fa : cat.hom a x), ∀ fb,
          inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
        ∧
        ∀ (g : cat.hom object x), either (inl ▷ g) (inr ▷ g) = g

  structure Exponential {a b : obj} where
    mk ::
      object : obj
      all_products (x : obj) : @Product _ cat x a
      curry {x : obj} : cat.hom (all_products x).object a -> cat.hom x object
      eval : cat.hom (all_products object).object b
      proof : sorry


end Definitions

-----------------------------------------------------------------------

namespace Theorems

  open Category

  variable {obj} {cat : Category obj}

  theorem eq_id_left {x : obj}
    {e : x ⟶ x} (h : ∀ y, ∀ (f : x ⟶ y), e ▷ f = f)
    : e = cat.id :=
      cat.id_is_right_identity.symm.trans (h x cat.id)

  theorem eq_id_right {x : obj}
    {e : x ⟶ x} (h : ∀ y, ∀ (f : y ⟶ x), f ▷ e = f)
    : e = cat.id :=
      cat.id_is_left_identity.symm.trans (h x cat.id)

end Theorems
