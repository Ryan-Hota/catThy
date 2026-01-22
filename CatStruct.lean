namespace Definitions

  structure Category.{u, v} (Obj : Type u) where
    mk ::
      hom : Obj -> Obj -> Type v
      seq {x y z : Obj} : hom x y -> hom y z -> hom x z
      id {x : Obj} : hom x x
      id_is_left_identity  {x y : Obj} {f : hom x y} : seq id f  = f
      id_is_right_identity {x y : Obj} {f : hom x y} : seq f  id = f

  infixr : 60 " ⟶ " => Category.hom _
  infixl : 70 " ▷ " => Category.seq _

  -----------------------------------------------------------------------

  variable {obj} {cat : Category obj}

  -- Isomorphism of objects
  structure Isomorphic {x y : obj} where
    mk::
      fwd : cat.hom x y
      bck : cat.hom y x
      proof : fwd ▷ bck = cat.id ∧ bck ▷ fwd = cat.id

  structure Initial where
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
      pair {x : obj} : cat.hom x a -> cat.hom x b -> cat.hom x object
      proof_exists (x : obj) :
        ∀ (fa : cat.hom x a), ∀ fb,
          pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
      proof_unique (x : obj) : ∀ (g : cat.hom x object),
          pair (g ▷ fst) (g ▷ snd) = g

  def cross
    {d1 d2 c1 c2 : obj}
    {d1Xd2 : @Product _ cat d1 d2}
    {c1Xc2 : @Product _ cat c1 c2}
    (f : cat.hom d1 c1) (g : cat.hom d2 c2)
    : cat.hom d1Xd2.object c1Xc2.object :=
      c1Xc2.pair (d1Xd2.fst ▷ f) (d1Xd2.snd ▷ g)

  structure Coproduct (a b : obj) where
    mk ::
      object : obj
      inl : cat.hom a object
      inr : cat.hom b object
      either {x : obj} : cat.hom a x -> cat.hom b x -> cat.hom object x
      proof (x : obj) : (
        ∀ (fa : cat.hom a x),
          ∀ fb,
            inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
      ) ∧ (
        ∀ (g : cat.hom object x),
          either (inl ▷ g) (inr ▷ g) = g
      )

  structure Exponential (a b : obj) where
    mk ::
      object : obj
      all_products (x : obj) : @Product _ cat x a
      curry {x : obj} : cat.hom (all_products x).object b -> cat.hom x object
      eval : cat.hom (all_products object).object b
      proof (x : obj) : (
        ∀ (f : cat.hom (all_products x).object b) ,
          (cross (curry f) cat.id) ▷ eval = f
      ) ∧ (
        ∀ (g : cat.hom x object) ,
          curry (cross g cat.id ▷ eval) = g
      )

end Definitions

-----------------------------------------------------------------------

namespace Theorems

  open Definitions

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
