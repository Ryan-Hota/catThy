-- Do we want (a :->: b) to be one Sort higher than a,b?
-- Do we want a,b to be of different Sorts?
axiom hom.{u} {x y : Sort u} : x -> y -> Sort u

infixr : 60 " :->: " => hom

axiom comp.{u} {x y z : Sort u} : x :->: y -> y :->: z -> x :->: z

infixl : 70 " >-> " => comp

axiom assoc.{u} {w x y z : Sort u}
  {f : w :->: x} {g : x :->: y} {h : y :->: z} :
    f >-> (g >-> h) = (f >-> g) >-> h

axiom ident.{u} {x : Sort u} : x :->: x

axiom comp_id_left.{u}  {x y : Sort u} {f : x :->: y} : ident >-> f = f

axiom comp_id_right.{u} {x y : Sort u} {f : x :->: y} : f >-> ident = f

-- Isomorphism of objects
def isom.{u} {x y : Sort u} : Prop :=
  ∃ (f : x :->: y), ∃ g, f >-> g = ident ∧ g >-> f = ident

infix : 50 " ≅ " => @isom

---------------------------------------------------------------------------------------

-- Do we want product of a b to be at the same Sort as a b?
-- Do we want a b to be of different Sorts?
axiom prod.{u} {x y : Sort (u+1)} : x -> y -> Sort u

infixl : 67 " :><: " => prod

axiom func_pair.{u} {x a b : Sort u} : x :->: a -> x :->: b -> x :->: a :><: b

infixl : 67 " <> " => func_pair

axiom fst.{u} {a b : Sort u} : a :><: b :->: a

axiom snd.{u} {a b : Sort u} : a :><: b :->: b

axiom proj_first.{u}  {x a b : Sort u} (f : x :->: a) (g : x :->: b)
  : (f <> g) >-> fst = f

axiom proj_second.{u} {x a b : Sort u} (f : x :->: a) (g : x :->: b)
  : (f <> g) >-> snd = g

noncomputable def func_prod.{u} {x1 y1 x2 y2 : Sort u}
  (f : x1 :->: y1) (g : x2 :->: y2) : x1 :><: x2 :->: y1 :><: y2 :=
    fst >-> f <> snd >-> g

infixl : 67 " >< " => func_prod

---------------------------------------------------------------------------------------

-- Do we want a^b to be at the same Sort as a b?
-- Do we want a b to be of different Sorts?
axiom exp.{u} {x y : Sort (u+1)} : x -> y -> Sort u

infixl : 68 " :^: " => exp

axiom curry.{u} {x a b : Sort u} : x :><: a :->: b -> x :->: b :^: a

axiom evaluate.{u} {a b : Sort u} : (b :^: a :><: a) :->: b

-- This says that the curried and uncurried versions of f act in the
-- same way on the arguments.
axiom curry_axiom.{u} {x a b : Sort u} {f: x :><: a :->: b}
  : (curry f >< ident) >-> evaluate = f

---------------------------------------------------------------------------------------

theorem eq_id_left {x} {e : x :->: x} (h : ∀ y, ∀ (f : x :->: y), e >-> f = f)
  : e = ident := comp_id_right.symm.trans (h x ident)

theorem eq_id_right {x} {e : x :->: x} (h : ∀ y, ∀ (f : y :->: x), f >-> e = f)
  : e = ident := comp_id_left.symm.trans (h x ident)

---------------------------------------------------------------------------------------

noncomputable def isom0to1.{u} {a b c : Sort u}
  : (a :><: b) :^: c :->: (a :^: c :><: b :^: c) :=
    curry (evaluate >-> fst) <> curry (evaluate >-> snd)

noncomputable def isom1to0.{u} {a b c : Sort u}
  : (a :^: c :><: b :^: c) :->: (a :><: b) :^: c :=
    curry ((fst >< ident) >-> evaluate <> (snd >< ident) >-> evaluate)

theorem isom_indeed_1.{u} {a b c : Sort u}
  : (isom0to1 : (a :><: b) :^: c :->: _) >-> isom1to0 = ident := by
    unfold isom0to1 isom1to0
    apply eq_id_right
    intro y f
    rw [assoc]

    sorry

theorem isom_indeed_2.{u} {a b c : Sort u}
  : isom1to0 >-> (isom0to1 : (a :><: b) :^: c :->: _) = ident := by
    unfold isom0to1 isom1to0

    sorry

-- Finally, the fruit of our hard works... (A × B) ^ C ≅ (A ^ C) × (B ^ C)
theorem exp_isom {a b c : Sort u}
  : (a :><: b) :^: c ≅ a :^: c :><: b :^: c :=
    ⟨isom0to1, ⟨isom1to0, ⟨isom_indeed_1, isom_indeed_2⟩⟩⟩
