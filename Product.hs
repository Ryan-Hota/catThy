module Product where

import Prelude (undefined)
import Function ((:->:), (>))

infixl 7:><:
data (:><:) a b

infixl 7 <-->
(<-->) :: x :->: a -> x :->: b -> x :->: a :><: b
(<-->) = undefined

fst :: (a :><: b) :->: a
fst = undefined
snd ::  (a :><: b) :->: b
snd = undefined

{-
LAWS
<f,g> > fst = f
<f,g> > snd = g
-}

lawFst :: (x :->: z) -> (x :->: b) -> x :->: z
lawFst f g = ( f <--> g ) > fst
lawSnd :: (x :->: a) -> (x :->: z) -> x :->: z
lawSnd f g = ( f <--> g ) > snd

infixl 7 ><
(><) :: (y1 :->: a) -> (y2 :->: b) -> (y1 :><: y2) :->: (a :><: b)
f >< g = fst > f <--> snd > g -- \ ( x , y ) -> ( f x , g y )