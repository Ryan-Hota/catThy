-- module Exponential where

import Prelude (undefined)
import Product ((:><:), fst, (<-->), snd, (><))
import Function ((:->:), (>),id)

infixl 8 :^:
data b:^:a

curry :: ( x:><:a :->: b) -> ( x :->: b:^:a )
curry = undefined

evaluate :: ( b:^:a :><: a ) :->: b
evaluate = undefined

{-
LAWS
( curry f >< id ) > evaluate = f
-}

law :: ((y1 :><: b) :->: z) -> (y1 :><: b) :->: z
law f = ( curry f >< id ) > evaluate

isomorphism0to1 :: (a:><:b):^:c :->: ( a:^:c :><: b:^:c )
isomorphism0to1 = curry ( evaluate > fst ) <--> curry ( evaluate > snd )

isomorphism1to0 :: ( a:^:c :><: b:^:c ) :->: (a:><:b):^:c
isomorphism1to0 = curry ( ( fst >< id ) > evaluate <--> ( snd >< id ) > evaluate )