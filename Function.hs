module Function where

import Prelude (undefined)

infixr 0 :->:
data a:->:b

infixl 9 > 
(>) :: x :->: y -> y :->: z -> x :->: z
(>) = undefined

id :: x :->: x
id = undefined

{-
LAWS
f > id = f
id > f = f 
-}