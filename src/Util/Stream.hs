module Util.Stream
    ( Stream(..)
    , head
    , tail
    , iterate
    ) where

import Prelude hiding (head, tail, iterate)

data Stream a = a :> Stream a

instance Functor Stream where
    fmap f (x :> xs) = f x :> fmap f xs

head :: Stream a -> a
head (x :> _) = x

tail :: Stream a -> Stream a
tail (_ :> xs) = xs

iterate :: (a -> a) -> a -> Stream a
iterate f x = x :> iterate f (f x)

