module Lecture.Six where

type F x = x -> x

data Bad = MkBad (F Bad)

-- MkBad :: (Bad -> Bad) -> Bad

instance Show Bad where
  show (MkBad f) = "MkBad..."


bad :: Bad -> Bad
bad (MkBad f) = f (MkBad f)

app :: Bad -> Bad -> Bad
app (MkBad f) x = f x

omega :: Bad
omega = bad (MkBad bad)