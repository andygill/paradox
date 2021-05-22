{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
import Control.Applicative
import Data.Char
import Data.List
import Debug.Trace
import Data.Reify

-- 

-- Parser API

satisfy :: (Char -> Bool) -> Parser Char
satisfy = SatParser

as :: Parser a -> String -> Parser a
as = AsParser

infix 1 `as`

data Parser :: * -> * where
   PureParser :: a -> Parser a
   ApParser :: Parser (a -> b) -> Parser a -> Parser b
   EmptyParser :: Parser a
   AltParser :: Parser a -> Parser a -> Parser a
   SatParser :: (Char -> Bool) -> Parser Char
   AsParser :: Parser a -> String -> Parser a


instance Functor Parser where 
  fmap f p = pure f <*> p

instance Applicative Parser where
  pure = PureParser
  g <*> h = ApParser g h

instance Alternative Parser where 
  empty = EmptyParser
  g <|> h = AltParser g h

instance MuRef (Parser a) where
  type DeRef (Parser a) = P

  mapDeRef _ (PureParser a)  = pure Pure
  mapDeRef f (ApParser g h)  = Ap <$> f g <*> f h
  mapDeRef _ (EmptyParser) = pure Empty
  mapDeRef f (AltParser g h) = Alt <$> f g <*> f h
  mapDeRef _ (SatParser p)   = pure (Sat p)
  mapDeRef f (AsParser p str) = flip As str <$> f p

-----
-- Small example of the parser
-- numbers

whitespace :: Parser ()
whitespace = some (satisfy isSpace) *> pure ()

whitespaced :: Parser a -> Parser a
whitespaced p = whitespace *> p <* whitespace

digit :: Parser Int
digit = (\ c -> read [c]) <$> satisfy isDigit `as` "digit"

number :: Parser Int
number = read <$> whitespaced (some (satisfy isDigit)) `as` "number"

-----

data P :: * -> * where
   Pure :: P u
   Ap :: u -> u -> P u
   Empty :: P u
   Alt :: u -> u -> P u
   Sat :: (Char -> Bool) -> P u
   As :: u -> String -> P u



-----
