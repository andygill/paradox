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
import Data.Maybe
import qualified Data.Graph as G
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

  mapDeRef _ (PureParser a)  = pure PureP
  mapDeRef f (ApParser g h)  = ApP <$> f g <*> f h
  mapDeRef _ (EmptyParser) = pure $ AltsP []
  mapDeRef f (AltParser g h) = (\ x y -> AltsP [x,y]) <$> f g <*> f h
  mapDeRef _ (SatParser p)   = pure (SatP p)
  mapDeRef f (AsParser p str) = flip AsP str <$> f p

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

example :: Parser ()
example =  (\ () () -> ()) <$> example <*> example
       <|> satisfy (== '#') *> pure ()

-----

data P :: * -> * where
   PureP :: P u
   ApP :: u -> u -> P u
   AltsP :: [u] -> P u
   SatP :: (Char -> Bool) -> P u
   AsP :: u -> String -> P u

instance Show u => Show (P u) where
  show PureP = "Pure"
  show (ApP f g) = "App "  ++ show [f,g]
  show (AltsP as) = "Alt "  ++ show as
  show (SatP _) = "Sat *"
  show (AsP u s) = "As " ++ show u ++ " " ++ show s

newtype Symbol = Symbol Int
  deriving (Eq, Ord)

instance Show Symbol where
  show (Symbol s) = "s" ++ show s

newtype Symbols = Symbols [Symbol]
  deriving (Eq, Ord)

instance Show Symbols where
  show (Symbols ss) = unwords (map show ss)

data Production = Production Symbol Symbols
  deriving (Eq, Ord)

instance Show Production where
  show (Production s ss) = 
    show s ++ " -> " ++ show ss

-- instance Eq Production where

data Grammar = Grammar 
  { productions :: [Production]
  , start       :: Symbol
  , terminals   :: [(Symbol, Char -> Bool)]
  , aliases     :: [(Symbol, String)]       -- user generated symbol names
  }

instance Show Grammar where
  show (Grammar ps s ts as) = 
      unlines $ 
        ("names: " ++ show as)  :
        ("terminal: " ++ show (map fst ts))  :
        ("start: " ++ show s) : 
        map show ps

parseGraphToGrammar :: Graph P -> Grammar
parseGraphToGrammar (Graph gs s) = Grammar ps (Symbol s) ts names
  where
    ps    = concatMap mkProds gs

    mkProds (i, PureP)     = [ mkProd i [] ]
    mkProds (i, ApP s1 s2) = [ mkProd i [Symbol s1, Symbol s2 ] ]
    mkProds (i, AltsP ss)  = [ mkProd i [Symbol s] | s <- ss ] 
    mkProds (i, SatP p)    = [ ]
    mkProds (i, AsP s _)   = [ mkProd i [Symbol s] ]

    mkProd i ss = Production (Symbol i) $ Symbols ss

    ts    = [ (Symbol i,p) | (i, SatP p) <- gs ]
    names = [ (Symbol i,n) | (i, AsP _ n) <- gs ]

removeEmptyProductionsGrammar :: Grammar -> Grammar
removeEmptyProductionsGrammar (Grammar ps s ts names) = Grammar ps' s ts names
  where
    scc = G.stronglyConnComp
          [ (i, i, nub (symbolsIn i))
          | i <- nub [ j | Production j _ <- ps ]
          ]
    acyclic = [ i | G.AcyclicSCC i <- scc ]

    symbolsIn i = 
        [ s
        | Production j (Symbols ss) <- ps
        , j == i
        , s <- ss
        ]

    ps' = dce [ Production i (Symbols (concatMap inline ss))
              | Production i (Symbols ss) <- ps
              ]

    dce xs = [ Production i ss | Production i ss <- xs, i `elem` live ]
      where live = s : 
              [ s
              | Production _ (Symbols ss) <- xs            
              , s <- ss
              ] 

    count = 
      [ (head v,length v)
      | v <- group $ sort [ i | Production i _ <- ps ]
      ]

    isNonTerminal s = isNothing (lookup s ts)

    inline i 
      | isNonTerminal i && i `elem` acyclic =
        case find i of
          [Production _ (Symbols ss)] -> [ Symbol s | Symbol s <- ss ]
          _ -> [i]
      | isNonTerminal i =
        -- Really need to do a loop-break here.
        -- s1 -> s2; s2 -> s1, will break.
        case find i of
          [Production _ (Symbols [s])] -> [s]
          _ -> [i]
      | otherwise = [i]

    find i = [ p | p@(Production j _) <- ps, i == j ]

fixGrammar :: (Grammar -> Grammar) -> Grammar -> Grammar
-- fixGrammar f g = f g
fixGrammar f g0@(Grammar ps0 s0 ts0 names0) 
    | ps0 == ps1 && s0 == s1 && map fst ts0 == map fst ts1 && names0 == names1
    = g0
    | otherwise = fixGrammar f g1
  where
    g1@(Grammar ps1 s1 ts1 names1) = f g0


main = do
  print "Starting"
--  g <- reifyGraph number
  g <- reifyGraph example
  print g
  let gr = parseGraphToGrammar g
  print gr
  print $ removeEmptyProductionsGrammar gr
  let gr2 = fixGrammar removeEmptyProductionsGrammar gr
  print gr2
{-
  print $ removeEmptyProductionsGrammar gr2
  let (gr3, _, _, _) = removeEmptyProductionsGrammar gr2
  print gr3
  print $ removeEmptyProductionsGrammar gr3
  let (gr4, _, _, _) = removeEmptyProductionsGrammar gr3
  print gr4
  print $ removeEmptyProductionsGrammar gr4
-}