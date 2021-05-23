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

type Id = Int

data Symbol 
  = Terminal (Char -> Bool)
  | NonTerminal Id

instance Show Symbol where
  show (Terminal _)    = "sat"
  show (NonTerminal s) = "e" ++ show s

newtype Symbols = Symbols [Symbol]

instance Show Symbols where
  show (Symbols ss) = unwords (map show ss)

data Production = Production Id Symbols

instance Show Production where
  show (Production s ss) = 
    "e" ++ show s ++ " -> " ++ show ss

-- instance Eq Production where

data Grammar = Grammar 
  { productions :: [Production]
  , start       :: Id
--  , terminals   :: [(Id, Char -> Bool)]
  , aliases     :: [(Id, String)]      -- user generated symbol names
  }

instance Show Grammar where
  show (Grammar ps s as) = 
      unlines $ ("names: " ++ show as) : ("start: " ++ show s) : map show ps

parseGraphToGrammar :: Graph P -> Grammar
parseGraphToGrammar (Graph gs s) = Grammar ps s names
  where
    ps    = concatMap mkProds gs

    mkProds (i, PureP)     = [ mkProd i [] ]
    mkProds (i, ApP s1 s2) = [ mkProd i [NonTerminal s1, NonTerminal s2 ] ]
    mkProds (i, AltsP ss)  = [ mkProd i [NonTerminal s] | s <- ss ] 
    mkProds (i, SatP p)    = [ mkProd i [Terminal p] ]
    mkProds (i, AsP s _)   = [ mkProd i  [NonTerminal s] ]

    mkProd i ss = Production i $ Symbols ss

    names = [ (i,n) | (i, AsP _ n) <- gs ]


--removeEmptyProductionsGrammar :: Grammar -> Grammar
removeEmptyProductionsGrammar (Grammar ps s names) = 
    (Grammar ps' s names, count, empty, scc)
  where
    scc = G.stronglyConnComp
          [ (i, i, nonTerminalsIn i)
          | i <- nub [ j | Production j _ <- ps ]
          ]

    acyclic = [ i | G.AcyclicSCC i <- scc ]

    nonTerminalsIn i = 
        [ s
        | Production j (Symbols ss) <- ps
        , j == i
        , NonTerminal s <- ss
        ]

    ps' = dce [ Production i (Symbols (concatMap inline ss))
              | Production i (Symbols ss) <- ps
              ]

    dce xs = [ Production i ss | Production i ss <- xs, i `elem` live ]
      where live = s : 
              [ s
              | Production _ (Symbols ss) <- xs            
              , NonTerminal s <- ss
              ] 

    count = 
      [ (head v,length v)
      | v <- group $ sort [ i | Production i _ <- ps ]
      ]

    inline (Terminal p) = [Terminal p]
    inline (NonTerminal i) = 
      if i `elem` acyclic &&  fromJust (lookup i count) == 1
      then case find i of
             [Production _ (Symbols ss)] -> ss
             _ -> error "impossible"
      else [NonTerminal i]

    find i = [ p | p@(Production j _) <- ps, i == j ]

    isNotEmpty (Terminal p) = True
    isNotEmpty (NonTerminal i) = i `notElem` empty

    empty =
      [ i
      | Production i (Symbols []) <- ps 
      , fromJust (lookup i count) == 1
      ]
{-
fixGrammer :: (Grammar -> Grammar) -> Grammar -> Grammar
fixGrammer f g0@(Grammar ps0 s0 names0) 
    | s0 == s1 && names0 == names1 && map 

  where
    g1@(Grammar ps1 s1 names1) = f g0
-}
main = do
  print "Starting"
  g <- reifyGraph number
  print g
  let gr = parseGraphToGrammar g
  print gr
  print $ removeEmptyProductionsGrammar gr
  let (gr2, _, _, _) = removeEmptyProductionsGrammar gr
  print gr2
  print $ removeEmptyProductionsGrammar gr2
  let (gr3, _, _, _) = removeEmptyProductionsGrammar gr2
  print gr3
  print $ removeEmptyProductionsGrammar gr3
  let (gr4, _, _, _) = removeEmptyProductionsGrammar gr3
  print gr4
  print $ removeEmptyProductionsGrammar gr4
