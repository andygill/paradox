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
  mapDeRef _ (EmptyParser) = pure $ EmptyP
  mapDeRef f (AltParser g h) = AltsP <$> f g <*> f h
  mapDeRef _ (SatParser p)   = pure (SatP p)
  mapDeRef f (AsParser p str) = flip AsP str <$> f p

-----
-- Small example of the parser
-- numbers

whitespace :: Parser ()
whitespace = some (satisfy isSpace) *> pure () `as` "whitespace"

whitespaced :: Parser a -> Parser a
whitespaced p = whitespace *> p <* whitespace

digit :: Parser Int
digit = (\ c -> read [c]) <$> satisfy isDigit `as` "digit"

number :: Parser Int
number = read <$> whitespaced (some (satisfy isDigit)) `as` "number"

example :: Parser ()
example =  (\ () () -> ()) <$> example <*> example
       <|> satisfy (== '#') *> pure ()

symbol :: String -> Parser ()
symbol str = whitespaced (sequenceA [satisfy (== c) | c <- str ]) *> pure () `as` show str

adder :: Parser ()
adder = (\ () _ () -> ()) <$> adder <*> symbol "+" <*> adder
    <|> (\ () _ () -> ()) <$> adder <*> symbol "-" <*> adder
    <|> const () <$> number

-----

data P :: * -> * where
   PureP :: P u
   ApP :: u -> u -> P u
   AltsP :: u -> u -> P u
   EmptyP :: P u
   SatP :: (Char -> Bool) -> P u
   AsP :: u -> String -> P u

instance Show u => Show (P u) where
  show PureP = "Pure"
  show (ApP f g) = "App "  ++ show [f,g]
  show (AltsP a b) = "Alt "  ++ show [a,b]
  show EmptyP = "Empty"
  show (SatP _) = "Sat *"
  show (AsP u s) = "As " ++ show u ++ " " ++ show s

newtype Symbol = Symbol Int
  deriving (Eq, Ord)

instance Show Symbol where
  show (Symbol s) = "s" ++ show s

-- Direct traffic through the parser
-- The only choice is <|>, so we signal
-- what productions are Left or Right.
-- We need to have them in the symbol list
-- because we inline productions.

data Sign = L | R
  deriving (Eq, Ord, Show)

newtype Symbols = Symbols [Either Sign Symbol]
  deriving (Eq, Ord)

instance Show Symbols where
  show (Symbols ss) = unwords $ map (either show show) ss

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
      unlines (
        ("names: " ++ show as)  :
        ("terminal: " ++ show (map fst ts))  :
        ("start: " ++ show s) : 
        terms) ++ show scc
    where
      terms = concatMap group scc

      group (G.CyclicSCC is) = ["-- rec"] ++ concatMap (map show) (map find is) ++ [""]
      group (G.AcyclicSCC i) = map show $ find i

      find :: Symbol -> [Production]
      find i = [ p | p@(Production j _) <- ps, i == j ]

      scc = G.stronglyConnComp
            [ (i, i, nub (symbolsIn i))
            | i <- nub [ j | Production j _ <- ps ]
            ]

      symbolsIn i = 
          [ s
          | Production j (Symbols ss) <- ps
          , j == i
          , Right s <- ss
          ]


parseGraphToGrammar :: Graph P -> Grammar
parseGraphToGrammar (Graph gs s) = Grammar ps (Symbol s) ts names
  where
    ps    = concatMap mkProds gs

    mkProds (i, PureP)     = [ mkProd i [] ]
    mkProds (i, ApP s1 s2) = [ mkProd i [Right (Symbol s1), Right (Symbol s2) ] ]
    mkProds (i, AltsP s1 s2)  = 
        [ mkProd i [Left d, Right $ Symbol s]
        | (d,s) <- [(L, s1), (R, s2)]
        ]
              
    mkProds (i, SatP p)    = [ ]
    mkProds (i, AsP s _)   = [ mkProd i [Right (Symbol s)] ]

    mkProd i ss = Production (Symbol i) $ Symbols ss

    ts    = [ (Symbol i,p) | (i, SatP p) <- gs ]
    names = [ (Symbol i,n) | (i, AsP _ n) <- gs ]

removeEmptyProductionsGrammar :: Grammar -> Grammar
removeEmptyProductionsGrammar (Grammar ps s ts names) =
    traceShow ("aliases", aliases) $ 
    Grammar ps' s ts (nub (names ++ aliases))
  where
    named = fst <$> names

    aliases = [ (s,n)
              | (i,n) <- names
              , let ps' = [ p | p@(Production j (Symbols ss)) <- ps, i == j ]
              , length ps' == 1 -- only one choise
              , Production _ (Symbols [Right s]) <- ps'
              ]

    scc = G.stronglyConnComp
          [ (i, i, nub (symbolsIn i))
          | i <- nub [ j | Production j _ <- ps ]
          ]
    acyclic = [ i | G.AcyclicSCC i <- scc ]

    symbolsIn i = 
        [ s
        | Production j (Symbols ss) <- ps
        , j == i
        , Right s <- ss
        ]

    ps' = dce [ Production i (Symbols (concatMap inline ss))
              | Production i (Symbols ss) <- ps
              ]

    dce xs = [ Production i ss | Production i ss <- xs, i `elem` live ]
      where live = s : 
              [ s
              | Production _ (Symbols ss) <- xs            
              , Right s <- ss
              ] 

    count = 
      [ (head v,length v)
      | v <- group $ sort [ i | Production i _ <- ps ]
      ]

    isNonTerminal s = isNothing (lookup s ts)

    inline (Left d) = [Left d] -- signposts stay
    inline (Right i)
      | isNonTerminal i && i `elem` acyclic && i `notElem` named =
        case find i of
          [Production _ (Symbols ss)] -> ss
          _ -> [Right i]
      | isNonTerminal i =
        -- Really need to do a loop-break here.
        -- s1 -> s2; s2 -> s1, will break.
        -- But this is a S ==>* S example.
        case find i of
          [Production _ (Symbols ss)] | length [ () | Right _ <- ss ] == 1 -> ss
          _ -> [Right i]

      | otherwise = [Right i]

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
--  g <- reifyGraph example
  g <- reifyGraph adder
  print g
  let gr = parseGraphToGrammar g
  print gr
  let gr2 = fixGrammar removeEmptyProductionsGrammar gr
  print gr2

