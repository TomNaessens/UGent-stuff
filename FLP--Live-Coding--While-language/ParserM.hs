-- -- -- |Project: Functionele en Logische Programmeertalen
-- -- -- |Deel: Haskell
-- -- -- |Auteur: Tom Schrijvers, Steven Keuchel (aanvulling Tom Naessens)
-- -- -- |File: ParserM
-- -- -- |      A monadic parser, for parsing purposes!

module ParserM where

import Control.Monad
import Data.Char

newtype Parser a =
  P { runParser :: String -> [(a,String)] }

instance Monad Parser where
  return a = P $ \str -> [(a,str)]
  m >>= f  = P $ \str ->
    [  res  | (a,str')  <- runParser m str
            , res       <- runParser (f a) str'  ]

runP :: Parser a -> String -> Maybe a
runP p str =
  case  [x | (x,"") <- runParser p str ] of
    (x:_)  ->  Just x
    []     ->  Nothing

instance Functor Parser where
  fmap f p = p >>= return . f

class (Functor p, Monad p) => ParserM p where
  item   ::  p Char
  abort  ::  p a
  (\/)   ::  p a -> p a -> p a

instance ParserM Parser where
  item      = P $ \str  ->  case str of
                              (c:cs)  ->  [(c,cs)]
                              []      ->  []
  abort     = P $ \_    ->  []
  p1 \/ p2  = P $ \str  ->  runParser p1 str ++ runParser p2 str

satisfy :: ParserM p => (a -> Bool) -> p a -> p a
satisfy f p = p >>= \a -> if f a then return a else abort

char :: ParserM p => Char -> p Char
char c = satisfy (==c) item

lower :: ParserM p => p Char
lower = satisfy isLower item

digit :: ParserM p => p Int
digit = fmap digitToInt $ satisfy isDigit item

number :: ParserM p => p Int
number = digit >>= go
  where
    go acc = (digit >>= \d -> go (acc * 10 + d)) \/ return acc

-- -- |Extension with functions from Set4 and Set5 and some new functions

-- |Matches an entire string
token :: ParserM p => String -> p String
token str =
    go str
        where go (s:ss) = do x <- char s
                             go ss
              go []     = return str

-- |Extended parser: can also parse expressions like "{Haskell!}"
parens :: ParserM p => p a -> Char -> Char -> p a
parens p c1 c2 =
    do char c1
       y <- p
       char c2
       return y

many :: ParserM p => p a -> p [a]
many p =
    do x  <- p
       x2 <- many p
       return (x:x2)
 \/ return []

some :: ParserM p => p a -> p [a]
some p =
    do x  <- p
       x2 <- many p
       return (x:x2)

sSeq :: ParserM p => p a -> p [a]
sSeq p =
    do whiteSpace
       l  <- p
       whiteSpace
       ls <- many $ do char ';'
                       p
       return $ l:ls
 \/ do token "[]"
       return []


-- |Recognizes multiple lower caracters, comes in handy for our variable names
sLower :: ParserM p => p String
sLower = some lower

-- |Detects whitespace, because we don't like it.
whiteSpace :: ParserM p => p String
whiteSpace = many (char ' ')

-- |Recognizes chars surrounded by whitespace like "3           +  4"
wChar :: ParserM p => Char -> p Char
wChar c = do whiteSpace
             x <- char c
             whiteSpace
             return x
