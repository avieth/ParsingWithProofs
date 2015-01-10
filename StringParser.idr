module StringParser

import Prelude.Chars

-- ||| Tail r s means r is a tail of s.
data Tail : List Char -> List Char -> Type where
  SelfTail : (s : List Char) -> Tail s s
  StillTail : Tail s q -> Tail s (r :: q)

-- ||| Theorem: Tail is transitive.
transitiveTail : Tail q r -> Tail r s -> Tail q s
-- In this case, q = r = s so we can get away with SelfTail.
transitiveTail (SelfTail q) (SelfTail q) = SelfTail q
-- Here q = r so the second parameters is our proof.
transitiveTail (SelfTail q) (StillTail y) = StillTail y
-- Here we have s = y :> q so we can use the first parameter as proof (of the
-- fact that Tail q r, which is all we need because the StillTail constructor
-- tells us that a proof of Tail q r is a proof of Tail q (y :> r))
transitiveTail (StillTail x) (SelfTail (y :: q)) = StillTail x
-- And now the tricky part.
transitiveTail (StillTail x) (StillTail z) = StillTail (transitiveTail (StillTail x) z)

data NoParse = MkNoParse String

-- ||| A Parse x s means an x was parsed from s, and holds some MyString which
--     is a Tail of s.
data Parse : (a : Type) -> (s : List Char) -> Type where
  parse : (x : a) -> (r : List Char) -> Tail r s -> Parse a s

exitParse : Parse a s -> a
exitParse (parse x _ _) = x

-- ||| Definition of a StringParser with a static guarantee that its values can
--     only consume (or leave unchanged) their inputs, they cannot make them
--     grow.
data StringParser : (a : Type) -> Type where
  stringParser : ((s : List Char) -> Either NoParse (Parse a s)) -> StringParser a

runStringParser : StringParser a -> (s : List Char) -> Either NoParse (Parse a s)
runStringParser (stringParser f) = f

-- ||| Monadic return, applicative pure: give a fixed value and consume no input.
parseValue : a -> StringParser a
parseValue x = stringParser (\s => Right (parse x s (SelfTail s)))

-- ||| Alternative empty: always a NoParse.
parseEmpty : StringParser a
parseEmpty = stringParser (\s => Left (MkNoParse "empty"))

instance Functor StringParser where
  map f parser = stringParser $ \str =>
    case runStringParser parser str of
      Left noParse => Left noParse
      Right (parse x s t) => Right (parse (f x) s t)

instance Applicative StringParser where
  pure = parseValue
  parser1 <$> parser2 = stringParser $ \str =>
    case runStringParser parser1 str of
      Left noParse => Left noParse
      Right (parse f s t) => case runStringParser parser2 s of
                               Left noParse => Left noParse
                               Right (parse x s' t') => Right (parse (f x) s' (transitiveTail t' t))

instance Alternative StringParser where
  empty = parseEmpty
  parser1 <|> parser2 = stringParser $ \str =>
    case runStringParser parser1 str of
      Right p => Right p
      Left noParse => runStringParser parser2 str

instance Monad StringParser where
  parser1 >>= k = stringParser $ \str =>
    case runStringParser parser1 str of
      Left noParse => Left noParse
      -- Can't just do this, because we have to supply further proof of Tail.
      --Right (parse x s t) => runStringParser (k x) s
      Right (parse x s t) => case runStringParser (k x) s of
                               Left noParse => Left noParse
                               Right (parse x s' t') => Right (parse x s' (transitiveTail t' t))

many1 : StringParser a -> StringParser (List a)
many1 parser = map (::) parser <$> (many1 parser <|> pure [])

many : StringParser a -> StringParser (List a)
many parser = many1 parser <|> pure []

count : (n : Nat) -> StringParser a -> StringParser (Vect n a)
count Z _ = pure []
count (S k) parser = map (::) parser <$> count k parser

-- ||| Parse the first zero or more times until the second succeeds.
manyTill : StringParser a -> StringParser b -> StringParser (List a)
manyTill parserA parserB = (parserB $> pure []) <|> (map (::) parserA <$> manyTill parserA parserB)

-- ||| Parse one or more occurrences of the first parser, separated by the
--     second parser.
sepBy1 : StringParser a -> StringParser sep -> StringParser (List a)
sepBy1 parserA parserSep = map (::) parserA <$> many (parserSep $> parserA)

sepBy : StringParser a -> StringParser sep -> StringParser (List a)
sepBy parserA parserSep = sepBy1 parserA parserSep <|> pure []

skipMany1 : StringParser a -> StringParser ()
skipMany1 parser = many1 parser $> pure ()

skipMany : StringParser a -> StringParser ()
skipMany parser = many parser $> pure ()

eitherP : StringParser a -> StringParser b -> StringParser (Either a b)
eitherP parserA parserB = map Left parserA <|> map Right parserB

choice : Alternative f => List (f a) -> f a
choice [] = empty
choice (f :: fs) = f <|> choice fs

-- ||| Parse only if at the end of the input.
endOfInput : StringParser ()
endOfInput = stringParser $ \str =>
  case str of
    [] => Right (parse () [] (SelfTail []))
    _ => Left (MkNoParse "end : no parse")

-- ||| This parser always parses; gives an indication of whether the end of
--     input has been reached.
atEnd : StringParser Bool
atEnd = (endOfInput $> pure True) <|> pure False

char : Char -> StringParser Char
char c = stringParser $ \str =>
  case str of
    [] => Left (MkNoParse "char : no parse")
    c' :: theRest => if c == c'
                     then Right (parse c' theRest (StillTail (SelfTail theRest)))
                     else Left (MkNoParse "char : no parse")

digit : StringParser Char
digit = stringParser $ \str =>
  case str of
    [] => Left (MkNoParse "digit : no parse")
    c :: theRest => if isDigit c
                    then Right (parse c theRest (StillTail (SelfTail theRest)))
                    else Left (MkNoParse "digit : no parse")

-- ||| Consume zero or more space, newline, tab, and carriage return.
whitespace : StringParser ()
whitespace = many (choice [char ' ', char '\n', char '\t', char '\r']) $> pure ()

symbol : List Char -> StringParser (List Char)
symbol [] = pure []
symbol (c :: cs) = map (::) (char 'c') <$> symbol cs

string : String -> StringParser (List Char)
string = symbol . unpack

-- ||| Parse something enclosed in parentheses, with whitespace admitted between
--     the parens and the content.
parens : StringParser a -> StringParser a
parens parser = char '(' $> whitespace $> parser <$ whitespace <$ char ')'
