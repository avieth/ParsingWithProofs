import Prelude.Chars

-- ||| I still can't figure out how to work with Idris Strings :) So I have made
--     my own string datatype (not for efficiency! just for demonstration).
data MyString : Type where
  myEmptyString : MyString
  (:>) : Char -> MyString -> MyString

infixr 10 :>

makeMyString : String -> MyString
makeMyString x with (strM x)
  -- Full disclosure: I have no clue what the hell is going on here. I find
  -- working with strings in Idris to be very confusing due to lack of
  -- documentation.
  makeMyString "" | StrNil = myEmptyString
  makeMyString (strCons s ss) | (StrCons s ss) = s :> (makeMyString ss)

makeString : MyString -> String
makeString myEmptyString = ""
makeString (c :> mstr) = "c" ++ (makeString mstr)

-- ||| Tail r s means r is a tail of s.
data Tail : MyString -> MyString -> Type where
  selfTail : (s : MyString) -> Tail s s
  stillTail : Tail s q -> Tail s (r :> q)

-- We prove transitivity of Tail:
-- If q is a tail of r, and s is a tail of q, then s is a tail of r.
-- We shall use this in our Applicative definition later.
-- Full disclosure: idris wrote this for me via proof search! It's not obvious
-- to my why or whether it is actually what we want.
--transitiveTail : Tail q r -> Tail s q -> Tail s r
--transitiveTail (selfTail q) (selfTail q) = selfTail q
--transitiveTail (selfTail (r :> x)) (stillTail y) = stillTail y
--transitiveTail (stillTail x) (selfTail q) = stillTail x
--transitiveTail (stillTail x) (stillTail y) = stillTail (transitiveTail x (stillTail y))

-- Here's another definition with a perhaps more natural ordering of the
-- parameters. Oddly enough, Idris couldn't solve this one by proof search!
transitiveTail : Tail q r -> Tail r s -> Tail q s
-- In this case, q = r = s so we can get away with selfTail.
transitiveTail (selfTail q) (selfTail q) = selfTail q
-- Here q = r so the second parameters is our proof.
transitiveTail (selfTail q) (stillTail y) = stillTail y
-- Here we have s = y :> q so we can use the first parameter as proof (of the
-- fact that Tail q r, which is all we need because the stillTail constructor
-- tells us that a proof of Tail q r is a proof of Tail q (y :> r))
transitiveTail (stillTail x) (selfTail (y :> q)) = stillTail x
-- And now the tricky part.
transitiveTail (stillTail x) (stillTail z) = stillTail (transitiveTail (stillTail x) z)

NoParse : Type
NoParse = String

-- ||| A Parse x s means an x was parsed from s, and holds some MyString which
--     is a Tail of s.
data Parse : (a : Type) -> (s : MyString) -> Type where
  parse : (x : a) -> (r : MyString) -> Tail r s -> Parse a s

exitParse : Parse a s -> a
exitParse (parse x _ _) = x

-- ||| Definition of a StringParser with a static guarantee that its values can
--     only consume (or leave unchanged) their inputs, they cannot make them
--     grow.
data StringParser : (a : Type) -> Type where
  stringParser : ((s : MyString) -> Either NoParse (Parse a s)) -> StringParser a

runStringParser : StringParser a -> (s : MyString) -> Either NoParse (Parse a s)
runStringParser (stringParser f) = f

parseValue : a -> StringParser a
parseValue x = stringParser (\s => Right (parse x s (selfTail s)))

parseEmpty : StringParser a
parseEmpty = stringParser (\s => Left "empty")

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

parseChar : Char -> StringParser Char
parseChar c = stringParser $ \str =>
  case str of
    myEmptyString => Left "char : no parse"
    c' :> theRest => if c == c'
                     then Right (parse c' theRest (stillTail (selfTail theRest)))
                     else Left "char : no parse"

parseDigit : StringParser Char
parseDigit = stringParser $ \str =>
  case str of
    myEmptyString => Left "digit : no parse"
    c :> theRest => if isDigit c
                    then Right (parse c theRest (stillTail (selfTail theRest)))
                    else Left "digit : no parse"

parseMyString : MyString -> StringParser MyString
parseMyString myEmptyString = pure myEmptyString
parseMyString (c :> mstr) = (map (:>) (parseChar c)) <$> (parseMyString mstr)

parseString : String -> StringParser String
parseString str = map (makeString) (parseMyString (makeMyString str))

data Formula : Type where
  terminal : Bool -> Formula
  conjunction : Formula -> Formula -> Formula
  disjunction : Formula -> Formula -> Formula

instance Show Formula where
  show (terminal False) = "F"
  show (terminal True) = "T"
  show (conjunction f1 f2) = "(" ++ show f1 ++ " ^ " ++ show f2 ++ ")"
  show (disjunction f1 f2) = "(" ++ show f1 ++ " v " ++ show f2 ++ ")"

evalFormula : Formula -> Bool
evalFormula (terminal b) = b
evalFormula (conjunction f1 f2) = evalFormula f1 && evalFormula f2
evalFormula (disjunction f1 f2) = evalFormula f1 || evalFormula f2

parseBool : StringParser Bool
parseBool = map (\_ => True) (parseString "true") <|> map (\_ => False) (parseString "false")
parseTerminal : StringParser Formula
parseTerminal = map terminal parseBool

-- Prefix parsing of formulas.
mutual
  parseConjunction : StringParser Formula
  parseConjunction = do
    parseChar '('
    parseChar '^'
    parseChar ' '
    f1 <- parseFormula
    parseChar ' '
    f2 <- parseFormula
    parseChar ')'
    return $ conjunction f1 f2
  
  parseDisjunction : StringParser Formula
  parseDisjunction = do
    parseChar '('
    parseChar 'v'
    parseChar ' '
    f1 <- parseFormula
    parseChar ' '
    f2 <- parseFormula
    parseChar ')'
    return $ disjunction f1 f2
  
  parseFormula : StringParser Formula
  parseFormula = parseDisjunction <|> parseConjunction <|> parseTerminal

-- No Functor instance for Either a???
eitherMap : (a -> b) -> Either c a -> Either c b
eitherMap f (Right x) = Right (f x)
eitherMap f (Left x) = Left x

checkParse : StringParser a -> String -> Either NoParse a
checkParse parser s = case runStringParser parser (makeMyString s) of
                        x => eitherMap exitParse x
