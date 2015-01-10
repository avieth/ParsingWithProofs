import StringParser

data Formula : Type where
  Terminal : Bool -> Formula
  Conjunction : Formula -> Formula -> Formula
  Disjunction : Formula -> Formula -> Formula

instance Show Formula where
  show (Terminal False) = "F"
  show (Terminal True) = "T"
  show (Conjunction f1 f2) = "(" ++ show f1 ++ " ^ " ++ show f2 ++ ")"
  show (Disjunction f1 f2) = "(" ++ show f1 ++ " v " ++ show f2 ++ ")"

evalFormula : Formula -> Bool
evalFormula (Terminal b) = b
evalFormula (Conjunction f1 f2) = evalFormula f1 && evalFormula f2
evalFormula (Disjunction f1 f2) = evalFormula f1 || evalFormula f2

parseBool : StringParser Bool
parseBool = (string "true" $> pure True) <|> (string "false" $> pure False)

parseTerminal : StringParser Formula
parseTerminal = map Terminal parseBool

-- Prefix parsing of formulas.
mutual
  parseConjunction : StringParser Formula
  parseConjunction = parens $ do
    char '^'
    whitespace
    f1 <- parseFormula
    whitespace
    f2 <- parseFormula
    return $ Conjunction f1 f2
  
  parseDisjunction : StringParser Formula
  parseDisjunction = parens $ do
    char 'v'
    whitespace
    f1 <- parseFormula
    whitespace
    f2 <- parseFormula
    return $ Disjunction f1 f2
  
  parseFormula : StringParser Formula
  parseFormula = parseDisjunction <|> parseConjunction <|> parseTerminal

-- No Functor instance for Either a???
eitherMap : (a -> b) -> Either c a -> Either c b
eitherMap f (Right x) = Right (f x)
eitherMap f (Left x) = Left x

checkParse : StringParser a -> String -> Either NoParse a
checkParse parser s = case runStringParser parser (unpack s) of
                        x => eitherMap exitParse x
