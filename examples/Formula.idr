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
parseTerminal = map Terminal (parseBool <|> parens parseBool)

-- Prefix parsing of formulas.
mutual
  parseConjunctionPrefix : StringParser Formula
  parseConjunctionPrefix = parens $ do
    char '^'
    whitespace
    f1 <- parseFormulaPrefix
    whitespace
    f2 <- parseFormulaPrefix
    return $ Conjunction f1 f2
  
  parseDisjunctionPrefix : StringParser Formula
  parseDisjunctionPrefix = parens $ do
    char 'v'
    whitespace
    f1 <- parseFormulaPrefix
    whitespace
    f2 <- parseFormulaPrefix
    return $ Disjunction f1 f2
  
  parseFormulaPrefix : StringParser Formula
  parseFormulaPrefix =
        parseDisjunctionPrefix
    <|> parseConjunctionPrefix
    <|> parseTerminal

-- Infix parsing of formulas.
mutual
  parseConjunctionInfix : Formula -> StringParser Formula
  parseConjunctionInfix f1 = map (Conjunction f1) (
      whitespace $> char '^' $> whitespace $> parseFormulaInfix
    )

  parseDisjunctionInfix : Formula -> StringParser Formula
  parseDisjunctionInfix f1 = map (Disjunction f1) (
      whitespace $> char 'v' $> whitespace $> parseFormulaInfix
    )

  parseFormulaInfix : StringParser Formula
  parseFormulaInfix = do
    t <- parens parseFormulaInfix <|> parseTerminal
    parseConjunctionInfix t <|> parseDisjunctionInfix t <|> pure t

-- Functor instance for Either a doesn't work for me; complains of incomplete
-- term.
eitherMap : (a -> b) -> Either c a -> Either c b
eitherMap f (Right x) = Right (f x)
eitherMap f (Left x) = Left x

checkParse : StringParser a -> String -> Either NoParse a
checkParse parser s = case runStringParser parser (unpack s) of
                        x => eitherMap exitParse x
