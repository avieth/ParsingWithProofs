import StringParser

||| All 10 of Canada's provinces, in one little type.
data Province
  = NewfoundlandAndLabrador
  | NovaScotia
  | PrinceEdwardIsland
  | NewBrunswick
  | Quebec
  | Ontario
  | Manitoba
  | Saskatchewan
  | Alberta
  | BritishColumbia

showProvince : Province -> List Char
showProvince NewfoundlandAndLabrador = unpack "Nfld"
showProvince NovaScotia = unpack "NS"
showProvince PrinceEdwardIsland = unpack "PEI"
showProvince NewBrunswick = unpack "NB"
showProvince Quebec = unpack "Que"
showProvince Ontario = unpack "Ont"
showProvince Manitoba = unpack "Man"
showProvince Saskatchewan = unpack "Sas"
showProvince Alberta = unpack "Alb"
showProvince BritishColumbia = unpack "BC"

-- We define a parser for Province in terms of 10 smaller parsers: one for
-- each province.

parseNewfoundlandAndLabrador : StringParser Province
parseNewfoundlandAndLabrador = string "Nfld" $> pure NewfoundlandAndLabrador

parseNovaScotia : StringParser Province
parseNovaScotia = string "NS" $> pure NovaScotia

parsePrinceEdwardIsland : StringParser Province
parsePrinceEdwardIsland = string "PEI" $> pure PrinceEdwardIsland

parseNewBrunswick : StringParser Province
parseNewBrunswick = string "NB" $> pure NewBrunswick

parseQuebec : StringParser Province
parseQuebec = string "Que" $> pure Quebec

parseOntario : StringParser Province
parseOntario = string "Ont" $> pure Ontario

parseManitoba : StringParser Province
parseManitoba = string "Man" $> pure Manitoba

parseSaskatchewan : StringParser Province
parseSaskatchewan = string "Sas" $> pure Saskatchewan

parseAlberta : StringParser Province
parseAlberta = string "Alb" $> pure Alberta

parseBritishColumbia : StringParser Province
parseBritishColumbia = string "BC" $> pure BritishColumbia

parseProvince : StringParser Province
parseProvince =
      parseNewfoundlandAndLabrador
  <|> parseNovaScotia
  <|> parsePrinceEdwardIsland
  <|> parseNewBrunswick
  <|> parseQuebec
  <|> parseOntario
  <|> parseManitoba
  <|> parseSaskatchewan
  <|> parseAlberta
  <|> parseBritishColumbia

-- Here is our seralize/deserialize combo! They're really not of any use to us
-- unless we prove that they actually stand up to their names.
serialize : Province -> List Char
serialize = showProvince

deserialize : List Char -> Maybe Province
deserialize cs = parsedValue (runStringParser parseProvince cs)
-- Oddly enough,
--   deserialize = parsedValue . runStringParser parseProvince
-- doesn't pass the type checker.

||| Theorem: for any Province p, showProvince p always parses to p under
||| parseProvince. This proves that serialize and deserialize are appropriately
||| named.
||| This one takes about 5 minutes for Idris to check!
leftInverse : (p : Province) -> (deserialize (serialize p) = Just p)
leftInverse NewfoundlandAndLabrador = Refl
leftInverse NovaScotia = Refl
leftInverse PrinceEdwardIsland = Refl
leftInverse NewBrunswick = Refl
leftInverse Quebec = Refl
leftInverse Ontario = Refl
leftInverse Manitoba = Refl
leftInverse Saskatchewan = Refl
leftInverse Alberta = Refl
leftInverse BritishColumbia = Refl
