module Main where

-- import System.Environment
import Text.ParserCombinators.Parsec

main :: IO ()
main = do
    putStrLn $ readExpr "(\\a:B.(y u))"
    putStrLn $ readExpr "(λx:α.(y u))"
    putStrLn $ readExpr "(λy : α . (y u))"
    putStrLn $ readExpr "(y u)"
    putStrLn $ readExpr "ident"
    putStrLn $ readExpr "(λα : ∗ . (Πx:α.bottom))A" -- TODO not exhaustive ???
    putStrLn $ readExpr "((λα : ∗ . (Πx:α.bottom)) A)"
{- $>
main
<$
-}

-- newtype AVariable = String
-- data LambdaExpr where
--     LambdaAbstraction :: Variable -> LambdaExpr -> LambdaExpr
--     Variable :: String -> LambdaExpr
--     Application :: LambdaExpr -> LambdaExpr -> LambdaExpr
data LambdaExpr
    = Variable String
    | Box
    | Star
    | Application LambdaExpr LambdaExpr
    | LambdaAbstraction LambdaExpr (Maybe LambdaExpr) LambdaExpr
    | PiAbstraction LambdaExpr (Maybe LambdaExpr) LambdaExpr
    deriving (Show)

parseVariable :: Parser LambdaExpr
parseVariable = do
    x <- many1 letter
    return $ Variable x

parseBox :: Parser LambdaExpr
parseBox = do
    _ <-
        char '!' -- Firefox & Chrome
            <|> char '□'
            <|> char '#'
    return Box

parseStar :: Parser LambdaExpr
parseStar = do
    _ <- char '∗' <|> char '*'
    return Star

-- ∅(∗ : !
-- E = V | ! | ∗ |(EE)|(λV : E . E)|(ΠV : E . E) .
-- {(∗, ∗), (!, ∗)},
parseApplication :: Parser LambdaExpr
parseApplication = do
    _ <- char '('
    a <- parseExpr
    _ <- spaces
    b <- parseExpr
    _ <- char ')'
    return $ Application a b

parseLambdaAbstraction :: Parser LambdaExpr
parseLambdaAbstraction = do
    _ <- char '('
    _ <- char '\\' <|> char 'λ'
    x <- parseExpr -- TODO only Variable
    -- TODO type optional?
    _ <- spaces
    _ <- char ':'
    _ <- spaces
    xType <- parseExpr
    -- type end
    _ <- spaces
    _ <- char '.'
    _ <- spaces
    body <- parseExpr
    _ <- char ')'
    return $ LambdaAbstraction x (Just xType) body

-- TODO arrow notation: A → B for Πx : A . B,  in case x \not\in FV (B)
parsePiAbstraction :: Parser LambdaExpr
parsePiAbstraction = do
    _ <- char '('
    _ <- char 'Π' <|> char '/'
    x <- parseExpr -- TODO only Variable
    -- TODO type optional?
    _ <- spaces
    _ <- char ':'
    _ <- spaces
    xType <- parseExpr
    -- type end
    _ <- spaces
    _ <- char '.'
    _ <- spaces
    body <- parseExpr
    _ <- char ')'
    return $ PiAbstraction x (Just xType) body

parseExpr :: Parser LambdaExpr
parseExpr =
    parseVariable
        <|> parseBox
        <|> parseStar
        <|> try parseApplication
        <|> try parseLambdaAbstraction
        <|> parsePiAbstraction

readExpr :: String -> String
readExpr input = case parse parseExpr "lisp" input of
    Left err -> "No match: " ++ show err
    Right v -> show v

-- TODO parseJudgement
