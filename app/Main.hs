module Main where

-- import System.Environment
import Text.ParserCombinators.Parsec

main :: IO ()
main = do
    putStrLn $ readExpr "(\\a.(y u))"
    putStrLn $ readExpr "(λα.(y u))"
    putStrLn $ readExpr "(λα . (y u))"
    putStrLn $ readExpr "(y u)"
    putStrLn $ readExpr "ident"

{- $>
main
<$
-}

-- newtype AIdentifier = String
-- data LambdaExpr where
--     Abstraction :: Identifier -> LambdaExpr -> LambdaExpr
--     Identifier :: String -> LambdaExpr
--     Application :: LambdaExpr -> LambdaExpr -> LambdaExpr
data LambdaExpr
    = Identifier String
    | Abstraction String LambdaExpr
    | Application LambdaExpr LambdaExpr
    deriving (Show)

-- parseAbstraction :: Parser LambdaExpr
-- parseAbstraction =

parseIdentifier :: Parser LambdaExpr
parseIdentifier = do
    x <- many1 letter
    return $ Identifier x

parseAbstraction :: Parser LambdaExpr
parseAbstraction = do
    _ <- char '('
    _ <- char '\\' <|> char 'λ'
    x <- many1 letter
    _ <- spaces
    _ <- char '.'
    _ <- spaces
    body <- parseExpr
    _ <- char ')'
    return $ Abstraction x body

parseApplication :: Parser LambdaExpr
parseApplication = do
    _ <- char '('
    a <- parseExpr
    _ <- spaces
    b <- parseExpr
    _ <- char ')'
    return $ Application a b

parseExpr :: Parser LambdaExpr
parseExpr = parseIdentifier <|> try parseAbstraction <|> parseApplication

readExpr :: String -> String
readExpr input = case parse parseExpr "lisp" input of
    Left err -> "No match: " ++ show err
    Right v -> show v
