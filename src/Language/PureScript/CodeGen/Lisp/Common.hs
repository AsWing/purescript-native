-- |
-- Common code generation utility functions
--
module Language.PureScript.CodeGen.Lisp.Common where

import Data.Char
import Data.List (intercalate)

import Language.PureScript.Crash
import Language.PureScript.Names

-- moduleNameToLisp :: ModuleName -> String
-- moduleNameToLisp (ModuleName pns) =
--   let name = intercalate "_" (runProperName `map` pns)
--   in if nameIsLispBuiltIn name then "!!" ++ name else name

-- |
-- Convert an Ident into a valid Lisp identifier:
--
--  * Alphanumeric characters are kept unmodified.
--
--  * Reserved Lisp identifiers are prefixed with '!!'.
--
--  * Symbols are prefixed with '!' followed by a symbol name or their ordinal value.
--
identToLisp :: Ident -> String
identToLisp (Ident name)
  | nameIsLispReserved name || nameIsLispBuiltIn name = "!!" ++ name
  | otherwise = concatMap identCharToString name
identToLisp (Op op) = concatMap identCharToString op
identToLisp (GenIdent _ _) = internalError "GenIdent in identToLisp"

-- |
-- Test if a string is a valid Lisp identifier without escaping.
--
identNeedsEscaping :: String -> Bool
identNeedsEscaping s = s /= identToLisp (Ident s)

-- |
-- Attempts to find a human-readable name for a symbol, if none has been specified returns the
-- ordinal value.
--
identCharToString :: Char -> String
identCharToString c | isAlphaNum c = [c]
identCharToString '_' = "_"
identCharToString '.' = "!dot"
identCharToString '$' = "!dollar"
identCharToString '~' = "!tilde"
identCharToString '=' = "!eq"
identCharToString '<' = "!less"
identCharToString '>' = "!greater"
identCharToString '!' = "!"
identCharToString '#' = "!hash"
identCharToString '%' = "!percent"
identCharToString '^' = "!up"
identCharToString '&' = "!amp"
identCharToString '|' = "!bar"
identCharToString '*' = "!times"
identCharToString '/' = "!div"
identCharToString '+' = "!plus"
identCharToString '-' = "!minus"
identCharToString ':' = "!colon"
identCharToString '\\' = "!bslash"
identCharToString '?' = "!qmark"
identCharToString '@' = "!at"
identCharToString '\'' = "*"
identCharToString c = '!' : show (ord c)

-- |
-- Checks whether an identifier name is reserved in Lisp.
--
nameIsLispReserved :: String -> Bool
nameIsLispReserved name =
  name `elem` lispAnyReserved

-- |
-- Checks whether a name matches a built-in value in Lisp.
--
nameIsLispBuiltIn :: String -> Bool
nameIsLispBuiltIn name =
  elem name
    [
    ]

lispAnyReserved :: [String]
lispAnyReserved =
  concat
    [ lispReserved
    , lispLiterals
    ]

lispReserved :: [String]
lispReserved =
  [ "alias"
  , "and"
  , "compare"
  , "complement"
  , "cond"
  , "declare"
  , "def"
  , "defn"
  , "do"
  , "fn"
  , "hash-map"
  , "if"
  , "import"
  , "let"
  , "letfn"
  , "list"
  , "load"
  , "loop"
  , "map"
  , "new"
  , "not"
  , "ns"
  , "or"
  , "require"
  , "refer"
  , "return"
  , "seq"
  , "throw"
  , "try"
  , "use"
  , "var"
  , "vec"
  , "vector"
  , "void"
  , "while"
  , "when"
  ]

lispLiterals :: [String]
lispLiterals =
  [ "null"
  , "true"
  , "false"
  ]

normalizedName :: String -> String
normalizedName ('_' : s) | last s == '_', s' <- init s, nameIsLispReserved s' = s'
normalizedName s = s
