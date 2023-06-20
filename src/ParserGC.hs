module ParserGC(
  parseGcSeq,       --     String ->  IO ( Either ParseError (GenClauseSequent Name) )
  parseFileGcSeq    --   FilePath ->  IO ( Either ParseError (GenClauseSequent Name) )
  )
 where



import Text.Parsec.Char
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Language
-- import Types



languageDef =
   emptyDef { Token.commentStart    = "/*" ,
              Token.commentEnd      = "*/" ,
              Token.commentLine     = "%" ,
              Token.identStart      = letter ,
              Token.identLetter     = alphaNum <|> oneOf "!$?^+-_",
              Token.reservedOpNames = [ "$false", "~", "|", "#", "=/=>" , "-/->",  "==>" ]
            }


lexer = Token.makeTokenParser languageDef

lexeme     = Token.lexeme     lexer 
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    -- parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
comma      = Token.comma      lexer -- parses a comma
dot        = Token.dot        lexer -- parses a dot
whiteSpace = Token.whiteSpace lexer -- parses whitespace


{-

* A gc (general clause) has the form

 d1 | d2| ... | ~c1| ~c2 | a1 =/=> b1 |   a2 =/=> b2 | ...


where:

-  a1, a2, ...  c1, c2 ...  d1, d2 ... are atoms
-  b1, b2 ... are atoms or $false
-   =/=> can be replaced by  # or -/->

* A gcSeq (sequent) has the form


 gc1 , gc2  , ... , gcn ==>  r

where r is an atom or $false 

-}

gcSeqDef :: Parser (GenClauseSequent Name)
gcSeqDef =
  do
    skipMany lineComment
    spaces
    gcs <-  (sepBy1 gc comma)
    reservedOp "==>"
    r <- identifier
    eof
    return $ mkGenClauseSequent gcs r


-- line starting with "%", possibly followed by spaces (e.g., empty lines)
lineComment :: Parser ()
lineComment =
  ( string "%" >> manyTill anyChar endOfLine >>  spaces >> return () )  





-- parse a gc
gc :: Parser (GenClause Name)
gc =
  sepBy1 gLit ( reservedOp "|" )


-- parse a gen. literal
gLit :: Parser (GenLit Name)
gLit =
  try  notImplGLit  --  ## do not change order ! ##
  <|>
  try negGLit
  <|>
  atomicGLit 
  <?> "gLit"


atomicGLit :: Parser (GenLit Name)
atomicGLit = 
  At <$> identifier
  <?> "Atomic gc"

negGLit :: Parser (GenLit Name)
negGLit =
    reservedOp "~" >> Not <$> identifier



notImplOp ::  Parser ()
notImplOp =
   reservedOp "#"
   <|>
   reservedOp "=/=>"
    <|>
   reservedOp "-/->"


identifierOrFalse ::  Parser Name
identifierOrFalse =
   ( reserved "$false" >> return "$false" )
   <|>
   identifier 
  
notImplGLit :: Parser (GenLit Name)
notImplGLit =
  do
    a <- identifier
    notImplOp 
    b <- identifierOrFalse
    return $ a :-/->: b


-- MAIN  

parseGcSeq ::  String -> IO ( Either ParseError (GenClauseSequent Name) )
parseGcSeq str = return $  parse gcSeqDef "" str


parseFileGcSeq :: FilePath ->  IO ( Either ParseError (GenClauseSequent Name ) )
parseFileGcSeq  = parseFromFile gcSeqDef   
 
{-
main :: IO ()
main =
  do
    args <- getArgs
    f <- parseFile $ List.head args  
    print f
-}
