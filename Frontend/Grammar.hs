{-# LANGUAGE TupleSections, FlexibleContexts, ScopedTypeVariables #-}

module Frontend.Grammar(SpecItem(..),
               Import(..),
               litParser, 
               boolParser,
               grammar,
               detexprParser,
               statementParser,
               statementsParser,
               statements1Parser) where

import Data.Maybe
import qualified Text.PrettyPrint as P

import Control.Applicative hiding (many,optional,Const)
import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Numeric
import Data.List
import Data.Bits

import Ops
import Util hiding (slice,index)
import TSLUtil
import PP
import Pos
import Name
import Frontend.Expr
import Frontend.Statement
import Frontend.Process
import Frontend.Template hiding (Prefix)
import qualified Frontend.Template as Template
import Frontend.TVar
import Frontend.Type
import Frontend.Method
import Frontend.Const
import Frontend.Relation
import Frontend.Transducer

-- exports: all exported parsers must start with removeTabs to get correct position markers
litParser         = removeTabs *> ((\(ELit _ w s r v) -> (w,s,r,v)) <$> elit True)
boolParser        = removeTabs *> ((True <$ reserved "true") <|> (False <$ reserved "false"))
detexprParser     = removeTabs *> detexpr
statementParser   = removeTabs *> statement
statementsParser  = removeTabs *> statements
statements1Parser = removeTabs *> ((optional whiteSpace) *> statements1)

reservedOpNames = ["!", "?", "~", "&", "|", "^", "=>", "||", "&&", "=", "==", "!=", "<", "<=", "<=>", "==>", "<==", ">", ">=", "%", "+", "-", "*", "<<", ">>", "...", "::", "->", "@", "#", "##", "_"]
reservedNames = ["after",
                 "apply",
                 "prefix",
                 "assert",
                 "assume", 
                 "before",
                 "bool",
                 "case",
                 "choice", 
                 "cond",
                 "const",
                 "controllable", 
                 "default",
                 "derive",
                 "do", 
                 "else", 
                 "endtemplate",
                 "enum",
                 "export",
                 "false",
                 "forever", 
                 "fork", 
                 "function", 
                 "goal",
                 "if", 
                 "import",
                 "init",
                 "instance",
                 "mem",
                 "out",
                 "pause",
                 "break",
                 "procedure", 
                 "process",
                 "relation",
                 "return",
                 "rule",
                 "seq",
                 "sint",
                 "stop", 
                 "struct",
                 "task", 
                 "template", 
                 "transducer",
                 "true",
                 "typedef",
                 "uint",
                 "uncontrollable", 
                 "void",
                 "while",
                 "wire",
                 "wait"]

lexer = T.makeTokenParser (emptyDef {T.commentStart      = "/*"
                                    ,T.commentEnd        = "*/"
                                    ,T.commentLine       = "//"
                                    ,T.nestedComments    = True
                                    ,T.identStart        = letter <|> char '_' 
                                    ,T.identLetter       = alphaNum <|> char '_'
                                    ,T.reservedOpNames   = reservedOpNames
                                    ,T.reservedNames     = reservedNames
                                    ,T.opLetter          = oneOf ":!#$%&*+./<=>\\^|-~_"
                                    ,T.caseSensitive     = True})

reservedOp = T.reservedOp lexer
reserved   = T.reserved lexer
identifier = T.identifier lexer
semiSep    = T.semiSep lexer
semiSep1   = T.semiSep1 lexer
colon      = T.colon lexer
commaSep   = T.commaSep lexer
commaSep1  = T.commaSep1 lexer
symbol     = T.symbol lexer
semi       = T.semi lexer
comma      = T.comma lexer
braces     = T.braces lexer
parens     = T.parens lexer
angles     = T.angles lexer
squares    = T.squares lexer
brackets   = T.brackets lexer
natural    = T.natural lexer
decimal    = T.decimal lexer
integer    = T.integer lexer
whiteSpace = T.whiteSpace lexer
lexeme     = T.lexeme lexer
dot        = T.dot lexer
stringLit  = T.stringLiteral lexer
charLit    = T.charLiteral lexer

----------------------------------------------------------------
-- Common declarations that occur in different syntactic scopes
----------------------------------------------------------------

removeTabs = do s <- getInput
                let s' = map (\c -> if' (c == '\t') ' ' c ) s 
                setInput s'          

withPos x = (\s x e -> atPos x (s,e)) <$> getPosition <*> x <*> getPosition

quote :: String -> String
quote s = "\"" ++ s ++ "\""

ident = withPos $ Ident nopos <$> (identifier <|> (quote <$> stringLit))

staticsym = sepBy1 ident (reservedOp "::")
methname = withPos $ MethodRef nopos <$> sepBy1 ident dot

varDecl = withPos $ Var nopos <$> option False (True <$ reserved "mem")
                              <*> typeSpec False
                              <*> ident 
                              <*> optionMaybe (reservedOp "=" *> detexpr)

typeDef = withPos $ TypeDecl nopos <$ reserved "typedef" <*> typeSpec False <*> ident

slice = brackets $ (,) <$> detexpr <*> (colon *> detexpr)
range = brackets $ (,) <$> detexpr <*> (reservedOp "##" *> detexpr)

index = brackets detexpr
field = dot *> ident
ptrfield = reservedOp "->" *> ident

-- Constant declaration
constant = withPos $ Const nopos <$  reserved "const" 
                                     <*> typeSpec False
                                     <*> ident 
                                     <*> (reservedOp "=" *> detexpr)

data TypeMod = ModPtr 
             | ModSequence 
             | ModDim (Maybe Expr)

-- Only parse VarArray if rel is true.  Makes sure that VarArray's can only
-- appear as relation arguments
typeSpec rel = mkType <$> (withPos $  sintType 
                                  <|> uintType 
                                  <|> boolType 
                                  <|> userType 
                                  <|> enumType 
                                  <|> structType) 
                      <*> (many $ (,) <$> ((ModDim <$> (brackets $ if' rel (optionMaybe detexpr) (Just <$> detexpr))) 
                                      <|>  (ModPtr      <$ reservedOp "*")
                                      <|>  (ModSequence <$ reserved "seq")) 
                                      <*> getPosition)

mkType :: TypeSpec -> [(TypeMod, SourcePos)] -> TypeSpec
mkType t [] = t
mkType t ((ModDim Nothing , p):es) = mkType (VarArraySpec (fst $ pos t, p) t) es
mkType t ((ModDim (Just e), p):es) = mkType (ArraySpec (fst $ pos t, p) t e) es
mkType t ((ModSequence, p):es)     = mkType (SeqSpec (fst $ pos t, p) t) es
mkType t ((ModPtr, p):es)          = mkType (PtrSpec (fst $ pos t, p) t) es

sintType   = SIntSpec     nopos <$  reserved "sint" <*> (fromIntegral <$> angles decimal)
uintType   = UIntSpec     nopos <$  reserved "uint" <*> (fromIntegral <$> angles decimal)
boolType   = BoolSpec     nopos <$  reserved "bool"
userType   = UserTypeSpec nopos <$> staticsym
enumType   = EnumSpec     nopos <$  reserved "enum" <*> (braces $ commaSep1 enum)
structType = StructSpec   nopos <$  reserved "struct" <*> (braces $ many1 $ withPos $ Field nopos <$> typeSpec False <*> (ident <* semi))

enum = withPos $ Enumerator nopos <$> ident

-------------------------------------------------------------------------
-- Top-level scope
-------------------------------------------------------------------------

-- A TSL spec is a list of type, constant, and template declarations
data SpecItem = SpImport     Import
              | SpType       TypeDecl
              | SpConst      Const
              | SpTemplate   Template
              | SpTransducer Transducer

instance PP SpecItem where
    pp (SpImport i)     = pp i
    pp (SpType t)       = pp t
    pp (SpConst c)      = pp c
    pp (SpTemplate t)   = pp t
    pp (SpTransducer t) = pp t


data Import = Import Pos Ident
instance PP Import where
    pp (Import _ file) = P.text "import" P.<+> P.char '<' P.<> pp file P.<> P.char '>'
instance WithPos Import where
    pos (Import p _)     = p
    atPos (Import _ i) p = Import p i

-- A TSL spec is a list of template, type, and constant declarations.  
grammar = removeTabs *> ((optional whiteSpace) *> (many decl) <* eof)
decl =  (SpImport <$> imp)
    <|> (SpConst <$> constant <* semi)
    <|> (SpType <$> typeDef <* semi)
    <|> (SpTemplate <$> template)
    <|> (SpTransducer <$> transducer <* semi)
    <?> "constant, type or template declaration"

imp = withPos $ Import nopos <$ reserved "import" <*> (reservedOp "<" *> (withPos $ Ident nopos <$> manyTill anyChar (reservedOp ">")))

------------------------------------------------------------------------
-- Transducer
------------------------------------------------------------------------

transducer = withPos $ Transducer nopos <$ reserved "transducer" <*> ident
                                       <*> (parens $ commaSep1 transducerPort)
                                       <*  reservedOp "->"
                                       <*> (parens $ commaSep transducerPort)
                                       <*> (choice [(\x y -> Left (x,y)) <$> transducerExport <*> transducerComposite, Right <$> statement])

transducerExport = reserved "export" *> (parens $ commaSep portRef)

transducerPort = withPos $ TxPort nopos <$> typeSpec False <*> ident

transducerComposite = braces $ many1 $ transducerInstance <* semi

transducerInstance = withPos $ TxInstance nopos <$ reserved "instance"
                                               <*> ident
                                               <*> ident
                                               <*> (parens $ commaSep $ choice [Nothing <$ reservedOp "*", Just <$> portRef])

portRef = choice [try $ TxLocalRef <$> ident <* dot <*> ident, try $ TxInputRef <$> ident]

------------------------------------------------------------------------
-- Template scope
------------------------------------------------------------------------

template = withPos $ mkTemplate  <$  reserved "template" 
                                <*> ident 
                                <*> option [] (parens $ commaSep $ templateImport) 
                                <*> ((many $ templateItem <* reservedOp ";") <*  reserved "endtemplate")

data TemplateItem = TDerive      Derive
                  | TTypeDecl    TypeDecl
                  | TInstDecl    Instance
                  | TConstDecl   Const
                  | TVarDecl     GVar
                  | TWire        Wire
                  | TInitBlock   Init
                  | TPrefix      Template.Prefix
                  | TProcessDecl Process
                  | TMethod      Method
                  | TGoalDecl    Goal
                  | TRelation    Relation
                  | TApply       Apply

mkTemplate :: Ident -> [Port] -> [TemplateItem] -> Template
mkTemplate n ps is = Template nopos n ps drvs consts types vars wires insts inits als procs meths goals rels apps
    where drvs   = mapMaybe (\i -> case i of 
                                        TDerive d -> Just d
                                        _ -> Nothing) is
          consts = mapMaybe (\i -> case i of 
                                        TConstDecl c -> Just c
                                        _ -> Nothing) is
          types  = mapMaybe (\i -> case i of 
                                        TTypeDecl t -> Just t
                                        _ -> Nothing) is
          vars   = mapMaybe (\i -> case i of 
                                        TVarDecl v -> Just v
                                        _ -> Nothing) is
          insts  = mapMaybe (\i -> case i of 
                                        TInstDecl inst -> Just inst
                                        _ -> Nothing) is
          inits  = mapMaybe (\i -> case i of 
                                        TInitBlock init -> Just init
                                        _ -> Nothing) is
          als    = mapMaybe (\i -> case i of 
                                        TPrefix al -> Just al
                                        _ -> Nothing) is
          wires  = mapMaybe (\i -> case i of 
                                        TWire w -> Just w
                                        _ -> Nothing) is
          procs  = mapMaybe (\i -> case i of 
                                        TProcessDecl p -> Just p
                                        _ -> Nothing) is
          meths  = mapMaybe (\i -> case i of 
                                        TMethod m -> Just m
                                        _ -> Nothing) is
          goals  = mapMaybe (\i -> case i of 
                                        TGoalDecl g -> Just g
                                        _ -> Nothing) is
          rels   = mapMaybe (\i -> case i of
                                        TRelation r -> Just r
                                        _ -> Nothing) is
          apps   = mapMaybe (\i -> case i of
                                        TApply a -> Just a
                                        _ -> Nothing) is
 

templateImport = withPos $ Port nopos <$> ident <*> ident

templateItem =  TDerive      <$> tderive
            <|> TInstDecl    <$> instDecl
            <|> TTypeDecl    <$> typeDef
            <|> TConstDecl   <$> constant
            <|> TVarDecl     <$> try tvarDecl
            <|> TInitBlock   <$> tinitBlock
            <|> TPrefix      <$> tprefix
            <|> TProcessDecl <$> tprocessDecl
            <|> TMethod      <$> tmethodDecl
            <|> TGoalDecl    <$> tgoalDecl
            <|> TWire        <$> twire
            <|> TRelation    <$> trel
            <|> TApply       <$> tapp
            <?> "declaration"

tderive      = withPos $ Derive nopos <$  reserved "derive" 
                                      <*> ident 
instDecl     = withPos $ Instance nopos <$  reserved "instance"
                                        <*> ident
                                        <*> ident
                                        <*> (option [] (parens $ commaSep ident))
tvarDecl     = withPos $ GVar nopos <$> (option False (True <$ reserved "export")) 
                                    <*> varDecl
twire        = withPos $ Wire nopos <$> (option False (True <$ reserved "export")) 
                                    <*  reserved "wire" 
                                    <*> typeSpec False
                                    <*> ident 
                                    <*> optionMaybe (reservedOp "=" *> detexpr)
tinitBlock   = withPos $ Init nopos <$ reserved "init" <*> detexpr
tprefix      = withPos $ Template.Prefix nopos <$ reserved "prefix" <*> statement
tprocessDecl = withPos $ Process nopos <$  reserved "process" 
                                       <*> ident 
                                       <*> statement
tmethodDecl  = withPos $ Method nopos <$> (option False (True <$ reserved "export")) 
                                          <*> methCateg
                                          <*> ((Nothing <$ reserved "void") <|> (Just <$> typeSpec False))
                                          <*> ident
                                          <*> (parens $ commaSep arg)
                                          <*> (option (Left (Nothing, Nothing)) $
                                                   Left <$ reserved "before" <*> ((,) <$> (Just <$> statement) <*> optionMaybe (reserved "after" *> statement))
                                               <|> Left <$ reserved "after" <*> ((Nothing,) <$> (Just <$> statement))
                                               <|> Right <$> statement)
tgoalDecl    = withPos $ Goal nopos <$  reserved "goal" 
                                    <*> (ident <* reservedOp "=") 
                                    <*> detexpr
trel         = withPos $ Relation nopos <$  reserved "relation"
                                        <*> ident
                                        <*> (parens $ commaSep1 rarg)
                                        <*> (many1 $ rule)


tapp         = withPos $ Apply nopos <$  reserved "apply"
                                     <*> ident
                                     <*> (parens $ commaSep detexpr)


methCateg =  (Function <$ reserved "function")
         <|> (Procedure <$ reserved "procedure")
         <|> (Task <$ reserved "task" <*> option Invisible (  Controllable <$ reserved "controllable" 
                                                          <|> Uncontrollable <$ reserved "uncontrollable"))
   
arg = withPos $ Arg nopos <$> (option ArgIn (ArgOut <$ reserved "out")) 
                              <*> typeSpec False
                              <*> ident

rarg = withPos $ RArg nopos <$> typeSpec True <*> ident

rule = withPos $ Rule nopos <$> ruleop <*> relexpr

ruleop  =  (Implies <$ reservedOp "==>")
       <|> (Implied <$ reservedOp "<==")
       <|> (Iff     <$ reservedOp "<=>")

----------------------------------------------------------------
-- Statement
----------------------------------------------------------------

statement =  withPos $
            ((try $ (\l s -> s{stLab = Just l}) <$> (ident <* reservedOp ":") <*> statement')
         <|> statement')

statement' =  withPos $
           ( (try svarDecl)
         <|> sreturn
         <|> smagic 
         <|> sseq
         <|> spar
         <|> sforever
         <|> sdo
         <|> swhile
         <|> sfor
         <|> schoice
         <|> spause
         <|> swait
         <|> sstop
         <|> sbreak
         <|> sassert
         <|> sassume
         <|> site
         <|> scase
         <|> sinp
         <|> sout
         <|> sinvoke
         <|> sassign
         <?> "statement")

statements  = many  $ statement <* semi
statements1 = sepBy1 statement semi

svarDecl = SVarDecl nopos Nothing <$> varDecl
sreturn  = SReturn  nopos Nothing <$ reserved "return" <*> (optionMaybe expr)
sseq     = SSeq     nopos Nothing <$> (braces statements)
spar     = SPar     nopos Nothing <$ reserved "fork" <*> (braces $ many $ statement <* semi)
sforever = SForever nopos Nothing <$ reserved "forever" <*> statement

sdo      = SDo      nopos Nothing <$ reserved "do" <*> statement <* reserved "while" <*> (parens expr)
swhile   = SWhile   nopos Nothing <$ reserved "while" <*> (parens expr) <*> statement
sfor     = SFor     nopos Nothing <$ reserved "for" <*> (parens $ (,,) <$> (optionMaybe statement <* semi) <*> (detexpr <* semi) <*> statement) <*> statement
schoice  = SChoice  nopos Nothing <$ reserved "choice" <*> (braces $ many $ statement <* semi)
spause   = SPause   nopos Nothing <$ reserved "pause"
swait    = SWait    nopos Nothing <$ reserved "wait" <*> (parens detexpr)
sstop    = SStop    nopos Nothing <$ reserved "stop"
sbreak   = SBreak   nopos Nothing <$ reserved "break"
sinvoke  = SInvoke  nopos Nothing <$ isinvoke <*> methname <*> (parens $ commaSep $ choice [Nothing <$ reservedOp "_", Just <$> expr])
    where isinvoke = try $ lookAhead $ methname *> symbol "("
sassert  = SAssert  nopos Nothing <$ reserved "assert" <*> (parens detexpr)
sassume  = SAssume  nopos Nothing <$ reserved "assume" <*> (parens detexpr)
sassign  = SAssign  nopos Nothing <$ isassign <*> detexpr <* reservedOp "=" <*> expr
    where isassign = try $ lookAhead $ expr *> symbol "="
site     = SITE     nopos Nothing <$ reserved "if" <*> (parens expr) <*> statement <*> optionMaybe (reserved "else" *> statement)
scase    = (fmap uncurry (SCase nopos Nothing <$ reserved "case" <*> (parens detexpr))) 
           <*> (braces $ (,) <$> (many $ (,) <$> detexpr <* colon <*> statement <* semi) 
                             <*> optionMaybe (reserved "default" *> colon *> statement <* semi))
sinp     = SIn nopos Nothing <$ isin <*> detexpr <* reservedOp "<<" <*> detexpr
    where isin = try $ lookAhead $ detexpr *> reservedOp "<<"
sout     = SOut nopos Nothing <$ isout <*> expr <* reservedOp ">>" <*> detexpr
    where isout = try $ lookAhead $ expr *> reservedOp ">>"
smagic   = SMagic   nopos Nothing <$ ismagic
                        <* (withPos $ nopos <$ reservedOp "...") 
                        -- <*> ((Left <$ reserved "using" <*> ident) <|> (Right <$ reserved "post" <*> detexpr))
    where ismagic = try $ lookAhead $ reservedOp "..."

------------------------------------------------------------------
-- Expression
------------------------------------------------------------------

term    = parens expr <|> term'
detterm = parens detexpr <|> detterm'
relterm = parens relexpr <|> relterm'


term' = withPos $
       ( elabel
     <|> erel
     <|> estruct True
     <|> etern   True
     <|> eapply  True
     <|> elit    True
     <|> ebool   True
     <|> eterm   True
     <|> ecase   True
     <|> econd   True)

detterm' = withPos $
          ( elabel
        <|> erel
        <|> estruct False
        <|> etern   False
        <|> eapply  False
        <|> elit    False
        <|> ebool   False
        <|> eterm   False
        <|> ecase   False
        <|> econd   False)

relterm' = withPos $
          ( erel
        <|> estruct False
        <|> etern   False
        <|> eapply  False
        <|> elit    False
        <|> ebool   False
        <|> eterm   False
        <|> ecase   False
        <|> econd   False)


elabel      = EAtLab nopos <$> (reservedOp "@" *> ident)
erel        = ERel nopos <$ (reservedOp "?") <*> ident <*> (parens $ commaSep detexpr)
estruct det = EStruct nopos <$ isstruct <*> staticsym <*> (braces $ option (Left []) ((Left <$> namedfields) <|> (Right <$> anonfields)))
    where isstruct = try $ lookAhead $ staticsym *> symbol "{"
          anonfields = commaSep1 (expr' det)
          namedfields = commaSep1 $ ((,) <$ reservedOp "." <*> ident <* reservedOp "=" <*> (expr' det))
eapply  det = EApply nopos <$ isapply <*> methname <*> (parens $ commaSep (choice [Nothing <$ reservedOp "_", Just <$> expr' det]))
    where isapply = try $ lookAhead $ methname *> symbol "("
eterm   det = ETerm nopos <$> staticsym
ebool   det = EBool nopos <$> boolParser
elit    det = lexeme elit'
etern   det = ETernOp nopos <$ reserved "if" <*> (expr' det) <*> (expr' det) <* reserved "else" <*> (expr' det)
ecase   det = (fmap uncurry (ECase nopos <$ reserved "case" <*> (parens detexpr))) 
              <*> (braces $ (,) <$> (many $ (,) <$> detexpr <* colon <*> (expr' det) <* semi) 
                                <*> optionMaybe (reserved "default" *> colon *> (expr' det) <* semi))
econd   det = (fmap uncurry (ECond nopos <$ reserved "cond")) 
               <*> (braces $ (,) <$> (many $ (,) <$> detexpr <* colon <*> (expr' det) <* semi) 
                                 <*> optionMaybe (reserved "default" *> colon *> (expr' det) <* semi))

elit'   = (lookAhead $ char '\'' <|> digit) *> (do w         <- width
                                                   ((s,r),v) <- sradval
                                                   mkLit w s r v)

width = optionMaybe (try $ ((fmap fromIntegral parseDec) <* (lookAhead $ char '\'')))
sradval =  ((,) <$> ((False, Rad2)  <$ (try $ string "'b"))  <*> parseBin)
       <|> ((,) <$> ((True,  Rad2)  <$ (try $ string "'sb")) <*> parseBin)
       <|> ((,) <$> ((False, Rad8)  <$ (try $ string "'o"))  <*> parseOct)
       <|> ((,) <$> ((True,  Rad8)  <$ (try $ string "'so")) <*> parseOct)
       <|> ((,) <$> ((False, Rad10) <$ (try $ string "'d"))  <*> parseDec)
       <|> ((,) <$> ((True,  Rad10) <$ (try $ string "'sd")) <*> parseSDec)
       <|> ((,) <$> ((False, Rad16) <$ (try $ string "'h"))  <*> parseHex)
       <|> ((,) <$> ((True,  Rad16) <$ (try $ string "'sh")) <*> parseHex)
       <|> (((False,Rad10),) <$> parseDec)
parseBin :: Stream s m Char => ParsecT s u m Integer
parseBin = readBin <$> (many1 $ (char '0') <|> (char '1'))
parseOct :: Stream s m Char => ParsecT s u m Integer
parseOct = (fst . head . readOct) <$> many1 octDigit
parseDec :: Stream s m Char => ParsecT s u m Integer
parseDec = (fst . head . readDec) <$> many1 digit
parseSDec = (\m v -> m * v)
            <$> (option 1 ((-1) <$ reservedOp "-"))
            <*> ((fst . head . readDec) <$> many1 digit)
parseHex :: Stream s m Char => ParsecT s u m Integer
parseHex = (fst . head . readHex) <$> many1 hexDigit

mkLit :: Maybe Int -> Bool -> Radix -> Integer -> ParsecT s u m Expr
mkLit Nothing  False Rad10 v                       = return $ ELit nopos (msb v + 1) False Rad10 v
mkLit Nothing  False r     v                       = return $ ELit nopos (msb v + 1) False r     v
mkLit Nothing  True  r     v                       = error "Explicit width required for signed literal"
mkLit (Just w) False r     v | w == 0              = error "Unsigned literals must have width >0"
                             | msb v < w           = return $ ELit nopos w False r v
                             | otherwise           = error "Value exceeds specified width"
mkLit (Just w) True  Rad10 v | w < 2               = error "Signed literals must have width >1"
                             | (msb $ abs v) < w-1 = return $ ELit nopos w True Rad10 v
                             | otherwise           = error "Value exceeds specified width"
mkLit (Just w) True  r     v | w < 2               = error "Signed literals must have width >1"
                             | msb v == w - 1      = do let v' = (foldl' (\_v i -> complementBit _v i) v [0..w-1]) + 1
                                                        return $ ELit nopos w True r (-v')
                             | msb v < w - 1       = return $ ELit nopos w True r v
                             | otherwise           = error "Value exceeds specified width"

expr' True  = expr
expr' False = detexpr

expr = (withPos $ ENonDet nopos Nothing <$ reservedOp "*")
    <|> buildExpressionParser table term
    <?> "expression"

detexpr =  (reservedOp "*" *> unexpected "unexpected * in deterministic expression")
       <|> buildExpressionParser table detterm
       <?> "expression (deterministic)"

relexpr = (reservedOp "*" *> unexpected "unexpected * in relation interpretation")
       <|> buildExpressionParser table relterm
       <?> "expression (relation interpretation)"


pref  p = Prefix  . chainl1 p $ return       (.)
postf p = Postfix . chainl1 p $ return (flip (.))

table = [[postf $ choice [postSlice, postRange, postIndex, postField, postPField]]
        ,[pref  $ choice [elen, prefix "!" Not, prefix "~" BNeg, prefix "-" UMinus, prefix "*" Deref, prefix "&" AddrOf]]
        ,[binary "==" Eq AssocLeft, 
          binary "!=" Neq AssocLeft,
          binary "<"  Lt AssocNone, 
          binary "<=" Lte AssocNone, 
          binary ">"  Gt AssocNone, 
          binary ">=" Gte AssocNone]
        ,[binary "&" BAnd AssocLeft]
        ,[binary "^" BXor AssocLeft]
        ,[binary "|" BOr AssocLeft]
        ,[binary "++" BConcat AssocLeft]
        ,[binary "&&" And AssocLeft]
        ,[binary "||" Or AssocLeft]
        ,[binary "=>" Imp AssocRight]
        ,[binary "*" Mul AssocLeft]
        ,[binary "%" Mod AssocLeft]
        ,[binary "+" Plus AssocLeft]
        ,[binary "-" BinMinus AssocLeft]
        ]

postSlice  = try $ (\s end e -> ESlice (fst $ pos e, end) e s) <$> slice <*> getPosition
postRange  = try $ (\r end a -> ERange (fst $ pos a, end) a r) <$> range <*> getPosition
postIndex  = (\i end e -> EIndex (fst $ pos e, end) e i) <$> index <*> getPosition
postField  = (\f end e -> EField (fst $ pos e, end) e f) <$> field <*> getPosition
postPField = (\f end e -> EPField (fst $ pos e, end) e f) <$> ptrfield <*> getPosition

elen = (\start e -> ELength (start, snd $ pos e) e) <$> getPosition <* reservedOp "#"
prefix n fun = (\start e -> EUnOp (start, snd $ pos e) fun e) <$> getPosition <* reservedOp n
binary n fun = Infix $ (\le re -> EBinOp (fst $ pos le, snd $ pos re) fun le re) <$ reservedOp n
