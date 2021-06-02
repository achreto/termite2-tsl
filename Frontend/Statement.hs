module Frontend.Statement(Statement(SVarDecl,SReturn,SSeq,SPar,SForever,SDo,
                           SWhile,SFor,SChoice,SPause,SWait,SStop,SBreak,SInvoke,
                           SAssert,SAssume,SAssign,SITE,SCase,SIn, SOut,SMagic,SMagExit,SDoNothing,stLab),
                 stmtVar,
                 sSeq) where
import Prelude hiding ((<>))
import Data.Maybe
import Text.PrettyPrint

import PP
import Pos
import Name
import Frontend.Expr
import Frontend.TVar

-- Statements
data Statement = SVarDecl   {stpos::Pos, stLab::Maybe Ident, svar::Var}
               | SReturn    {stpos::Pos, stLab::Maybe Ident, retval::(Maybe Expr)}
               | SSeq       {stpos::Pos, stLab::Maybe Ident, statements::[Statement]}
               | SPar       {stpos::Pos, stLab::Maybe Ident, procs::[Statement]}
               | SForever   {stpos::Pos, stLab::Maybe Ident, body::Statement}
               | SDo        {stpos::Pos, stLab::Maybe Ident, body::Statement, cond::Expr}
               | SWhile     {stpos::Pos, stLab::Maybe Ident, cond::Expr, body::Statement}
               | SFor       {stpos::Pos, stLab::Maybe Ident, limits::(Maybe Statement, Expr, Statement), body::Statement}
               | SChoice    {stpos::Pos, stLab::Maybe Ident, statements::[Statement]}
               | SPause     {stpos::Pos, stLab::Maybe Ident}
               | SWait      {stpos::Pos, stLab::Maybe Ident, cond::Expr}
               | SStop      {stpos::Pos, stLab::Maybe Ident}
               | SBreak     {stpos::Pos, stLab::Maybe Ident}
               | SInvoke    {stpos::Pos, stLab::Maybe Ident, mname::MethodRef, args::[Maybe Expr]}
               | SAssert    {stpos::Pos, stLab::Maybe Ident, cond::Expr}
               | SAssume    {stpos::Pos, stLab::Maybe Ident, cond::Expr}
               | SAssign    {stpos::Pos, stLab::Maybe Ident, lhs::Expr, rhs::Expr}
               | SITE       {stpos::Pos, stLab::Maybe Ident, cond::Expr, sthen::Statement, selse::(Maybe Statement)}     -- if () then {..} [else {..}]
               | SCase      {stpos::Pos, stLab::Maybe Ident, caseexpr::Expr, cases::[(Expr, Statement)], def::(Maybe Statement)}
               | SIn        {stpos::Pos, stLab::Maybe Ident, lhs::Expr, rhs::Expr}
               | SOut       {stpos::Pos, stLab::Maybe Ident, lhs::Expr, rhs::Expr}
               | SMagic     {stpos::Pos, stLab::Maybe Ident}
               | SMagExit   {stpos::Pos, stLab::Maybe Ident}
               | SDoNothing {stpos::Pos, stLab::Maybe Ident}
instance PP Statement where
    pp s = case stLab s of
                Nothing -> pp' s
                Just l  -> pp l <> char ':' <+> pp' s
        where
        pp' (SVarDecl _ _ d)                   = pp d
        pp' (SReturn  _ _ e)                   = text "return" <+> pp e
        pp' (SSeq     _ _ ss)                  = braces' $ vcat $ map ((<> semi) . pp) ss
        pp' (SPar     _ _ ss)                  = text "fork" $+$ (braces' $ vcat $ map ((<> semi) . pp) ss)
        pp' (SForever _ _ s)                   = text "forever" $+$ pp s
        pp' (SDo      _ _ s cond)              = text "do" $+$ pp s <+> text "while" <+> (parens $ pp cond)
        pp' (SWhile   _ _ cond s)              = (text "while" <+> (parens $ pp cond)) $+$ pp s
        pp' (SFor     _ _ (init, cond, upd) s) = (text "for" <+> (parens $ pp init <> semi <+> pp cond <> semi <+> pp upd)) $+$ pp s
        pp' (SChoice  _ _ ss)                  = text "choice" $+$ (braces' $ vcat $ map ((<> semi) . pp) ss)
        pp' (SPause   _ _)                     = text "pause"
        pp' (SWait    _ _ cond)                = text "wait" <> (parens $ pp cond)
        pp' (SStop    _ _)                     = text "stop"
        pp' (SBreak   _ _)                     = text "break"
        pp' (SInvoke  _ _ m args)              = pp m <+> (parens $ hsep $ punctuate comma $ map pp args)
        pp' (SAssert  _ _ e)                   = text "assert" <+> (parens $ pp e)
        pp' (SAssume  _ _ e)                   = text "assume" <+> (parens $ pp e)
        pp' (SAssign  _ _ l r)                 = pp l <+> char '=' <+> pp r
        pp' (SITE     _ _ cond s1 ms2)         = text "if" <+> (parens $ pp cond) $+$ pp s1 $+$
                                                 (case ms2 of
                                                       Nothing -> empty
                                                       Just s2 -> text "else" $+$ pp s2)
        pp' (SCase    _ _ e cases def)         = text "case" <+> (parens $ pp e) <+> (braces' $ ppcases $+$ ppdef)
                                                 where ppcases = vcat $ map (\(c,s) -> pp c <> colon <+> pp s <> semi) cases
                                                       ppdef = case def of 
                                                                    Nothing -> empty
                                                                    Just s  -> text "default" <> colon <+> pp s <> semi
        pp' (SIn _ _ l r)                      = pp l <+> text "<<" <+> pp r
        pp' (SOut _ _ l r)                     = pp l <+> text ">>" <+> pp r
        pp' (SMagic   _ _)                     = text "..."
        pp' (SMagExit _ _)                     = text "exit"
        pp' (SDoNothing _ _)                   = text "do_nothing"

instance WithPos Statement where
    pos       = stpos
    atPos s p = s{stpos = p}

instance Show Statement where
    show = render . pp

stmtVar :: Statement -> [Var]
stmtVar (SVarDecl _ _ v)              = [v]
stmtVar (SSeq     _ _ ss)             = concat $ map stmtVar ss
stmtVar (SPar     _ _ ss)             = concat $ map stmtVar ss
stmtVar (SForever _ _ s)              = stmtVar s
stmtVar (SDo      _ _ s _)            = stmtVar s
stmtVar (SWhile   _ _ _ s)            = stmtVar s
stmtVar (SFor     _ _ (init,_,inc) s) = concat $ map stmtVar $ inc:s:(maybeToList init)               
stmtVar (SChoice  _ _ ss)             = concat $ map stmtVar ss
stmtVar (SITE     _ _ _ ts es)        = concat $ map stmtVar $ ts:(maybeToList es)
stmtVar (SCase    _ _ _ cs def)       = concat $ map stmtVar $ (snd $ unzip cs) ++ (maybeToList def)
stmtVar _                             = []

sSeq :: Pos -> Maybe Ident -> [Statement] -> Statement
sSeq p l [s] = s{stLab = l}
sSeq p l ss = SSeq p l ss


