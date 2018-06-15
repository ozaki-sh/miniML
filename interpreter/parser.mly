%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT LT
%token AND OR
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ LETAND
%token RARROW FUN DFUN
%token REC

%token <int> INTV
%token <Syntax.id> ID

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | d=LetDecl SEMISEMI { Decls d }
  | LET REC x=ID EQ FUN p=ID RARROW e=Expr SEMISEMI { RecDecl (x, p ,e) }

LetDecl :
  | LET d1=LetAndDecl d2=LetDecl { d1 :: d2 }
  | LET d=LetAndDecl { [d] }

LetAndDecl :
    x=ID EQ e=Expr LETAND d=LetAndDecl { (x, e) :: d }
  | x=ID EQ e=Expr { [(x, e)] }
  | f=ID e=LetFunExpr LETAND d=LetAndDecl { (f, e) :: d }
  | f=ID e=LetFunExpr { [(f, e)] }
    

Expr :
    e=IfExpr { e }
  | e=OrExpr { e }
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=DFunHeadExpr { e }
  | e=LetRecExpr { e }

OrExpr :
    l=OrExpr OR r=AndExpr { BinOp(Or, l, r) }
  | e=AndExpr { e }

AndExpr :
    l=AndExpr AND r=LTExpr { BinOp(And, l, r) }
  | e=LTExpr { e }

LTExpr : 
    l=PMExpr LT r=PMExpr { BinOp (Lt, l, r) }
  | e=PMExpr { e }

PMExpr :
    l=PMExpr PLUS r=MExpr { BinOp (Plus, l, r) }
  | l=PMExpr MINUS r=MExpr { BinOp (Minus, l, r) }
  | e=MExpr { e }

MExpr : 
    l=MExpr MULT r=AppExpr { BinOp (Mult, l, r) }
  | e=AppExpr { e }

AppExpr :
    l=AppExpr r=FunInfixExpr { AppExp (l, r) }
  | e=FunInfixExpr { e }

FunInfixExpr :
    LPAREN PLUS RPAREN { FunExp ("x", FunExp ("y", BinOp(Plus, Var "x", Var "y"))) }
  | LPAREN MINUS RPAREN { FunExp ("x", FunExp ("y", BinOp(Minus, Var "x", Var "y"))) }
  | LPAREN MULT RPAREN { FunExp ("x", FunExp ("y", BinOp(Mult, Var "x", Var "y"))) }
  | LPAREN LT RPAREN { FunExp ("x", FunExp ("y", BinOp(Lt, Var "x", Var "y"))) }
  | LPAREN AND RPAREN { FunExp ("x", FunExp ("y", BinOp(And, Var "x", Var "y"))) }
  | LPAREN OR RPAREN { FunExp ("x", FunExp ("y", BinOp(Or, Var "x", Var "y"))) }
  | e=AExpr { e }

AExpr :
    i=INTV { ILit i }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | i=ID   { Var i }
  | LPAREN e=Expr RPAREN { e }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) } 

LetExpr :
    LET le=LetAndExpr { let (l, e) = le in LetExp (l, e) }
    
LetAndExpr :
    x=ID EQ e1=Expr LETAND le=LetAndExpr { let (l, e) = le in ((x, e1) :: l, e) } 
  | x=ID EQ e1=Expr IN e2=Expr { ([(x, e1)], e2) }
  | f=ID e1=LetFunExpr LETAND le=LetAndExpr { let (l, e) = le in ((f, e1) :: l, e) } 
  | f=ID e1=LetFunExpr IN e2=Expr { ([(f, e1)], e2) }

LetFunExpr :
    x=ID e=LetFunExpr { FunExp(x, e) }
  | EQ e=Expr { e }

FunExpr :
    e=FunHeadExpr { e }
 
FunHeadExpr :
    FUN e=FunTailExpr { e }

FunTailExpr :
    x=ID e=FunTailExpr { FunExp (x, e) }
  | RARROW e=Expr { e }

DFunHeadExpr :
    DFUN e=DFunTailExpr { e }

DFunTailExpr :
    x=ID e=DFunTailExpr { DFunExp (x, e) }
  | RARROW e=Expr { e }

LetRecExpr :
    LET REC x=ID EQ FUN p=ID RARROW e1=Expr IN e2=Expr { LetRecExp(x, p, e1, e2) }
