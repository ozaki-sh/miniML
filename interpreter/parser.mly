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
%token MATCH WITH BAR
%token EMPTY CONS

%token <int> INTV
%token <Syntax.id> ID

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | d=LetDecl SEMISEMI { Decls d }
  | d=LetRecDecl SEMISEMI { RecDecls d }

LetDecl :
  | LET d1=LetAndDecl d2=LetDecl { d1 :: d2 }
  | LET d=LetAndDecl { [d] }

LetAndDecl :
    x=ID EQ e=Expr LETAND d=LetAndDecl { (x, e) :: d }
  | x=ID EQ e=Expr { [(x, e)] }
  | f=ID fe=LetFunHeadExpr LETAND d=LetAndDecl { match fe with 
                                                   FunExp (p ,e) -> (f, FunExp (p, e)) :: d }
  | f=ID fe=LetFunHeadExpr { match fe with FunExp (p, e) -> [(f, FunExp (p, e))] }

LetRecDecl :
  | LET REC d1=LetRecAndDecl d2=LetRecDecl { d1 :: d2 }
  | LET REC d=LetRecAndDecl { [d] }

LetRecAndDecl :
    f=ID EQ fe=FunHeadExpr LETAND d=LetRecAndDecl { match fe with FunExp (p, e) -> (f, p, e) :: d }
  | f=ID EQ fe=FunHeadExpr { match fe with FunExp (p, e) -> [(f, p, e)] }
  | f=ID fe=LetFunHeadExpr LETAND d=LetRecAndDecl { match fe with 
                                                      FunExp (p, e) ->(f, p, e) :: d }
  | f=ID fe=LetFunHeadExpr { match fe with FunExp (p, e) -> [(f, p, e)] }
    

Expr :
    e=IfExpr { e }
  | e=OrExpr { e }
  | e=LetExpr { e }
  | e=FunHeadExpr { e }
  | e=DFunHeadExpr { e }
  | e=LetRecExpr { e }

OrExpr :
    l=OrExpr OR r=AndExpr { BinLogicOp(Or, l, r) }
  | e=AndExpr { e }

AndExpr :
    l=AndExpr AND r=CmpExpr { BinLogicOp(And, l, r) }
  | e=CmpExpr { e }

CmpExpr : 
    l=PMExpr LT r=PMExpr { BinOp (Lt, l, r) }
  | l=CmpExpr EQ r=PMExpr { BinOp (Eq, l, r) }
  | e=PMExpr { e }

ConsExpr :
    l=PMExpr CONS r=ConsExpr { BinOp (Cons, l, t) }
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
  | LPAREN EQ RPAREN { FunExp ("x", FunExp ("y", BinOp(Eq, Var "x", Var "y"))) }
  | LPAREN AND RPAREN { FunExp ("x", FunExp ("y", BinLogicOp(And, Var "x", Var "y"))) }
  | LPAREN OR RPAREN { FunExp ("x", FunExp ("y", BinLogicOp(Or, Var "x", Var "y"))) }
  | e=AExpr { e }

AExpr :
    i=INTV { ILit i }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | i=ID   { Var i }
  | EMPTY  { EmpList }
  | LPAREN e=Expr RPAREN { e }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) } 

LetExpr :
    LET le=LetAndExpr { let (l, e) = le in LetExp (l, e) }
    
LetAndExpr :
    x=ID EQ e1=Expr LETAND le=LetAndExpr { let (l, e2) = le in ((x, e1) :: l, e2) } 
  | x=ID EQ e1=Expr IN e2=Expr { ([(x, e1)], e2) }
  | f=ID e1=LetFunHeadExpr LETAND le=LetAndExpr { let (l, e2) = le in ((f, e1) :: l, e2) } 
  | f=ID e1=LetFunHeadExpr IN e2=Expr { ([(f, e1)], e2) }

LetFunHeadExpr :
    x=ID e=LetFunTailExpr { FunExp(x, e) }

LetFunTailExpr :
    x=ID e=LetFunTailExpr { FunExp(x, e) }
  | EQ e=Expr { e }

FunHeadExpr :
    FUN p=ID e=FunTailExpr { FunExp (p, e) }

FunTailExpr :
    p=ID e=FunTailExpr { FunExp (p, e) }
  | RARROW e=Expr { e }

DFunHeadExpr :
    DFUN p=ID e=DFunTailExpr { DFunExp (p, e) }

DFunTailExpr :
    p=ID e=DFunTailExpr { DFunExp (p, e) }
  | RARROW e=Expr { e }

LetRecExpr :
    LET REC le=LetRecAndExpr { let (l, e) = le in LetRecExp (l, e) }

LetRecAndExpr :
    f=ID EQ fe=FunHeadExpr LETAND le=LetRecAndExpr { match fe with FunExp (p, e1) ->
                                                       let (l, e2) = le in ((f, p, e1) :: l, e2) } 
  | f=ID EQ fe=FunHeadExpr IN e2=Expr { match fe with FunExp (p, e1) -> ([(f, p, e1)], e2) }
  | f=ID fe=LetFunHeadExpr LETAND le=LetRecAndExpr { match fe with FunExp (p, e1) ->
                                                   let (l, e2) = le in ((f, p, e1) :: l, e2) } 
  | f=ID fe=LetFunHeadExpr IN e2=Expr { match fe with FunExp (p, e1) -> ([(f, p, e1)], e2) }

(*MatchExpr :
    MATCH e1=Expr WITH EMPTY RARROW e2=Expr BAR x1=ID CONS x2=ID RARROW e3=Expr { *)


