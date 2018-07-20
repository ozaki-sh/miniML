%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT LT MT HAT EXPO
%token AND OR
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ LETAND
%token RARROW FUN DFUN
%token REC
%token MATCH WITH BAR
%token LSTLPRN LSTRPRN CONS SEMI
%token COMMA UNDERSCORE
%token COLON
%token INT BOOL STRING LIST

%token <int> INTV
%token <Syntax.id> ID
%token <string> TYVAR
%token <string> STRINGV

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | d=LetDecl SEMISEMI { Decls d }
  | d=LetRecDecl SEMISEMI { RecDecls d }

LetDecl :
    LET d1=LetAndDecl d2=LetDecl { d1 :: d2 }
  | LET d=LetAndDecl { [d] }

LetAndDecl :
    x=IDt EQ e=Expr LETAND d=LetAndDecl { (x, e) :: d }
  | x=IDt EQ e=Expr { [(x, e)] }
  | f=ID fe=LetFunExpr LETAND d=LetAndDecl { let (e, ty) = fe in ((f, ty), e) :: d }
  | f=ID fe=LetFunExpr { let (e, ty) = fe in [((f, ty), e)] }

LetRecDecl :
    LET REC d1=LetRecAndDecl d2=LetRecDecl { d1 :: d2 }
  | LET REC d=LetRecAndDecl { [d] }

LetRecAndDecl :
    f=IDt EQ e=FunExpr LETAND d=LetRecAndDecl { (f, e) :: d }
  | f=IDt EQ e=FunExpr { [(f, e)] }
  | f=ID fe=LetFunExpr LETAND d=LetRecAndDecl { let (e, ty) = fe in ((f, ty), e) :: d }
  | f=ID fe=LetFunExpr { let (e, ty) = fe in [((f, ty), e)] }
    

Expr :
    e=IfExpr { e }
  | e=OrExpr { e }
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=DFunExpr { e }
  | e=LetRecExpr { e }
  | e=MatchExpr { e }

LookRightExpr :
    e=IfExpr { e }
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=DFunExpr { e }
  | e=LetRecExpr { e }
  | e=MatchExpr { e }

OrExpr :
    l=OrExpr OR r=AndExpr { (BinLogicOp(Or, l, r), []) }
  | l=OrExpr OR r=LookRightExpr { (BinLogicOp(Or, l, r), []) }
  | e=AndExpr { e }

AndExpr :
    l=AndExpr AND r=CmpExpr { (BinLogicOp(And, l, r), []) }
  | l=AndExpr AND r=LookRightExpr { (BinLogicOp(And, l, r), []) }
  | e=CmpExpr { e }

CmpExpr : 
    l=PMExpr LT r=PMExpr { (BinOp (Lt, l, r), []) }
  | l=PMExpr LT r=LookRightExpr { (BinOp (Lt, l, r), []) }
  | l=PMExpr MT r=PMExpr { (BinOp (Mt, l, r), []) }
  | l=PMExpr MT r=LookRightExpr { (BinOp (Mt, l, r), []) }
  | l=CmpExpr EQ r=PMExpr { (BinOp (Eq, l, r), []) }
  | l=CmpExpr EQ r=LookRightExpr { (BinOp (Eq, l, r), []) }
  | e=ConsExpr { e }

ConsExpr :
    l=HExpr CONS r=ConsExpr { (BinOp (Cons, l, r), []) }
  | l=HExpr CONS r=LookRightExpr { (BinOp (Cons, l, r), []) }
  | e=HExpr { e }

HExpr :
    l=HExpr HAT r=PMExpr { (BinOp (Hat, l, r), []) }
  | e=PMExpr { e }

PMExpr :
    l=PMExpr PLUS r=MExpr { (BinOp (Plus, l, r), []) }
  | l=PMExpr PLUS r=LookRightExpr { (BinOp (Plus, l, r), []) }
  | l=PMExpr MINUS r=MExpr { (BinOp (Minus, l, r), []) }
  | l=PMExpr MINUS r=LookRightExpr { (BinOp (Minus, l, r), []) }
  | e=MExpr { e }

MExpr : 
    l=MExpr MULT r=EExpr { (BinOp (Mult, l, r), []) }
  | l=MExpr MULT r=LookRightExpr { (BinOp (Mult, l, r), []) }
  | e=EExpr { e }

EExpr :
    l=AppExpr EXPO r=EExpr { (BinOp (Expo, l, r), []) }
  | l=AppExpr EXPO r=LookRightExpr { (BinOp (Expo, l, r), []) }
  | e=AppExpr { e }

AppExpr :
    l=AppExpr r=FunInfixExpr { (AppExp (l, r), []) }
  | e=FunInfixExpr { e }

FunInfixExpr :
    LPAREN PLUS RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinOp (Plus, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN MINUS RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinOp (Minus, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN MULT RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinOp (Mult, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN LT RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinOp (Lt, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN EQ RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinOp (Eq, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN AND RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinLogicOp (And, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN OR RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinLogicOp (Or, (Var "x", []), (Var "y", []))), [])), [])), []) }
  | LPAREN HAT RPAREN { (FunExp (("x", []), (FunExp (("y", []), ((BinOp (Hat, (Var "x", []), (Var "y", []))), [])), [])), []) } 
  | e=AExpr { e }

AExpr :
    i=INTV { (ILit i, []) }
  | TRUE   { (BLit true, []) }
  | FALSE  { (BLit false, []) }
  | s=STRINGV { (SLit s, []) }
  | i=ID   { (Var i, []) }
  | LSTLPRN LSTRPRN  { (ListExp Emp, []) }
  | e=ListHeadExpr { (ListExp e, []) } 
  | LPAREN e=Expr RPAREN { e }
  | LPAREN e=Expr COLON ty=FunType RPAREN { let (e', l) = e in (e', ty :: l) }

ListHeadExpr :
    LSTLPRN e=Expr lst=ListTailExpr { Cons (e, lst) }

ListTailExpr :
    SEMI e=Expr lst=ListTailExpr { Cons (e, lst) }
  | LSTRPRN { Emp }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { (IfExp (c, t, e), []) } 

LetExpr :
    LET le=LetAndExpr { let (l, e) = le in (LetExp (l, e), []) }
    
LetAndExpr :
    x=IDt EQ e1=Expr LETAND le=LetAndExpr { let (l, e2) = le in ((x, e1) :: l, e2) } 
  | x=IDt EQ e1=Expr IN e2=Expr { ([(x, e1)], e2) }
  | f=ID et=LetFunExpr LETAND le=LetAndExpr { let (e1, ty) = et in let (l, e2) = le in (((f, ty), e1) :: l, e2) } 
  | f=ID et=LetFunExpr IN e2=Expr { let (e1, ty) = et in ([((f, ty), e1)], e2) }

LetFunExpr :
    p=nonempty_list(IDt) ty=option(WithType) EQ e=Expr {
      let rec loop = function
          [para] -> FunExp (para, e)
        | head :: rest -> FunExp (head, (loop rest, []))
      in
        let exp = loop p in
        match ty with
          None -> ((exp, []), [])
        | Some ty' -> ((exp, []), [ty']) }

FunExpr :
    FUN p=nonempty_list(IDt) RARROW e=Expr {
      let rec loop = function
          [para] -> FunExp (para, e)
        | head :: rest -> FunExp (head, (loop rest, []))
      in
        (loop p, []) }

DFunExpr :
    DFUN p=nonempty_list(IDt) RARROW e=Expr {
      let rec loop = function
          [para] -> DFunExp (para, e)
        | head :: rest -> DFunExp (head, (loop rest, []))
      in
        (loop p, []) }

LetRecExpr :
    LET REC le=LetRecAndExpr { let (l, e) = le in (LetRecExp (l, e), []) }

LetRecAndExpr :
    f=IDt EQ e1=FunExpr LETAND le=LetRecAndExpr { let (l, e2) = le in ((f, e1) :: l, e2) } 
  | f=IDt EQ e1=FunExpr IN e2=Expr { ([(f, e1)], e2) }
  | f=ID fe=LetFunExpr LETAND le=LetRecAndExpr { let (e1, ty) = fe in let (l, e2) = le in (((f, ty), e1) :: l, e2) } 
  | f=ID fe=LetFunExpr IN e2=Expr { let (e1, ty) = fe in ([((f, ty), e1)], e2) }

MatchExpr :
    MATCH e1=Expr e2=list(MoreExpr) WITH option(BAR) e3=PatternMatchExpr { (MatchExp (e1 :: e2, e3), []) }
 
MoreExpr :
    COMMA e=Expr { e }

Pattern :
    LSTLPRN pt=Pattern LSTRPRN { (ListExp (Cons (pt, Emp)), []) }
  | pt1=Pattern CONS pt2=Pattern { (ListExp (Cons (pt1, Cons (pt2, Emp))), []) }
  | pt=APattern { pt }

APattern :
    i=INTV { (ILit i, []) }
  | TRUE { (BLit true, []) }
  | FALSE  { (BLit false, []) }
  | s=STRINGV { (SLit s, []) }
  | x=ID { (Var x, []) }
  | LSTLPRN LSTRPRN { (ListExp Emp, []) }
  | UNDERSCORE { (Wildcard, []) }
  | LPAREN pt=Pattern RPAREN { pt }
  | LPAREN pt=Pattern COLON ty=FunType RPAREN { let (pt', l) = pt in (pt', ty :: l) }

PatternMatchExpr :
    pt=Patterns pts=list(MorePatterns) RARROW e1=Expr e2=list(MorePatternMatchExpr) { 
      let pattern_and_body_list = List.concat e2 in
      let rec link_pattern_with_body_andthen_cons = function
          [] -> (pt, e1) :: pattern_and_body_list
        | head :: rest -> (head, e1) :: link_pattern_with_body_andthen_cons rest
      in
        link_pattern_with_body_andthen_cons pts }

MorePatternMatchExpr :
    BAR pt=Patterns pts=list(MorePatterns) RARROW e=Expr { 
      let rec link_pattern_with_body = function
          [] -> [(pt, e)]
        | head :: rest -> (head, e) :: link_pattern_with_body rest
      in
        link_pattern_with_body pts }

Patterns :
    pt=Pattern pts=list(MorePattern) { pt :: pts }

MorePattern :
    COMMA pt=Pattern { pt }

MorePatterns :
    BAR pt=Patterns { pt }

FunType :
    ty1=AType RARROW ty2=FunType { Tyfun (ty1, ty2) }
  | ty=AType { ty }

AType :
    INT { Tyint }
  | BOOL { Tybool }
  | STRING { Tystring }
  | tv=TYVAR { Tyvar tv }
  | ty=AType LIST { Tylist ty }
  | LPAREN ty=FunType RPAREN { ty }

WithType :
    COLON ty=FunType { Ranty ty }

IDt :
    x=ID { (x, []) }
  | LPAREN x=IDt COLON ty=FunType RPAREN { let (x', l) = x in (x', ty :: l) }  




