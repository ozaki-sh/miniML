%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT LT MT HAT EXPO
%token AND OR
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ METAAND
%token RARROW FUN DFUN
%token REC
%token MATCH WITH BAR
%token LBOXBRA RBOXBRA CONS SEMI
%token COMMA UNDERSCORE
%token COLON
%token INT BOOL STRING LIST
%token LCLYBRA RCLYBRA DOT
%token REF COLONEQ EXCLM
%token TYPE OF

%token <int> INTV
%token <Syntax.id> ID
%token <string> TYVAR
%token <string> STRINGV
%token <string> CNSTR

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | d=LetDecl SEMISEMI { Decls d }
  | d=LetRecDecl SEMISEMI { RecDecls d }
  | d=TypeDecl SEMISEMI { TypeDecls d }

LetDecl :
    LET d1=LetAndDecl d2=LetDecl { d1 :: d2 }
  | LET d=LetAndDecl { [d] }

LetAndDecl :
    x=IDt EQ e=Expr METAAND d=LetAndDecl { (x, e) :: d }
  | x=IDt EQ e=Expr { [(x, e)] }
  | f=ID fe=LetFunExpr METAAND d=LetAndDecl { let (e, ty) = fe in ((f, ty), e) :: d }
  | f=ID fe=LetFunExpr { let (e, ty) = fe in [((f, ty), e)] }

LetRecDecl :
    LET REC d1=LetRecAndDecl d2=LetRecDecl { d1 :: d2 }
  | LET REC d=LetRecAndDecl { [d] }

LetRecAndDecl :
    f=IDt EQ e=FunExpr METAAND d=LetRecAndDecl { (f, e) :: d }
  | f=IDt EQ e=FunExpr { [(f, e)] }
  | f=ID fe=LetFunExpr METAAND d=LetRecAndDecl { let (e, ty) = fe in ((f, ty), e) :: d }
  | f=ID fe=LetFunExpr { let (e, ty) = fe in [((f, ty), e)] }

TypeDecl :
    TYPE d1=TypeAndDecl d2=TypeDecl { d1 :: d2 }
  | TYPE d=TypeAndDecl { [d] }

TypeAndDecl :
    tvs=option(Parameters) x=ID EQ t=Type METAAND d=TypeAndDecl { match tvs with None -> (x, [], t) :: d | Some tvs' -> (x, tvs', t) :: d }
  | tvs=option(Parameters) x=ID EQ t=Type { match tvs with None -> [(x, [], t)] | Some tvs' -> [(x, tvs', t)] }


Expr :
    e=IfExpr { e }
  | e=OrExpr { e }
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=DFunExpr { e }
  | e=LetRecExpr { e }
  | e=MatchExpr { e }
  | e=TupleHeadExpr { (TupleExp e, []) }

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
  | e=CnstrExpr { e }

CnstrExpr :
    c=CNSTR { (Constr (c, None), []) }
  | c=CNSTR e=CnstrExpr { (Constr (c, Some e), []) }
  | e=ProjExpr { e }

ProjExpr :
    e=ProjExpr DOT x=ID { (MatchExp (e, [((RecordPattern (ConsR ((x, (Var "_a", [])), EmpR)), []), (Var "_a", []))]), []) }
  | e=AExpr { e }

AExpr :
    i=INTV { (ILit i, []) }
  | TRUE   { (BLit true, []) }
  | FALSE  { (BLit false, []) }
  | s=STRINGV { (SLit s, []) }
  | i=ID   { (Var i, []) }
  | LBOXBRA RBOXBRA  { (ListExp Emp, []) }
  | e=ListHeadExpr { (ListExp e, []) }
  | e=RecordHeadExpr { (Record e, []) }
  | e=RecordWithHeadExpr { let (old, l) = e in (RecordWith (old, l), []) }
  | LPAREN e=Expr RPAREN { e }
  | LPAREN e=Expr COLON ty=TupleType RPAREN { let (e', l) = e in (e', ty :: l) }

ListHeadExpr :
    LBOXBRA e=Expr lst=ListTailExpr { Cons (e, lst) }

ListTailExpr :
    SEMI e=Expr lst=ListTailExpr { Cons (e, lst) }
  | option(SEMI) RBOXBRA { Emp }

RecordHeadExpr :
    LCLYBRA e=RecordExpr lst=RecordTailExpr { ConsR (e, lst) }

RecordTailExpr :
    SEMI e=RecordExpr lst=RecordTailExpr { ConsR (e, lst) }
  | option(SEMI) RCLYBRA { EmpR }

RecordExpr :
    x=ID EQ e=Expr { (x, e) }

RecordWithHeadExpr :
    LCLYBRA old=ProjExpr WITH e=RecordExpr lst=RecordTailExpr { (old, ConsR (e, lst)) }


IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { (IfExp (c, t, e), []) }

LetExpr :
    LET le=LetAndExpr { let (l, e) = le in (LetExp (l, e), []) }

LetAndExpr :
    x=IDt EQ e1=Expr METAAND le=LetAndExpr { let (l, e2) = le in ((x, e1) :: l, e2) }
  | x=IDt EQ e1=Expr IN e2=Expr { ([(x, e1)], e2) }
  | f=ID et=LetFunExpr METAAND le=LetAndExpr { let (e1, ty) = et in let (l, e2) = le in (((f, ty), e1) :: l, e2) }
  | f=ID et=LetFunExpr IN e2=Expr { let (e1, ty) = et in ([((f, ty), e1)], e2) }

LetFunExpr :
    p=nonempty_list(IDt) ty=option(WithType) EQ e=Expr {
      let rec loop = function
          [para] ->
           (match ty with
              None -> FunExp (para, e)
            | Some ty' ->
               (match e with
                  (e', att_ty) -> FunExp (para, (e', ty' :: att_ty))))
        | head :: rest -> FunExp (head, (loop rest, []))
      in
        let exp = loop p in
        ((exp, []), []) }

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
    f=IDt EQ e1=FunExpr METAAND le=LetRecAndExpr { let (l, e2) = le in ((f, e1) :: l, e2) }
  | f=IDt EQ e1=FunExpr IN e2=Expr { ([(f, e1)], e2) }
  | f=ID fe=LetFunExpr METAAND le=LetRecAndExpr { let (e1, ty) = fe in let (l, e2) = le in (((f, ty), e1) :: l, e2) }
  | f=ID fe=LetFunExpr IN e2=Expr { let (e1, ty) = fe in ([((f, ty), e1)], e2) }

MatchExpr :
    MATCH e1=Expr WITH option(BAR) e2=PatternMatchExpr { (MatchExp (e1 , e2), []) }

TupleTailExpr :
    COMMA e=Expr { ConsT (e, EmpT) }
  | COMMA e=Expr lst=TupleTailExpr { ConsT (e, lst) }

TupleHeadExpr :
    e=Expr lst=TupleTailExpr { ConsT (e, lst) }

Pattern :
    pt=TuplePattern { pt }

TuplePattern :
    pt=TupleHeadPattern { (TupleExp pt, []) }
  | pt=ConsPattern { pt }

TupleTailPattern :
    COMMA pt=Pattern { ConsT (pt, EmpT) }
  | COMMA pt=Pattern lst=TupleTailPattern { ConsT (pt, lst) }

TupleHeadPattern :
    pt=Pattern lst=TupleTailPattern { ConsT (pt, lst) }

ConsPattern :
    ptl=CnstrPattern CONS ptr=ConsPattern { (BinOp (Cons, ptl, ptr), []) }
  | pt=CnstrPattern { pt }

CnstrPattern :
    c=CNSTR { (Constr (c, None), []) }
  | c=CNSTR pt=CnstrPattern { (Constr (c, Some pt), []) }
  | pt=APattern { pt }

APattern :
    i=INTV { (ILit i, []) }
  | TRUE { (BLit true, []) }
  | FALSE  { (BLit false, []) }
  | s=STRINGV { (SLit s, []) }
  | x=ID { (Var x, []) }
  | LBOXBRA RBOXBRA { (ListExp Emp, []) }
  | pt=ListHeadPattern { (ListExp pt, []) }
  | pt=RecordHeadPattern { (RecordPattern pt, []) }
  | UNDERSCORE { (Wildcard, []) }
  | LPAREN pt=Pattern RPAREN { pt }
  | LPAREN pt=Pattern COLON ty=TupleType RPAREN { let (pt', l) = pt in (pt', ty :: l) }

ListHeadPattern :
    LBOXBRA pt=Pattern lst=ListTailPattern { Cons (pt, lst) }

ListTailPattern :
    SEMI pt=Pattern lst=ListTailExpr { Cons (pt, lst) }
  | option(SEMI) RBOXBRA { Emp }

RecordHeadPattern :
    LCLYBRA pt=RecordPattern lst=RecordTailPattern { ConsR (pt, lst) }

RecordTailPattern :
    SEMI pt=RecordPattern lst=RecordTailPattern { ConsR (pt, lst) }
  | option(SEMI) RCLYBRA { EmpR }

RecordPattern :
    x=ID EQ pt=Pattern { (x, pt) }

PatternMatchExpr :
    pt=Pattern pts=list(MorePattern) RARROW e1=Expr e2=list(MorePatternMatchExpr) {
      let pattern_and_body_list = List.concat e2 in
      let rec link_pattern_with_body_andthen_cons = function
          [] -> (pt, e1) :: pattern_and_body_list
        | head :: rest -> (head, e1) :: link_pattern_with_body_andthen_cons rest
      in
        link_pattern_with_body_andthen_cons pts }

MorePatternMatchExpr :
    BAR pt=Pattern pts=list(MorePattern) RARROW e=Expr {
      let rec link_pattern_with_body = function
          [] -> [(pt, e)]
        | head :: rest -> (head, e) :: link_pattern_with_body rest
      in
        link_pattern_with_body pts }

MorePattern :
    BAR pt=Pattern { pt }

WithType :
    COLON ty=TupleType { ty }

IDt :
    x=ID { (x, []) }
  | LPAREN x=IDt COLON ty=TupleType RPAREN { let (x', l) = x in (x', ty :: l) }

Type :
    option(BAR) v=VariantType l=list(MoreVariantType) { v :: l }
  | l=RecordHeadType { l }

VariantType :
    c=CNSTR { (Constructor (c, TyNone c)) }
  | c=CNSTR OF a=Arg { Constructor (c, a) }

MoreVariantType :
    BAR v=VariantType { v }

Arg :
    t=TupleType { t }

RecordHeadType :
    LCLYBRA r=RecordType lst=RecordTailType { r :: lst }

RecordTailType :
    SEMI r=RecordType lst=RecordTailType { r :: lst }
  | option(SEMI) RCLYBRA { [] }

RecordType :
    x=ID COLON ty=TupleType { Field (x, ty) }

Parameters :
    tv=TYVAR { [tv] }
  | LPAREN tvs=ListedParameters RPAREN { tvs }

ListedParameters :
    tv=TYVAR { [tv] }
  | tv=TYVAR COMMA tvs=ListedParameters { tv :: tvs }

TypeParameters :
    ty=TupleType { [ty] }
  | LPAREN tys=ListedTypeParameters RPAREN { tys }

ListedTypeParameters :
    ty=TupleType { [ty] }
  | ty=TupleType COMMA tys=ListedTypeParameters { ty :: tys }

TupleTailType :
    MULT ty=TupleType { TyConsT (ty, TyEmpT) }
  | MULT ty1=TupleType ty2=TupleTailType { TyConsT (ty1, ty2) }

TupleHeadType :
    ty1=TupleType ty2=TupleTailType { TyConsT (ty1, ty2) }

TupleType :
    ty=TupleHeadType { TyTuple ty }
  | ty=FunType { ty }

FunType :
    ty1=AType RARROW ty2=FunType { TyFun (ty1, ty2) }
  | ty=AType { ty }

AType :
    INT { TyInt }
  | BOOL { TyBool }
  | STRING { TyString }
  | tv=TYVAR { TyStringVar tv }
  | ty=AType LIST { TyList ty }
  | x=ID { TyUser (x, []) }
  | tys=TypeParameters x=ID { TyUser (x, tys) }
  | LPAREN ty=TupleType RPAREN { ty }





