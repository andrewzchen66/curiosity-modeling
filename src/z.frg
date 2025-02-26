#lang forge/froglet

// RESERVED KEYWORDS, SYMBOLS
sig FUNCTION {}
sig LPAREN {}
sig RPAREN {}
sig COMMA {}
sig EQ {}
sig IF {}
sig THEN {}
sig ELSE {}
sig LET {}
sig PLUS {}
sig MINUS {}

// EVERYTHING IS AN EXP
abstract sig Exp {}

// <expr> ::=
//   | IF <expr> THEN <expr> ELSE <expr>
//   | LET ID EQ <expr> IN <expr>
//   | <seq>
abstract sig BaseExp extends Exp {}
sig IfExp extends BaseExp {
  // if: one IF,
  // then: one THEN,
  if_expr: one BaseExp,
  // els: one ELSE,
  else_expr: one BaseExp
}
sig LetExp extends BaseExp {
  // lt:
  // id: 
  // eq: one EQ,
  bind_expr: one BaseExp,
  body_expr: one BaseExp
}
sig SeqExp extends BaseExp {
  infix1: one Infix1
  // seq_list: one SeqList
}
// <seq> ::=
//   | <infix1> <rest-seq>
// <rest-seq> ::=
//   | epsilon
//   | SEMICOLON <infix1> <rest-seq>
abstract sig SeqList extends Exp {}
sig EmptySeqList extends SeqList {}
sig SomeSeqList extends SeqList {}

// <infix1> ::=
//   | <infix2> <infix1'>
// <infix1'> ::=
//   | epsilon
//   | EQ <infix1>
//   | LT <infix1>
// <infix2> ::=
//   | <term> <infix2'>
// <infix2'> ::=
//   | epsilon
//   | PLUS <infix2>
//   | MINUS <infix2>
sig Infix1 extends Exp {
  infix2: one Infix2,
  infix1_: one Infix1_ 
}
abstract sig Infix1_ extends Exp {}
sig EmptyInfix1_ extends Infix1_ {}
sig EqInfix1_ extends Infix1_ {
  // eq: one EQ,
  eq_infix1: one Infix1
}

sig Infix2 extends Exp {
  term: one Term,
  infix2_: one Infix2_
}
abstract sig Infix2_ extends Exp {}
sig EmptyInfix2_ extends Infix2_ {}
sig PlusInfix2_ extends Infix2_ {
  plus: one PLUS,
  plus_infix2: one Infix2
}
// sig MinusInfix2_ extends Infix2_ {
//   minus: one MINUS,
//   minus_infix2: one infix2
// }

// <term> ::=
//   | ID
//   | ID LPAREN <args>
//   | NUM
//   | LPAREN <expr> RPAREN
abstract sig Term extends Exp {}
// sig SymbolTerm extends Term {
//   // s: one String
// }
sig NumberTerm extends Term {
  n: one Int
}
// sig FunctionCallTerm extends Term {
// }
// sig ParenTerm extends Term {
// }

// <args> ::=
//   | RPAREN
//   | <expr> <rest-args>
// <rest-args> ::=
//   | RPAREN
//   | COMMA <expr> <rest-args>


// <program> ::= <defns> <expr>
sig Program {
  // program_defns: one DefnList,
  program_expr: one BaseExp
}

// <defns> ::=
//   | epsilon
//   | <defn> <defns>
// <defn> ::=
//   | FUNCTION ID LPAREN <params> EQ <expr>
// <params> ::=
//   | RPAREN
//   | ID <rest-params>
// <rest-params> ::=
//   | RPAREN
//   | COMMA ID <rest-params>
// abstract sig DefnList {}
// sig EmptyDefnList extends DefnList {}
// sig SomeDefnList extends DefnList {
//   first: one Defn,
//   rest: one DefnList
// }
// sig DefnId {}
// sig Defn {
//   defn_function: one FUNCTION,
//   defn_id: one DefnId,
//   defn_lparen: one LPAREN,
//   // params: _,
//   defn_eq: one EQ,
//   defn_expr: one Exp
// }

// PREDS
pred expReachable[expr1, expr2: Exp] {
  reachable[
    expr1,
    expr2,
    // defn_expr,
    if_expr,
    else_expr,
    bind_expr,
    body_expr,
    infix1,
    infix1_,
    infix2,
    infix2_,
    eq_infix1,
    plus_infix2,
    // seq_list,
    term
  ]
}

pred noDangling[program: Program] {
  all expr: Exp | program.program_expr != expr => {
    expReachable[expr, program.program_expr]
  }
}

pred noExpCycles {
  all disj expr1, expr2: Exp {
    expReachable[expr1, expr2] => not expReachable[expr2, expr1]
  }
}

pred noExpDAGs {
  all expr: Exp {
    add[
      #{e: Exp | e.if_expr = expr},
      #{e: Exp | e.else_expr = expr},
      #{e: Exp | e.bind_expr = expr},
      #{e: Exp | e.body_expr = expr},
      #{e: Exp | e.infix1 = expr},
      #{e: Exp | e.infix1_ = expr},
      #{e: Exp | e.infix2 = expr},
      #{e: Exp | e.infix2_ = expr},
      #{e: Exp | e.eq_infix1 = expr},
      #{e: Exp | e.plus_infix2 = expr},
      #{e: Exp | e.term = expr}
    ] <= 1
  }
}

run {
  all program: Program {
    noDangling[program]
  }

  noExpCycles
  noExpDAGs

  all expr: IfExp {
    expr.if_expr != expr
    expr.else_expr != expr
    expr.if_expr != expr.else_expr
  }

  all expr: LetExp {
    expr.bind_expr != expr
    expr.body_expr != expr
    expr.bind_expr != expr.body_expr
  }
} for exactly 1 Program, 10 Exp