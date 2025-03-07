#lang forge/froglet

// RESERVED KEYWORDS, SYMBOLS
sig LPAREN {}
sig RPAREN {}
sig SEMICOLON {}
sig COMMA {}
sig PLUS {}
sig MINUS {}

sig IF {}
sig THEN {}
sig ELSE {}

sig ID {}
sig LET {}
sig EQ {}
sig FUNCTION {}

// EVERYTHING IS AN EXP - this is just a "node" in the S-Exp/AST tree
abstract sig Exp {}

// <expr> ::=
//   | IF <expr> THEN <expr> ELSE <expr>
//   | LET ID EQ <expr> IN <expr>
//   | <seq>
abstract sig BaseExp extends Exp {}
sig IfExp extends BaseExp {
  // __if__: one IF,
  // __then__: one THEN,
  // __else__: one ELSE,
  if_expr: one BaseExp,
  then_expr: one BaseExp,
  else_expr: one BaseExp
}
sig LetExp extends BaseExp {
  // __let__: one LET,
  // __id__: one ID,
  // __eq__: one EQ,
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
// sig SeqList extends Exp {
//   __semicolon__: one SEMICOLON,
//   infix1: one Infix1,
//   rest_seq: lone SeqList
// }

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
  infix1_: lone Infix1_ 
}
abstract sig Infix1_ extends Exp {}
sig EqInfix1_ extends Infix1_ {
  // eq: one EQ,
  eq_infix1: one Infix1
}

sig Infix2 extends Exp {
  term: one Term,
  infix2_: lone Infix2_
}
abstract sig Infix2_ extends Exp {}
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
sig NumberTerm extends Term {
  n: one Int
}
// sig SymbolTerm extends Term {
//   // s: one String
// }
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
// sig Args extends Exp {
//   rparen: one RPAREN,
//   args_expr: one BaseExp,
//   rest_args: one RestArgs
// }
// sig RestArgs extends Exp {
//   rparen: one RPAREN,
//   comma: one COMMA,
//   rest_args_expr: one BaseExp,
//   rest_args: one RestArgs
// }

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

// ______________________________________________________________________
// PREDS

// Helper that checks every Exp field for whether expr2 is reachable from expr1
pred expReachable[expr1, expr2: Exp] {
  reachable[
    expr1,
    expr2,
    // defn_expr,
    if_expr,
    then_expr,
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

// Program shouldn't have dangling Exp
// All Exp should be reachable from root (Program)
pred noDangling {
  all program: Program {
    all expr: Exp | program.program_expr != expr => {
      expReachable[expr, program.program_expr]
    }
  }
}

// Exps shouldn't have cycles
// if expr2 is reachable from expr1, then expr1 shouldn't be reachable from expr2
pred noExpCycles {
  all disj expr1, expr2: Exp {
    expReachable[expr1, expr2] => not expReachable[expr2, expr1]
  }
}

// no DAGs in Program 
// For every Exp, there should only be one parent that points to it
pred noExpDAGs {
  all expr: Exp {
    add[
      #{e: Exp | e.if_expr = expr},
      #{e: Exp | e.then_expr = expr},
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

// Defines valid if exp
// if_expr, then_expr, else_expr should be distinct, and not point to the current expr
pred validIfExp {
  all expr: IfExp {
    expr.if_expr != expr
    expr.then_expr != expr
    expr.else_expr != expr
    expr.if_expr != expr.then_expr
    expr.if_expr != expr.else_expr
  }
}

// Defines valid let exp
// bind_expr and body_expr should be distinct, and not point to the current expr
pred validLetExp {
  all expr: LetExp {
    expr.bind_expr != expr
    expr.body_expr != expr
    expr.bind_expr != expr.body_expr
  }
}

run {
  noDangling
  noExpCycles
  noExpDAGs
  validIfExp
  validLetExp
} for exactly 1 Program, 16 Exp //, exactly 1 LetExp, exactly 1 IfExp