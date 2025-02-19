#lang forge/froglet

// FIRST, we model this at the most basic level:
// <s_exp> ::=
// | NUM (n)
// | SYM (s)
// | LPAREN <lst> RPAREN

// <lst> ::=
// | ε
// | <s_exp> <lst>

abstract sig S_Expr {}

abstract sig Operator {}
sig Plus extends Operator {}
sig Minus extends Operator {}

sig Num extends S_Expr {
  n: one Int
}

sig Sym extends S_Expr {
  s: one Operator
}

abstract sig Lst {}
sig EmptyLst extends Lst {}
sig SomeList extends Lst {
  first: one S_Expr,
  rest: one Lst
}

sig LPAREN {}
sig RPAREN {}

sig Paren_Expr extends S_Expr {
  lparen: one LPAREN,
  lst: one Lst,
  rparen: one RPAREN
}

sig Program {
  // defns: set Defn, // id -> defn w/ that id 
  expr: one S_Expr
}

pred wellformed {
  some p: Program | {
    
  }
}

run {
  wellformed
}