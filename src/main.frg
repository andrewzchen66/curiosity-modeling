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
  symbol: one Operator
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
    // FIXME: implement! mostly:
    // 1. need to make sure no dangling SExprs, Operators, etc
    // 2. no cycles in the program AST
    
    // No dangles
    all s_expr: S_Expr, op: Operator, l_paren: LPAREN, r_paren: RPAREN | {
      reachable[s_expr, p.expr, first, rest, lst] // no dangling s_expr
      reachable[op, p.expr, symbol] // no dangling operators
      reachable[l_paren, p.expr, lparen] // no dangling l_paren
      reachable[r_paren, p.expr, rparen] // no dangling r_paren
    }

    all s_expr1, s_expr2: S_Expr | {
      reachable[s_expr1, s_expr2, first, rest, lst] implies not reachable[s_expr2, s_expr1, first, rest, lst]
    }


    // 
    all lst: SomeList | {
      lst.rest != lst
    }
    
    // all op: Operator | {
    //   reachable[op, p.expr, first, rest, lst]
    // }
  }
}

run {
  wellformed
} for exactly 1 Program, 3 S_Expr