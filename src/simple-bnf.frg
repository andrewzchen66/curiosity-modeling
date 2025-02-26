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
// abstract sig NonTerminal extends S_Expr {}
// abstract sig Terminal extends S_Expr {}

// numbers
sig Number extends S_Expr {
  n: one Int
}

// // symbols (+, -)
// sig Operator {}
// sig Plus extends Operator {}
// sig Minus extends Operator {}

// sig Symbol extends S_Expr { 
//   s: one Operator
// }

// parenthetical expression
sig LPAREN {}
sig RPAREN {}

abstract sig List {}
sig EmptyList extends List {}
sig SomeList extends List {
  first: one S_Expr,
  rest: one List
}

sig Paren_Expr extends S_Expr {
  lparen: one LPAREN,
  list: one List,
  rparen: one RPAREN
}

// program
sig Program {
  expr: one S_Expr
}

// wellformed
pred wellformed {
  // no dangling S_Expr, Lists, parens
  all program: Program {
    all s_expr: S_Expr {
      s_expr = program.expr or reachable[s_expr, program.expr, list, first, rest]
    }
    all lst: List {
      reachable[lst, program.expr, list, first, rest]
    }
    all lp: LPAREN {
      reachable[lp, program.expr, list, first, rest, lparen]
    }
    all rp: RPAREN {
      reachable[rp, program.expr, list, first, rest, rparen]
    }

    // // no dangling operator
    // all op: Operator {
    //   some sym: Symbol {
    //     sym.s = op
    //   }
    // }
  }

  all disj lst1, lst2: List {
    // no cycles between lists
    reachable[lst1, lst2, list, first, rest] => not reachable[lst2, lst1, list, first, rest]

    // no DAGs
    // all s_expr: S_Expr {
    //   reachable[s_expr, lst1, list, first, rest] => reachable[s_expr, lst2, list, first, rest]
    // }
  }

  // no self looping lists
  all lst: List {
    lst.rest != lst
  }

  // FIXME: replace w generalized cycle Logic?
  // lists cannot contain parent s_exprs
  all s_expr: S_Expr, lst: List {
    s_expr.list = lst => lst.first != s_expr
  }

  // FIXME: replace w generalized DAG Logic?
  // no 2 paren_expr can share same list instance
  all disj paren_expr1, paren_expr2: Paren_Expr, lst: List {
    paren_expr1.list = lst => paren_expr2.list != lst
  }
  all disj lst1, lst2: List, s_expr: S_Expr {
    lst1.first = s_expr => lst2.first != s_expr
  }

  // ===
  // no cycles S_Expr
  // all disj s_expr1, s_expr2: S_Expr {
  //   reachable[s_expr1, s_expr2, list, first, rest] => not reachable[s_expr2, s_expr1, list, first, rest]
  // }

  // no dangling parens //  or list
  // all lp: LPAREN, rp: RPAREN, lst: List {
  //   some paren_expr: Paren_Expr {
  //     paren_expr.lparen = lp
  //     paren_expr.rparen = rp
  //     paren_expr.list = lst
  //   }
  // }

  // no cycles S_Expr
  // all disj s_expr1, s_expr2: S_Expr {
  //   reachable[s_expr1, s_expr2, list, first, rest] => not reachable[s_expr2, s_expr1, list, first, rest]
  // }

  // // no cycles between S_Expr and List
  // all s_expr: S_Expr, lst: List {
  //   reachable[lst, s_expr.list, rest] => lst.first != s_expr
  //   s_expr.list = lst => lst.first != s_expr
  // }

  // // no 2 paren_expr can share same list instance
  // all paren_expr1, paren_expr2: Paren_Expr, lst: List {
  //   paren_expr1.list = lst => paren_expr2.list != lst
  // }

  // // no cycles in List
  // all disj list1, list2: SomeList {
  //   reachable[list1, list2, rest] => not reachable[list2, list1, rest]
  //   list1.rest != list1
  //   list2.rest != list2
  // }
}

run {
  wellformed
} for exactly 1 Program, exactly 2 SomeList, 2 Paren_Expr

// ====== OLD STUFF ========= // 
// abstract sig S_Expr {}

// abstract sig Operator {}
// sig Plus extends Operator {}
// sig Minus extends Operator {}

// sig Num extends S_Expr {
//   n: one Int
// }

// sig Sym extends S_Expr {
//   s: one Operator
// }

// abstract sig Lst {}
// sig EmptyLst extends Lst {}
// sig SomeList extends Lst {
//   first: one S_Expr,
//   rest: one Lst
// }

// sig LPAREN {}
// sig RPAREN {}

// sig Paren_Expr extends S_Expr {
//   lparen: one LPAREN,
//   lst: one Lst,
//   rparen: one RPAREN
// }

// sig Program {
//   // defns: set Defn, // id -> defn w/ that id 
//   expr: one S_Expr
// }

// pred wellformed {
//   all p: Program | {
//     // FIXME: implement! mostly:
//     // 1. need to make sure no dangling SExprs, Operators, etc
//     // 2. no cycles in the program AST
//     all s_expr: S_Expr | {
//       reachable[s_expr, p.expr, first, rest, lst]
//     }
//   }
// }

// run {
//   wellformed
// } for exactly 1 Program